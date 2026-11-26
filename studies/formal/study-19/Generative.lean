/- Research-only formal candidate, study 19.
   Free presentations, not a claim of foundation-independent construction.
   The fixed reference is represented by the initial mark; its actual
   relational structure and the correctness of a physical copy are not formalized.
   No built-in numerical carrier is used. -/
namespace NumbersTheory.Study19

inductive Snapshot where
  | unit : Snapshot
  | repeatMark : Snapshot → Snapshot

open Snapshot

inductive Sync : Snapshot → Snapshot → Prop where
  | initial : Sync unit unit
  | step {a b : Snapshot} : Sync a b → Sync (repeatMark a) (repeatMark b)

theorem sync_refl (a : Snapshot) : Sync a a := by
  induction a with
  | unit => exact Sync.initial
  | repeatMark a ih => exact Sync.step ih

theorem sync_symm {a b : Snapshot} (h : Sync a b) : Sync b a := by
  induction h with
  | initial => exact Sync.initial
  | step h ih => exact Sync.step ih

theorem sync_eq {a b : Snapshot} (h : Sync a b) : a = b := by
  induction h with
  | initial => rfl
  | step h ih => exact congrArg repeatMark ih

theorem sync_iff_eq (a b : Snapshot) : Sync a b ↔ a = b := by
  constructor
  · exact sync_eq
  · intro h
    cases h
    exact sync_refl a

theorem sync_trans {a b c : Snapshot} (h : Sync a b) (k : Sync b c) :
    Sync a c := by
  exact (sync_iff_eq a c).2 ((sync_eq h).trans (sync_eq k))

theorem sync_cancel {a b : Snapshot} :
    Sync (repeatMark a) (repeatMark b) ↔ Sync a b := by
  constructor
  · intro h
    cases h with
    | step h => exact h
  · exact Sync.step

theorem sync_unit_repeat_false (a : Snapshot) : ¬ Sync unit (repeatMark a) := by
  intro h
  cases h

theorem sync_repeat_unit_false (a : Snapshot) : ¬ Sync (repeatMark a) unit := by
  intro h
  cases h

/- History tags are arbitrary documentary annotations. They do not identify
   globally unique physical occurrences. -/
inductive History where
  | initial : Bool → History
  | completed : History → Bool → History

def erase : History → Snapshot
  | .initial _ => unit
  | .completed h _ => repeatMark (erase h)

inductive HistorySync : History → History → Prop where
  | initial (x y : Bool) : HistorySync (.initial x) (.initial y)
  | step {h k : History} (x y : Bool) :
      HistorySync h k → HistorySync (.completed h x) (.completed k y)

theorem history_sync_erase {h k : History} (p : HistorySync h k) :
    Sync (erase h) (erase k) := by
  induction p with
  | initial x y => exact Sync.initial
  | step x y p ih => exact Sync.step ih

theorem erase_history_sync (h k : History) :
    Sync (erase h) (erase k) → HistorySync h k := by
  induction h generalizing k with
  | initial x =>
    cases k with
    | initial y => intro _; exact HistorySync.initial x y
    | completed k y =>
      intro p
      exact False.elim (sync_unit_repeat_false (erase k) p)
  | completed h x ih =>
    cases k with
    | initial y =>
      intro p
      exact False.elim (sync_repeat_unit_false (erase h) p)
    | completed k y =>
      intro p
      exact HistorySync.step x y (ih k (sync_cancel.mp p))

theorem history_sync_iff (h k : History) :
    HistorySync h k ↔ Sync (erase h) (erase k) :=
  ⟨history_sync_erase, erase_history_sync h k⟩

theorem history_refl (h : History) : HistorySync h h :=
  (history_sync_iff h h).2 (sync_refl (erase h))

theorem history_symm {h k : History} (p : HistorySync h k) : HistorySync k h :=
  (history_sync_iff k h).2 (sync_symm (history_sync_erase p))

theorem history_trans {h k l : History} (p : HistorySync h k)
    (q : HistorySync k l) : HistorySync h l :=
  (history_sync_iff h l).2 (sync_trans (history_sync_erase p) (history_sync_erase q))

/- Strict reachability by a nonempty sequence of completed repetitions.
   The relation is on presentations. -/
inductive Earlier : Snapshot → Snapshot → Prop where
  | direct (a : Snapshot) : Earlier a (repeatMark a)
  | extend {a b : Snapshot} : Earlier a b → Earlier a (repeatMark b)

theorem earlier_trans {a b c : Snapshot} (p : Earlier a b) (q : Earlier b c) :
    Earlier a c := by
  induction q with
  | direct b => exact Earlier.extend p
  | extend q ih => exact Earlier.extend ih

theorem earlier_lift {a b : Snapshot} (h : Earlier a b) :
    Earlier (repeatMark a) (repeatMark b) := by
  induction h with
  | direct a => exact Earlier.direct (repeatMark a)
  | extend h ih => exact Earlier.extend ih

theorem earlier_unit (a : Snapshot) : Earlier unit (repeatMark a) := by
  induction a with
  | unit => exact Earlier.direct unit
  | repeatMark a ih => exact Earlier.extend ih

theorem not_earlier_unit (a : Snapshot) : ¬ Earlier a unit := by
  intro h
  cases h

theorem earlier_cancel (a b : Snapshot) :
    Earlier (repeatMark a) (repeatMark b) → Earlier a b := by
  induction b with
  | unit =>
    intro h
    cases h with
    | extend h => exact False.elim (not_earlier_unit (repeatMark a) h)
  | repeatMark b ih =>
    intro h
    cases h with
    | direct _ => exact Earlier.direct a
    | extend h => exact Earlier.extend (ih h)

theorem earlier_irrefl (a : Snapshot) : ¬ Earlier a a := by
  induction a with
  | unit => exact not_earlier_unit unit
  | repeatMark a ih =>
    intro h
    exact ih (earlier_cancel a a h)

theorem earlier_asymm {a b : Snapshot} (h : Earlier a b) : ¬ Earlier b a := by
  intro k
  exact earlier_irrefl a (earlier_trans h k)

theorem compare (a b : Snapshot) : Earlier a b ∨ Sync a b ∨ Earlier b a := by
  induction a generalizing b with
  | unit =>
    cases b with
    | unit => exact Or.inr (Or.inl Sync.initial)
    | repeatMark b => exact Or.inl (earlier_unit b)
  | repeatMark a ih =>
    cases b with
    | unit => exact Or.inr (Or.inr (earlier_unit a))
    | repeatMark b =>
      rcases ih b with h | h | h
      · exact Or.inl (earlier_lift h)
      · exact Or.inr (Or.inl (Sync.step h))
      · exact Or.inr (Or.inr (earlier_lift h))

theorem no_intermediate (a b : Snapshot) :
    Earlier a b → Earlier b (repeatMark a) → False := by
  intro h k
  cases k with
  | direct _ => exact earlier_irrefl a h
  | extend k => exact earlier_irrefl a (earlier_trans h k)

/- T75: uniqueness of the comparison criterion under explicit conditions. -/
theorem criterion_unique (Q : Snapshot → Snapshot → Prop)
    (base : Q unit unit)
    (left : ∀ b, ¬ Q unit (repeatMark b))
    (right : ∀ a, ¬ Q (repeatMark a) unit)
    (cancel : ∀ a b, Q (repeatMark a) (repeatMark b) ↔ Q a b)
    (a b : Snapshot) : Q a b ↔ Sync a b := by
  induction a generalizing b with
  | unit =>
    cases b with
    | unit => exact ⟨fun _ => Sync.initial, fun _ => base⟩
    | repeatMark b =>
      exact ⟨fun h => False.elim (left b h),
        fun h => False.elim (sync_unit_repeat_false b h)⟩
  | repeatMark a ih =>
    cases b with
    | unit =>
      exact ⟨fun h => False.elim (right a h),
        fun h => False.elim (sync_repeat_unit_false a h)⟩
    | repeatMark b =>
      exact (cancel a b).trans ((ih b).trans sync_cancel.symm)

/- T76: two explicitly different criteria, with their failure witnesses. -/
def collapseTag : Snapshot → Bool
  | unit => false
  | repeatMark _ => true

def Collapse (a b : Snapshot) : Prop := collapseTag a = collapseTag b

theorem collapse_base : Collapse unit unit := rfl

theorem collapse_left (b : Snapshot) : ¬ Collapse unit (repeatMark b) := by
  intro h
  change false = true at h
  cases h

theorem collapse_right (a : Snapshot) : ¬ Collapse (repeatMark a) unit := by
  intro h
  change true = false at h
  cases h

theorem collapse_preserves (a b : Snapshot) :
    Collapse a b → Collapse (repeatMark a) (repeatMark b) := by
  intro _
  rfl

theorem collapse_failure :
    Collapse (repeatMark unit) (repeatMark (repeatMark unit)) ∧
    ¬ Collapse unit (repeatMark unit) :=
  ⟨rfl, collapse_left unit⟩

def alternateTag : Snapshot → Bool
  | unit => false
  | repeatMark a => !alternateTag a

def Alternate (a b : Snapshot) : Prop := alternateTag a = alternateTag b

theorem alternate_base : Alternate unit unit := rfl

theorem alternate_cancel (a b : Snapshot) :
    Alternate (repeatMark a) (repeatMark b) ↔ Alternate a b := by
  unfold Alternate
  change (!alternateTag a) = (!alternateTag b) ↔ alternateTag a = alternateTag b
  cases alternateTag a <;> cases alternateTag b <;> decide

theorem alternate_adjacent (a : Snapshot) : ¬ Alternate a (repeatMark a) := by
  unfold Alternate
  change ¬ alternateTag a = (!alternateTag a)
  cases alternateTag a <;> decide

theorem alternate_failure : Alternate unit (repeatMark (repeatMark unit)) := rfl

/- T77: on snapshots, congruence under Sync follows from sync_eq.
   On histories it must be explicitly required for an arbitrary order. -/
theorem order_unique (Q : Snapshot → Snapshot → Prop)
    (irrefl : ∀ a, ¬ Q a a)
    (trans : ∀ {a b c}, Q a b → Q b c → Q a c)
    (growth : ∀ a, Q a (repeatMark a))
    (a b : Snapshot) : Q a b ↔ Earlier a b := by
  have forwardReach : ∀ {x y}, Earlier x y → Q x y := by
    intro x y h
    induction h with
    | direct x => exact growth x
    | extend h ih => exact trans ih (growth _)
  constructor
  · intro h
    rcases compare a b with p | p | p
    · exact p
    · have e := sync_eq p
      cases e
      exact False.elim (irrefl a h)
    · exact False.elim (irrefl a (trans h (forwardReach p)))
  · exact forwardReach

#print axioms history_refl
#print axioms history_symm
#print axioms history_trans
#print axioms history_sync_iff
#print axioms earlier_irrefl
#print axioms earlier_trans
#print axioms compare
#print axioms no_intermediate
#print axioms criterion_unique
#print axioms collapse_failure
#print axioms alternate_cancel
#print axioms alternate_adjacent
#print axioms alternate_failure
#print axioms order_unique

end NumbersTheory.Study19
