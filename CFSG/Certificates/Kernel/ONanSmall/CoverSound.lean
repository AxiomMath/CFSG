module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import Mathlib.Algebra.Group.Basic
public import Batteries.Data.List.Lemmas
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push

public section

namespace CFSG.Certificates.Kernel.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

theorem isCovered_mono {L R R' : List M} (h : ∀ r ∈ R, r ∈ R') {t : M}
    (ht : isCovered L R t = true) : isCovered L R' t = true := by
  unfold isCovered at *
  obtain ⟨g, hg, hr⟩ := List.any_eq_true.1 ht
  obtain ⟨r, hr, he⟩ := List.any_eq_true.1 hr
  exact List.any_eq_true.2 ⟨g, hg, List.any_eq_true.2 ⟨r, h r hr, he⟩⟩

theorem isCovered_self {L R : List M} (h1 : (1 : M) ∈ L) {t : M} (ht : t ∈ R) :
    isCovered L R t = true :=
  List.any_eq_true.2 ⟨1, h1, List.any_eq_true.2 ⟨t, ht, by simp⟩⟩

theorem pickReps_fold (L : List M) (h1 : (1 : M) ∈ L) :
    ∀ (xs R : List M), (∀ r ∈ R, r ∈ xs.foldl (fun reps t =>
        if decide (t * t = 1 ∧ t ≠ 1) && !isCovered L reps t then reps ++ [t] else reps) R) ∧
      ∀ t ∈ xs, t * t = 1 ∧ t ≠ 1 → isCovered L (xs.foldl (fun reps t =>
        if decide (t * t = 1 ∧ t ≠ 1) && !isCovered L reps t then reps ++ [t] else reps) R) t = true
  | [], R => ⟨fun r hr => hr, fun t ht => by simp at ht⟩
  | x :: xs, R => by
    obtain ⟨ih1, ih2⟩ := pickReps_fold L h1 xs (if decide (x * x = 1 ∧ x ≠ 1) &&
      !isCovered L R x then R ++ [x] else R)
    have hsub : ∀ r ∈ R, r ∈ (if decide (x * x = 1 ∧ x ≠ 1) && !isCovered L R x then R ++ [x]
        else R) := fun r hr => by split <;> simp [hr]
    refine ⟨fun r hr => ih1 r (hsub r hr), fun t ht hinv => ?_⟩
    rw [List.foldl_cons]
    rcases List.mem_cons.1 ht with rfl | ht
    · apply isCovered_mono ih1
      by_cases hc : isCovered L R t = true
      · exact isCovered_mono hsub hc
      · have : (decide (t * t = 1 ∧ t ≠ 1) && !isCovered L R t) = true := by simp [hinv, hc]
        rw [if_pos this]
        exact isCovered_self h1 (by simp)
    · exact ih2 t ht hinv

theorem coverB_pickReps {L : List M} (h1 : (1 : M) ∈ L) : coverB (pickReps L) L = true := by
  unfold coverB
  refine List.all_eq_true.2 fun t ht => ?_
  by_cases hinv : t * t = 1 ∧ t ≠ 1
  · rw [isCovered_eq_pick L h1 t ht hinv]
  · simp [hinv]
where
  isCovered_eq_pick (L : List M) (h1 : (1 : M) ∈ L) (t : M) (ht : t ∈ L)
      (hinv : t * t = 1 ∧ t ≠ 1) :
      (!decide (t * t = 1 ∧ t ≠ 1) || isCovered L (pickReps L) t) = true := by
    have := (pickReps_fold L h1 L []).2 t ht hinv
    unfold pickReps
    rw [this, Bool.or_true]

theorem verdictCheck_pickReps (B : ℕ) (LN L : List M) (e3b : Bool) (h1 : (1 : M) ∈ L) :
    verdictCheck B LN L e3b (pickReps L) =
      (pickReps L).all fun t => (let C := centB L t; noOddB3 B C && pairsV B LN L e3b t C) := by
  rw [verdictCheck, coverB_pickReps h1, Bool.true_and]

theorem mem_zip_map {α β : Type*} (f : α → β) {t : α} : ∀ {R : List α}, t ∈ R →
    (t, f t) ∈ R.zip (R.map f)
  | [], h => by simp at h
  | x :: R, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · rw [List.map_cons, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ (mem_zip_map f h)

theorem all_cent_of {L R : List M} {Cs : List (List M)} (P : M → List M → Bool)
    (hC : R.map (centB L) = Cs) (h : (R.zip Cs).all (fun p => P p.1 p.2) = true) :
    R.all (fun t => P t (centB L t)) = true := by
  subst hC
  rw [List.all_eq_true] at h ⊢
  intro t ht
  exact h (t, centB L t) (mem_zip_map (centB L) ht)

theorem mem_zip_map2 {α β γ : Type*} (f : α → β) (g : α → γ) {t : α} : ∀ {R : List α}, t ∈ R →
    ((t, f t), g t) ∈ (R.zip (R.map f)).zip (R.map g)
  | [], h => by simp at h
  | x :: R, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.zip_cons_cons]
      exact List.mem_cons_of_mem _ (mem_zip_map2 f g h)

theorem all_cent2_of {LP LA R : List M} {Cs Ds : List (List M)} (P : M → List M → List M → Bool)
    (hC : R.map (centB LP) = Cs) (hD : R.map (centB LA) = Ds)
    (h : ((R.zip Cs).zip Ds).all (fun p => P p.1.1 p.1.2 p.2) = true) :
    R.all (fun t => P t (centB LP t) (centB LA t)) = true := by
  subst hC hD
  rw [List.all_eq_true] at h ⊢
  intro t ht
  exact h ((t, centB LP t), centB LA t) (mem_zip_map2 (centB LP) (centB LA) ht)

end CFSG.Certificates.Kernel.ONanSmall
