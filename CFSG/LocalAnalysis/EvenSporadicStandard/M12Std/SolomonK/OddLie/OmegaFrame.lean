module

public import CFSG.GH74.Filter.Orthogonal.OddReflections
import all CFSG.GH74.Filter.Orthogonal.OddReflections

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.ClassicalGroups.Orthogonal CFSG.GH74.Filter QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure EqFrame7 (Q : QuadraticForm K V) where
  v : Fin 7 → V
  ν : K
  ν_ne : ν ≠ 0
  Q_v : ∀ i, Q (v i) = ν
  orth : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0

variable {Q : QuadraticForm K V}

section Rotation

theorem map_comb {p q : V} (hp : Q p = 1) (hq : Q q = 1) (hpq : polar Q p q = 0) (a b : K) :
    Q (a • p + b • q) = a ^ 2 + b ^ 2 := by
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, hp, hq, hpq]
  ring

theorem _root_.CFSG.GH74.Filter.Frame7.polar_v (F : Frame7 Q) (i j : FrameIdx) :
    polar Q (F.v i) (F.v j) = if i = j then 2 * frameNorm K i else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, polar_self_eq_two_mul, F.Q_v]
  · rw [if_neg h, F.orth i j h]

theorem _root_.CFSG.GH74.Filter.Frame7.Q_inl (F : Frame7 Q) (i : Fin 3) :
    Q (F.v (.inl i)) = 1 := by
  rw [F.Q_v]
  simp [frameNorm]

theorem _root_.CFSG.GH74.Filter.Frame7.Q_w (F : Frame7 Q) : Q (F.v (.inr (.inl ()))) = 1 := by
  rw [F.Q_v]
  simp [frameNorm]

theorem _root_.CFSG.GH74.Filter.Frame7.Q_inr (F : Frame7 Q) (i : Fin 3) :
    Q (F.v (.inr (.inr i))) = -1 := by
  rw [F.Q_v]
  simp [frameNorm]

noncomputable def _root_.CFSG.GH74.Filter.Frame7.toEqFrame7 (F : Frame7 Q) {s t : K}
    (hst : s ^ 2 + t ^ 2 = -1) : EqFrame7 Q where
  v := ![s • F.v (.inl 0) + t • F.v (.inl 1), (-t) • F.v (.inl 0) + s • F.v (.inl 1),
    s • F.v (.inl 2) + t • F.v (.inr (.inl ())), (-t) • F.v (.inl 2) + s • F.v (.inr (.inl ())),
    F.v (.inr (.inr 0)), F.v (.inr (.inr 1)), F.v (.inr (.inr 2))]
  ν := -1
  ν_ne := neg_ne_zero.2 one_ne_zero
  Q_v := by
    intro i
    fin_cases i
    · simpa using (map_comb (F.Q_inl 0) (F.Q_inl 1) (F.orth _ _ (by decide)) s t).trans hst
    · simpa using (map_comb (F.Q_inl 0) (F.Q_inl 1) (F.orth _ _ (by decide)) (-t) s).trans
        (by linear_combination hst)
    · simpa using (map_comb (F.Q_inl 2) F.Q_w (F.orth _ _ (by decide)) s t).trans hst
    · simpa using (map_comb (F.Q_inl 2) F.Q_w (F.orth _ _ (by decide)) (-t) s).trans
        (by linear_combination hst)
    · simpa using F.Q_inr 0
    · simpa using F.Q_inr 1
    · simpa using F.Q_inr 2
  orth := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.cons_val, F.polar_v, frameNorm, polar_add_left, polar_add_right,
        polar_smul_left_eq, polar_smul_right_eq, polar_comm] at hij ⊢

end Rotation

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
