module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.SeitzReduction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eichler_shear [CharP K 2] {Q : QuadraticForm K V} {W L : Submodule K V}
    (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {w u : V} (hw : w ∈ W) (hQw : Q w = 0)
    (hu : u ∈ L) :
    (∀ v ∈ L, eichler Q w u v = v + polar Q v u • w) ∧
      ∀ v, eichler Q w u v - v - polar Q v w • u ∈ W := by
  have hwu : polar Q w u = 0 := (hL u).1 hu w hw
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · have hvw : polar Q v w = 0 := by
      rw [polar_comm]
      exact (hL v).1 hv w hw
    rw [eichler_apply hQw hwu, hvw, zero_smul, add_zero, mul_zero, add_zero, sub_eq_add_neg,
      ← neg_smul, CharTwo.neg_eq]
  · rw [eichler_apply hQw hwu,
      show v + polar Q v w • u - (polar Q v u + Q u * polar Q v w) • w - v - polar Q v w • u =
        -((polar Q v u + Q u * polar Q v w) • w) by abel]
    exact W.neg_mem (W.smul_mem _ hw)

theorem exists_shear_of_commute_eichler [CharP K 2] {Q : QuadraticForm K V}
    {W L : Submodule K V} (hL : ∀ v, v ∈ L ↔ ∀ w ∈ W, polar Q w v = 0) {w u : V} (hw : w ∈ W)
    (hQw : Q w = 0) (hu : u ∈ L) {F : Type*} [FunLike F V V] {T : F}
    (hc : ∀ v, T (eichler Q w u v) = eichler Q w u (T v)) :
    ∃ g : V →+ V, (∀ v, T (g v) = g (T v)) ∧ (∀ v ∈ L, g v = v + polar Q v u • w) ∧
      ∀ v, g v - v - polar Q v w • u ∈ W :=
  ⟨(eichler Q w u).toLinearMap.toAddMonoidHom, hc, (eichler_shear hL hw hQw hu).1,
    (eichler_shear hL hw hQw hu).2⟩

end CFSG.SeitzReduction
