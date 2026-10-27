module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerIndex
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K]

theorem finrank_V4 : Module.finrank K (HypIndex 2 0 → K) = 4 := by
  rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]

theorem card_hypSU_four_eight [Finite K] (h : UnitaryFieldData 2 3 K) :
    Nat.card (hypSU h 2 0) = 262144 * 63 * 513 * 4095 := by
  have hn : Module.finrank K (HypIndex 2 0 → K) = 4 := finrank_V4
  have hSU := (unitary_full_group_order h (hypForm_isSymm h) (hypForm_separatingLeft h) hn
    (by norm_num)).2.1
  have hcard : Nat.card (hypSU h 2 0) = Nat.card (sesqSpecialUnitaryGroup (hypForm h 2 0)) :=
    card_gramSU h (hypGram 2 0 K)
  rw [hcard]
  norm_num [Finset.prod_Icc_succ_top] at hSU
  exact_mod_cast hSU

theorem finrank_le_two_of_isotropic_four [Finite K] (h : UnitaryFieldData 2 3 K)
    (W : Submodule K (HypIndex 2 0 → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) :
    Module.finrank K W ≤ 2 := by
  have hsurj : Function.Surjective h.bar := Finite.surjective_of_injective h.bar.injective
  have hle : W ≤ W.orthogonalBilin (hypForm h 2 0) := fun x hx y hy => hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  have h2 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hsurj
    (hypForm_separatingLeft h) W
  rw [finrank_V4] at h2
  omega

theorem perp_eq_of_finrank_two [Finite K] (h : UnitaryFieldData 2 3 K)
    (W : Submodule K (HypIndex 2 0 → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0)
    (hk : Module.finrank K W = 2) : W.orthogonalBilin (hypForm h 2 0) = W := by
  have hsurj : Function.Surjective h.bar := Finite.surjective_of_injective h.bar.injective
  have hle : W ≤ W.orthogonalBilin (hypForm h 2 0) := fun x hx y hy => hW y hy x hx
  have h2 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hsurj
    (hypForm_separatingLeft h) W
  rw [finrank_V4, hk] at h2
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem index_isoStab_point [Finite K] (h : UnitaryFieldData 2 3 K)
    (W : Submodule K (HypIndex 2 0 → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0)
    (hk : Module.finrank K W = 1) : (isoStabilizer h 2 0 W).index = 33345 := by
  have hcount := (isotropic_stabilizer_index h W hW).2.1
  have h33 : isoIndexCount (2 ^ 3) (2 * 2 + 0) 1 = 33345 := by
    rw [(isotropic_stabilizer_index h W hW).2.2.2.2.1 (2 * 2 + 0)]
    norm_num
  have hq : ((isoStabilizer h 2 0 W).index : ℚ) = 33345 := by
    rw [hcount, hk, h33]
  exact_mod_cast hq

theorem not_five_dvd_of_le_isoStab_point [Finite K] (h : UnitaryFieldData 2 3 K)
    (W : Submodule K (HypIndex 2 0 → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0)
    (hk : Module.finrank K W = 1) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W) :
    ¬ 5 ∣ Nat.card X := by
  intro h5
  have hidx := index_isoStab_point h W hW hk
  have hmul := Subgroup.card_mul_index (isoStabilizer h 2 0 W)
  rw [hidx, card_hypSU_four_eight h] at hmul
  have hstab : Nat.card (isoStabilizer h 2 0 W) = 262144 * 3969 := by omega
  have hdvd : Nat.card X ∣ Nat.card (isoStabilizer h 2 0 W) := Subgroup.card_dvd_of_le hX
  rw [hstab] at hdvd
  have h5' : 5 ∣ 262144 * 3969 := h5.trans hdvd
  norm_num at h5'

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

end
