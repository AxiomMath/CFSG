module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerIndex
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open scoped Pointwise

variable {K : Type} [Field K]

theorem card_hypSU_two_one [Finite K] (h : UnitaryFieldData 2 1 K) :
    Nat.card (hypSU h 2 1) = 13685760 := by
  have hn : Module.finrank K (HypIndex 2 1 → K) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hSU := (unitary_full_group_order h (hypForm_isSymm h) (hypForm_separatingLeft h) hn
    (by norm_num)).2.1
  have hcard : Nat.card (hypSU h 2 1) = Nat.card (sesqSpecialUnitaryGroup (hypForm h 2 1)) :=
    card_gramSU h (hypGram 2 1 K)
  rw [hcard]
  norm_num [Finset.prod_Icc_succ_top] at hSU
  exact_mod_cast hSU

theorem finrank_le_two_of_isotropic [Finite K] (h : UnitaryFieldData 2 1 K)
    (W : Submodule K (HypIndex 2 1 → K)) (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0) :
    Module.finrank K W ≤ 2 := by
  have hsurj : Function.Surjective h.bar := Finite.surjective_of_injective h.bar.injective
  have hV : Module.finrank K (HypIndex 2 1 → K) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hle : W ≤ W.orthogonalBilin (hypForm h 2 1) := fun x hx =>
    fun y hy => hW y hy x hx
  have h1 := Submodule.finrank_mono hle
  have h2 := CFSG.HardMathSupport.Curtis.UnitaryLevi.finrank_orthogonalBilin_eq hsurj
    (hypForm_separatingLeft h) W
  omega

theorem index_isoStab_one [Finite K] (h : UnitaryFieldData 2 1 K) (W : Submodule K (HypIndex 2 1 → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0) (hk : Module.finrank K W = 1) :
    (isoStabilizer h 2 1 W).index = 165 := by
  have hcount := (isotropic_stabilizer_index h W hW).2.1
  have h165 : isoIndexCount (2 ^ 1) (2 * 2 + 1) 1 = 165 := by
    rw [(isotropic_stabilizer_index h W hW).2.2.2.2.1 (2 * 2 + 1)]
    norm_num
  have hq : ((isoStabilizer h 2 1 W).index : ℚ) = 165 := by
    rw [hcount, hk, h165]
  exact_mod_cast hq

theorem not_five_dvd_of_le_isoStab_one [Finite K] (h : UnitaryFieldData 2 1 K)
    (W : Submodule K (HypIndex 2 1 → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0) (hk : Module.finrank K W = 1)
    (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W) : ¬ 5 ∣ Nat.card X := by
  intro h5
  have hidx := index_isoStab_one h W hW hk
  have hmul := Subgroup.card_mul_index (isoStabilizer h 2 1 W)
  rw [hidx, card_hypSU_two_one h] at hmul
  have hstab : Nat.card (isoStabilizer h 2 1 W) = 82944 := by omega
  have hdvd : Nat.card X ∣ Nat.card (isoStabilizer h 2 1 W) := Subgroup.card_dvd_of_le hX
  rw [hstab] at hdvd
  have h5' : 5 ∣ 82944 := (h5.trans hdvd)
  norm_num at h5'

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

end
