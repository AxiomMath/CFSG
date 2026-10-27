module

public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerIndex
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups
open scoped Pointwise

theorem card_hypSU_two_two {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 1 K) :
    Nat.card (hypSU h 2 0) = 25920 := by
  have hn : Module.finrank K (HypIndex 2 0 → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  have hSU := (unitary_full_group_order h (hypForm_isSymm h) (hypForm_separatingLeft h) hn
    (by norm_num)).2.1
  have hcard : Nat.card (hypSU h 2 0) = Nat.card (sesqSpecialUnitaryGroup (hypForm h 2 0)) :=
    card_gramSU h (hypGram 2 0 K)
  rw [hcard]
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)] at hSU
  norm_num at hSU
  exact_mod_cast hSU

theorem smul_eq_self_of_mulVec_stable {K : Type} [Field K] {n : ℕ} (x : GL (Fin n) K)
    (W : Submodule K (Fin n → K))
    (hx : ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (hx' : ∀ w ∈ W, ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W) :
    x • W = W := by
  rw [smul_eq_map]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact hx w hw
  · intro w hw
    refine ⟨((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w, hx' w hw, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    have hinv : (x : Matrix (Fin n) (Fin n) K) *
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hinv, Matrix.one_mulVec]

theorem not_dvd_card_of_stabilizes_isotropic {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) (X : Subgroup (StatedSU 4 2 K)) (W : Submodule K (Fin 4 → K))
    (hW0 : W ≠ ⊥) (hWiso : IsTotallyIsotropicSU 2 W)
    (hXW : ∀ y ∈ X, ∀ w ∈ W, ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ w ∈ W) :
    ¬ 360 ∣ Nat.card X := by
  intro hdvd
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let h : UnitaryFieldData 2 1 K := ToralCensus.unitaryFieldData_of_card_eq_sq hK1 le_rfl
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 0)
  set T := transportSubspace h hR with hTdef
  set W' : Submodule K (HypIndex 2 0 → K) := T.symm W with hW'def
  have hTW : T W' = W := T.apply_symm_apply W
  have hW'0 : W' ≠ ⊥ := by
    intro hbot
    apply hW0
    rw [← hTW, hbot]
    exact map_bot T
  have hW'iso : ∀ x ∈ W', ∀ y ∈ W', hypForm h 2 0 x y = 0 := by
    refine (isTotallyIsotropic_transportSubspace hR W').mpr ?_
    rw [hTW]
    exact (ToralCensus.isTotallyIsotropicSU_iff h W).mp hWiso
  have hW1 : 1 ≤ Module.finrank K W' := Submodule.one_le_finrank_iff.mpr hW'0
  have hW2 : 2 * Module.finrank K W' ≤ 2 * 2 + 0 := by
    obtain ⟨Wc, hWc, -⟩ := exists_isotropicChain_eq W' hW'iso
    have hdim : Module.finrank K (HypIndex 2 0 → K) = 2 * 2 + 0 := by
      rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
    have := ((isotropic_flag_extension h (hypForm_isSymm (r := 2) (ε := 0) h)
      (hypForm_separatingLeft h) hdim).1 _ Wc hWc).1
    omega
  have hk : Module.finrank K W' = 1 ∨ Module.finrank K W' = 2 := by omega
  have hidx' : (isoStabilizer h 2 0 W').index = 45 ∨ (isoStabilizer h 2 0 W').index = 27 := by
    have hcount := (isotropic_stabilizer_index h W' hW'iso).2.1
    rcases hk with hk | hk
    · left
      have h45 : isoIndexCount (2 ^ 1) (2 * 2 + 0) 1 = 45 := by
        rw [(isotropic_stabilizer_index h W' hW'iso).2.2.2.2.1 (2 * 2 + 0)]
        norm_num
      have : ((isoStabilizer h 2 0 W').index : ℚ) = 45 := by rw [hcount, hk, h45]
      exact_mod_cast this
    · right
      have h27 : isoIndexCount (2 ^ 1) (2 * 2 + 0) 2 = 27 := by
        rw [show 2 * 2 + 0 = 2 * 2 from rfl,
          (isotropic_stabilizer_index h W' hW'iso).2.2.2.2.2.1 2,
          show Finset.Icc 1 2 = {1, 2} from rfl, Finset.prod_pair (by norm_num)]
        norm_num
      have : ((isoStabilizer h 2 0 W').index : ℚ) = 27 := by rw [hcount, hk, h27]
      exact_mod_cast this
  have hQcard : Nat.card (isoStabilizer h 2 0 W') * (isoStabilizer h 2 0 W').index = 25920 := by
    rw [Subgroup.card_mul_index, card_hypSU_two_two h]
  have hQ : Nat.card (isoStabilizer h 2 0 W') = 576 ∨
      Nat.card (isoStabilizer h 2 0 W') = 960 := by
    rcases hidx' with h' | h'
    · left
      rw [h'] at hQcard
      omega
    · right
      rw [h'] at hQcard
      omega
  let Ψ : unitarySU 2 1 K (2 * 2 + 0) ≃* hypSU h 2 0 := (hypTransport h hR).symm
  let X₁ : Subgroup (unitarySU 2 1 K (2 * 2 + 0)) := X
  have hYQ : X₁.map Ψ.toMonoidHom ≤ isoStabilizer h 2 0 W' := by
    rintro _ ⟨x, hx, rfl⟩
    refine MulAction.mem_stabilizer_iff.mpr ?_
    apply (transportSubspace h hR).injective
    rw [transportSubspace_smul hR, hTW]
    have hxΨ : hypTransport h hR (Ψ x) = x := (hypTransport h hR).apply_symm_apply x
    rw [MulEquiv.coe_toMonoidHom, hxΨ]
    exact smul_eq_self_of_mulVec_stable (x : GL (Fin 4) K) W
      (fun w hw => hXW x hx w hw)
      (fun w hw => hXW _ (inv_mem hx) w hw)
  have hcardY : Nat.card (X₁.map Ψ.toMonoidHom) = Nat.card X₁ :=
    Subgroup.card_map_of_injective (fun a b hab => Ψ.injective hab)
  have hdivY : Nat.card (X₁.map Ψ.toMonoidHom) ∣ Nat.card (isoStabilizer h 2 0 W') :=
    Subgroup.card_dvd_of_le hYQ
  have h360 : 360 ∣ Nat.card (isoStabilizer h 2 0 W') := by
    have hdvdY : 360 ∣ Nat.card (X₁.map Ψ.toMonoidHom) := by
      rw [hcardY]
      exact hdvd
    exact dvd_trans hdvdY hdivY
  rcases hQ with hQ | hQ
  · rw [hQ] at h360
    norm_num at h360
  · rw [hQ] at h360
    norm_num at h360

end CFSG.LieType.BorelTits
