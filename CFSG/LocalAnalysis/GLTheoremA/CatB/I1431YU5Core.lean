module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Two2
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Ord

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding
open scoped Pointwise

theorem core_hyp {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {h : UnitaryFieldData 2 1 K} {W : Submodule K (HypIndex 2 1 → K)} (hW0 : W ≠ ⊥)
    (hWiso : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 1 x y = 0)
    (X : Subgroup (hypSU h 2 1)) (hX : X ≤ isoStabilizer h 2 1 W)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : Nat.card T = 360) :
    ¬ ∃ φ : X →* T, Function.Surjective φ := by
  have hle2 := finrank_le_two_of_isotropic h W hWiso
  have hge1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  rcases (show Module.finrank K W = 1 ∨ Module.finrank K W = 2 by omega) with hk | hk
  · rintro ⟨φ, hφ⟩
    have hd : Nat.card T ∣ Nat.card X := by
      have h1 := Subgroup.card_map_dvd (⊤ : Subgroup X) φ
      rw [Subgroup.map_top_of_surjective φ hφ, Subgroup.card_top, Subgroup.card_top] at h1
      exact h1
    have h5 : 5 ∣ Nat.card X := by
      rw [hT] at hd
      exact (by norm_num : (5 : ℕ) ∣ 360).trans hd
    exact not_five_dvd_of_le_isoStab_one h W hWiso hk X hX h5
  · exact no_surj_two hK hWiso hk X hX T hT

theorem smul_eq_self_of_mulVec_stable' {K : Type} [Field K] {n : ℕ} (x : GL (Fin n) K)
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

theorem core_stated {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (W : Submodule K (Fin 5 → K)) (hW0 : W ≠ ⊥) (hWiso : CFSG.AGLEmbedding.IsTotallyIsotropicSU 2 W)
    (X : Subgroup (StatedSU 5 2 K))
    (hXW : ∀ y ∈ X, ∀ w ∈ W, ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w ∈ W)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : Nat.card T = 360) :
    ¬ ∃ φ : X →* T, Function.Surjective φ := by
  rintro ⟨φ, hφ⟩
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let h : UnitaryFieldData 2 1 K := ToralCensus.unitaryFieldData_of_card_eq_sq hK1 le_rfl
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 1)
  set Tr := transportSubspace h hR with hTdef
  set W' : Submodule K (HypIndex 2 1 → K) := Tr.symm W with hW'def
  have hTW : Tr W' = W := Tr.apply_symm_apply W
  have hW'0 : W' ≠ ⊥ := by
    intro hbot
    apply hW0
    rw [← hTW, hbot]
    exact map_bot Tr
  have hW'iso : ∀ x ∈ W', ∀ y ∈ W', hypForm h 2 1 x y = 0 := by
    refine (isTotallyIsotropic_transportSubspace hR W').mpr ?_
    rw [hTW]
    exact (ToralCensus.isTotallyIsotropicSU_iff h W).mp hWiso
  let Ψ : unitarySU 2 1 K (2 * 2 + 1) ≃* hypSU h 2 1 := (hypTransport h hR).symm
  let X₁ : Subgroup (unitarySU 2 1 K (2 * 2 + 1)) := X
  have hYQ : X₁.map Ψ.toMonoidHom ≤ isoStabilizer h 2 1 W' := by
    rintro _ ⟨x, hx, rfl⟩
    refine MulAction.mem_stabilizer_iff.mpr ?_
    apply (transportSubspace h hR).injective
    rw [transportSubspace_smul hR, hTW]
    have hxΨ : hypTransport h hR (Ψ x) = x := (hypTransport h hR).apply_symm_apply x
    rw [MulEquiv.coe_toMonoidHom, hxΨ]
    exact smul_eq_self_of_mulVec_stable' (x : GL (Fin 5) K) W
      (fun w hw => hXW x hx w hw)
      (fun w hw => hXW _ (inv_mem hx) w hw)
  let φ' : X₁.map Ψ.toMonoidHom →* T := φ.comp (MulEquiv.subgroupMap Ψ X₁).symm.toMonoidHom
  have hφ' : Function.Surjective φ' := by
    intro t
    obtain ⟨x, hx⟩ := hφ t
    refine ⟨(MulEquiv.subgroupMap Ψ X₁) x, ?_⟩
    show φ (((MulEquiv.subgroupMap Ψ X₁).symm) ((MulEquiv.subgroupMap Ψ X₁) x)) = t
    rw [MulEquiv.symm_apply_apply]
    exact hx
  exact core_hyp hK hW'0 hW'iso (X₁.map Ψ.toMonoidHom) hYQ T hT ⟨φ', hφ'⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5

end
