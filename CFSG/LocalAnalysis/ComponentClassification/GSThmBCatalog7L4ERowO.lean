module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EForms
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

namespace Catalog7L4E

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {k : Type} [Field k] [Finite k]

theorem exists_sq_ne_one (h5 : 5 ≤ Nat.card k) : ∃ a : k, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  have := Fintype.ofFinite k
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1, -1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 := h a ha
      have : (a - 1) * (a + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h2 | h2
      · simp [sub_eq_zero.mp h2]
      · simp [eq_neg_of_add_eq_zero_left h2]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 : ({0, 1, -1} : Finset k).card ≤ 3 := Finset.card_le_three
  omega

omit [Finite k] in
theorem exists_singular_plane (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) :
    ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧ ∀ x ∈ S, (ψ x).det = 0 := by
  classical
  set u : Fin 2 → (Fin 4 → k) := ![ψ.symm !![0, 1; 0, 0], ψ.symm !![0, 0; 0, 1]] with hu
  have hli : LinearIndependent k u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 := congrArg ψ hc
    rw [map_sum, map_zero] at h1
    simp only [Fin.sum_univ_two, hu, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
      LinearEquiv.apply_symm_apply] at h1
    have e1 := congrFun (congrFun h1 0) 1
    have e2 := congrFun (congrFun h1 1) 1
    simp at e1 e2
    fin_cases i
    · exact e1
    · exact e2
  refine ⟨Submodule.span k (Set.range u), ?_, fun x hx => ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hx
    simp only [Fin.sum_univ_two, hu, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, LinearEquiv.apply_symm_apply]
    rw [det_fin_two]
    simp

theorem split_of_commute_factor (hk2 : ringChar k ≠ 2) (h5 : 5 ≤ Nat.card k)
    {A B : GL (Fin 4) k} (hA : (A : Matrix (Fin 4) (Fin 4) k)ᵀ = A)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B) (ψ : (Fin 4 → k) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k)
    (hψ : ∀ v, v ⬝ᵥ (((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v) = (ψ v).det)
    {f : SpecialLinearGroup (Fin 2) k →* GL (Fin 4) k}
    (hf : f = splitLeftHom ψ ∨ f = splitRightHom ψ)
    (hcA : ∀ U, conjAut 4 k (f U) ∈ centralizer {conjAut 4 k A * dualAut 4 k})
    (hcB : ∀ U, conjAut 4 k (f U) ∈ centralizer {conjAut 4 k B * dualAut 4 k}) :
    ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0 := by
  classical
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 k le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  set G := f.range with hG
  have hGp : ⁅G, G⁆ = G := by
    have : Group.IsPerfect G := Group.IsPerfect.ofSurjective (f := f.rangeRestrict)
      f.rangeRestrict_surjective
    exact Subgroup.commutator_eq_self (H := G)
  have hGA : G ≤ CatalogueBGraphForm.isometryGroup 4 k A⁻¹ := by
    rw [← hGp]
    refine graph_commutator_le_isometry (by norm_num) A ?_
    rintro _ ⟨U, rfl⟩
    exact hcA U
  have hGB : G ≤ CatalogueBGraphForm.isometryGroup 4 k B⁻¹ := by
    rw [← hGp]
    refine graph_commutator_le_isometry (by norm_num) B ?_
    rintro _ ⟨U, rfl⟩
    exact hcB U
  set Am : Matrix (Fin 4) (Fin 4) k := (A : Matrix (Fin 4) (Fin 4) k) with hAm
  set Ai : Matrix (Fin 4) (Fin 4) k := ((A⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) with hAi
  set Bi : Matrix (Fin 4) (Fin 4) k := ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) with hBi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAiT : Aiᵀ = Ai := transpose_inv_eq_of_transpose_eq hA
  have hBiT : Biᵀ = Bi := transpose_inv_eq_of_transpose_eq hB
  set W : GL (Fin 4) k := A * B⁻¹ with hW
  have hWm : (W : Matrix (Fin 4) (Fin 4) k) = Am * Bi := by rw [hW, Units.val_mul]
  have hiso : ∀ (R : GL (Fin 4) k) (g : GL (Fin 4) k), g ∈ CatalogueBGraphForm.isometryGroup 4 k R →
      (g : Matrix (Fin 4) (Fin 4) k)ᵀ * R * g = R := fun R g hg =>
    (CatalogueBGraphForm.mem_isometryGroup 4 k R g).mp hg
  have hcomm : ∀ g ∈ G, W * g = g * W := by
    intro g hg
    have hA1 := hiso _ g (hGA hg)
    have hB1 := hiso _ g (hGB hg)
    apply Units.ext
    change (W : Matrix (Fin 4) (Fin 4) k) * (g : Matrix (Fin 4) (Fin 4) k) =
      (g : Matrix (Fin 4) (Fin 4) k) * W
    rw [hWm]
    set gm : Matrix (Fin 4) (Fin 4) k := (g : Matrix (Fin 4) (Fin 4) k) with hgm
    set gi : Matrix (Fin 4) (Fin 4) k := ((g⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
      with hgi
    have hggi : gm * gi = 1 := by rw [hgm, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hgig : gi * gm = 1 := by rw [hgm, hgi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hA2 : Ai * gm = giᵀ * Ai := by
      calc Ai * gm = (gm * gi)ᵀ * Ai * gm := by rw [hggi, transpose_one, Matrix.one_mul]
        _ = giᵀ * (gmᵀ * Ai * gm) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = giᵀ * Ai := by rw [hA1]
    have hB2 : Bi * gm = giᵀ * Bi := by
      calc Bi * gm = (gm * gi)ᵀ * Bi * gm := by rw [hggi, transpose_one, Matrix.one_mul]
        _ = giᵀ * (gmᵀ * Bi * gm) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
        _ = giᵀ * Bi := by rw [hB1]
    have hA3 : Am * giᵀ = gm * Am := by
      calc Am * giᵀ = Am * (giᵀ * Ai) * Am := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc giᵀ, hAiA, Matrix.mul_one]
        _ = Am * (Ai * gm) * Am := by rw [hA2]
        _ = gm * Am := by rw [← Matrix.mul_assoc, hAAi, Matrix.one_mul]
    calc Am * Bi * gm = Am * (giᵀ * Bi) := by rw [Matrix.mul_assoc, hB2]
      _ = gm * (Am * Bi) := by rw [← Matrix.mul_assoc, hA3, Matrix.mul_assoc]
  have hsa : (W : Matrix (Fin 4) (Fin 4) k)ᵀ * Ai = Ai * W := by
    rw [hWm, transpose_mul, hBiT, hA, Matrix.mul_assoc, hAAi, Matrix.mul_one, ← Matrix.mul_assoc,
      hAiA, Matrix.one_mul]
  obtain ⟨a, ha0, ha1⟩ := exists_sq_ne_one h5
  have hscalar : ∃ c : kˣ, W = GeneralLinearGroup.scalar (Fin 4) c := by
    rcases hf with rfl | rfl
    · exact eq_scalar_of_commute_splitLeft ψ htwo ha0 ha1 hAiT hψ W
        (fun U => hcomm _ ⟨U, rfl⟩) hsa
    · exact eq_scalar_of_commute_splitRight ψ htwo ha0 ha1 hAiT hψ W
        (fun U => hcomm _ ⟨U, rfl⟩) hsa
  obtain ⟨c, hc⟩ := hscalar
  have hBA : Bi = (c : k) • Ai := by
    have h1 : Ai * (W : Matrix (Fin 4) (Fin 4) k) = Bi := by
      rw [hWm, ← Matrix.mul_assoc, hAiA, Matrix.one_mul]
    rw [← h1, hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
  obtain ⟨S, hS, hS0⟩ := exists_singular_plane ψ
  refine ⟨S, hS, fun x hx => ?_⟩
  rw [CatalogueBLinearHigherB.matrixQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply,
    CatalogueBLinearHigherB.matrixForm_apply]
  change x ⬝ᵥ Bi *ᵥ x = 0
  rw [hBA, Matrix.smul_mulVec, dotProduct_smul, hψ x, hS0 x hx, smul_zero]

end Catalog7L4E

end CFSG.ComponentClassification.OddSelector
