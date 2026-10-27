module

public import CFSG.GH74.L5U5.Models
public import CFSG.GH74.Generic.S1.RInvClasses

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup

section Core

variable {F : Type} [Field F]

theorem nbfus_xyGL_eq : xyGL F = xGL F * yGL F := by
  rw [xGL, yGL, xyGL, diagGL_mul]
  congr 1 <;> simp

theorem nbfus_det_conj (P W : GL (Fin 4) F) :
    ((P * W * P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (W : Matrix (Fin 4) (Fin 4) F).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    map_mul, map_mul, map_inv]
  congr 1
  exact mul_inv_cancel_comm _ _

theorem nbfus_core (M : ModelData F) {T P : GL (Fin 4) F} (hP : P ∈ M.U4)
    (hTP : T * P = P * yGL F) :
    P * swapGL F * P⁻¹ ∈ M.K4 ∧
      (P * swapGL F * P⁻¹) * T * (P * swapGL F * P⁻¹)⁻¹ = xGL F * T := by
  refine ⟨?_, ?_⟩
  · rw [M.mem_K4]
    refine ⟨M.U4.mul_mem (M.U4.mul_mem hP M.swap_mem) (M.U4.inv_mem hP), ?_⟩
    rw [nbfus_det_conj, coe_swapGL]
    exact det_wMat
  · have hT : T = P * yGL F * P⁻¹ := eq_mul_inv_of_mul_eq hTP
    calc (P * swapGL F * P⁻¹) * T * (P * swapGL F * P⁻¹)⁻¹
        = P * (swapGL F * yGL F * (swapGL F)⁻¹) * P⁻¹ := by
          rw [hT]; group
      _ = P * (xGL F * yGL F) * P⁻¹ := by rw [swapGL_mul_yGL_mul_inv, nbfus_xyGL_eq]
      _ = xGL F * (P * yGL F * P⁻¹) := by
          rw [← mul_assoc P, ← xGL_comm P]
          simp only [mul_assoc]
      _ = xGL F * T := by rw [hT]

theorem nbfus_of_model (M : ModelData F) {K : Type*} [Group K] (e : K ≃* ↥M.K4)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hP : ∀ T : GL (Fin 4) F, T ∈ M.K4 → T * T = 1 → T ≠ 1 → T ≠ xGL F →
      ∃ P : GL (Fin 4) F, P ∈ M.U4 ∧ T * P = P * yGL F)
    {w t : K} (hw : w ∈ Subgroup.center K) (hw1 : w ≠ 1) (ht : t * t = 1) (h1 : t ≠ 1)
    (htw : t ≠ w) : ∃ g : K, g * t * g⁻¹ = w * t := by
  have hwc : ((e w : ↥M.K4) : GL (Fin 4) F) = 1 ∨ ((e w : ↥M.K4) : GL (Fin 4) F) = xGL F :=
    (hcenter _).1 ((mem_center_iff_of_mulEquiv e w).2 hw)
  have hwx : ((e w : ↥M.K4) : GL (Fin 4) F) = xGL F := by
    rcases hwc with h | h
    · exact absurd (e.injective (Subtype.ext (by rw [map_one]; exact h))) hw1
    · exact h
  have hT2 : ((e t : ↥M.K4) : GL (Fin 4) F) * ((e t : ↥M.K4) : GL (Fin 4) F) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, ht, map_one]
    rfl
  have hT1 : ((e t : ↥M.K4) : GL (Fin 4) F) ≠ 1 := fun h =>
    h1 (e.injective (Subtype.ext (by rw [map_one]; exact h)))
  have hTx : ((e t : ↥M.K4) : GL (Fin 4) F) ≠ xGL F := fun h =>
    htw (e.injective (Subtype.ext (by rw [hwx]; exact h)))
  obtain ⟨P, hPU, hTP⟩ := hP _ (e t).2 hT2 hT1 hTx
  obtain ⟨hs, hst⟩ := nbfus_core M hPU hTP
  refine ⟨e.symm ⟨_, hs⟩, ?_⟩
  apply e.injective
  apply Subtype.ext
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hst, hwx]

end Core

section Mat

variable {F : Type} [Field F]

theorem nbfus_yGL_matrix :
    ((yGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
  rw [yGL, coe_diagGL, Units.val_neg, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock, Matrix.reindex_apply,
      Matrix.submatrix_apply, e0, e1, e2, e3]

theorem nbfus_rinvSign : rinvSign F 4 2 = ![-1, -1, 1, 1] := by
  funext j
  fin_cases j <;> simp [rinvSign]

theorem nbfus_lin (h2 : (2 : F) ≠ 0) :
    ∀ T : GL (Fin 4) F, T ∈ (ModelData.lin F).K4 → T * T = 1 → T ≠ 1 → T ≠ xGL F →
      ∃ P : GL (Fin 4) F, P ∈ (ModelData.lin F).U4 ∧ T * P = P * yGL F := by
  intro T hT hT2 hT1 hTx
  have hdet : (T : Matrix (Fin 4) (Fin 4) F).det = 1 := (((ModelData.lin F).mem_K4 _).1 hT).2
  have hTT : (T : Matrix (Fin 4) (Fin 4) F) * (T : Matrix (Fin 4) (Fin 4) F) = 1 := by
    simpa using congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hT2
  have hT1' : (T : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h => hT1 (Units.ext h)
  have hm1 : (T : Matrix (Fin 4) (Fin 4) F) ≠ -1 := fun h =>
    hTx (Units.ext (by rw [xGL_eq_neg_one]; simpa using h))
  obtain ⟨P, hPu, hTP⟩ := CFSG.GH74.Generic.exists_conj_diag4 h2 _ hTT
    (CFSG.GH74.Generic.involution_dim_two h2 (Fintype.card_fin 4) _ hTT hdet hT1' hm1)
  refine ⟨hPu.unit, Subgroup.mem_top _, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hTP, nbfus_yGL_matrix]

end Mat

section Uni

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [CharP F p] in
theorem nbfus_unitaryFieldData (hF : Nat.card F = (p ^ f) ^ 2) : UnitaryFieldData p f F := by
  have hf : 1 ≤ f := by
    by_contra hf0
    have hf0' : f = 0 := by omega
    subst hf0'
    have : 1 < Nat.card F := Finite.one_lt_card
    simp at hF
    omega
  exact ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩

theorem nbfus_uni (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) :
    ∀ T : GL (Fin 4) F, T ∈ (ModelData.uni hF).K4 → T * T = 1 → T ≠ 1 → T ≠ xGL F →
      ∃ P : GL (Fin 4) F, P ∈ (ModelData.uni hF).U4 ∧ T * P = P * yGL F := by
  intro T hT hT2 hT1 hTx
  have h := nbfus_unitaryFieldData (F := F) hF
  obtain ⟨hdet, hU⟩ := (mem_unitarySU_iff h).1 hT
  have hTT : (T : Matrix (Fin 4) (Fin 4) F) * (T : Matrix (Fin 4) (Fin 4) F) = 1 := by
    simpa using congrArg (fun x : GL (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F)) hT2
  have hT1' : (T : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h => hT1 (Units.ext h)
  have hm1 : (T : Matrix (Fin 4) (Fin 4) F) ≠ -1 := fun h =>
    hTx (Units.ext (by rw [xGL_eq_neg_one]; simpa using h))
  have hdim := CFSG.GH74.Generic.involution_dim_two h2 (Fintype.card_fin 4) _ hTT hdet hT1' hm1
  have hf2 : ∀ v, Matrix.toLin' (T : Matrix (Fin 4) (Fin 4) F)
      (Matrix.toLin' (T : Matrix (Fin 4) (Fin 4) F) v) = v := rinv_toLin_involutive _ hTT
  have hsum := CFSG.GH74.Generic.involution_finrank_add h2
    (Matrix.toLin' (T : Matrix (Fin 4) (Fin 4) F)) hf2
  have h4 : Module.finrank F (Fin 4 → F) = 4 := by simp
  have hb : Module.finrank F
      (LinearMap.ker (Matrix.toLin' (T : Matrix (Fin 4) (Fin 4) F) - LinearMap.id)) = 2 := by
    omega
  obtain ⟨B, hB1, hB2, hon⟩ := rinv_orthonormal_basis h h2 _ hTT hU 2 2 hdim hb
  have hab : 2 + 2 = 4 := rfl
  have hTP := rinvMat_mul_eq hab B _ hB1 hB2
  have hPu := rinvMat_isUnit hab B
  have hPU := rinvMat_unitary h hab B hon
  refine ⟨hPu.unit, ?_, ?_⟩
  · have hσ : (⇑(unitaryInvolution F p f) : F → F) = ⇑h.bar :=
      funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
    change conjTr (unitaryInvolution F p f) ((hPu.unit : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((hPu.unit : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
    rw [IsUnit.unit_spec, conjTr, hσ]
    exact hPU
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hTP, nbfus_rinvSign, nbfus_yGL_matrix]

end Uni

theorem nb_fusion_sl4 {K : Type} [Group K] [Finite K] (hK : IsSL4Model K) {w t : K}
    (hw : w ∈ center K) (hw1 : w ≠ 1) (hw2 : w * w = 1) (ht : t * t = 1) (h1 : t ≠ 1)
    (htw : t ≠ w) : ∃ g : K, g * t * g⁻¹ = w * t := by
  have _ := hw2
  rcases hK with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
    have h2 := two_ne_zero_of_odd_card (F := F) hodd
    exact nbfus_of_model (ModelData.lin F) e (mem_center_lin_iff hF) (nbfus_lin h2) hw hw1 ht h1
      htw
  · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
    have h2 := two_ne_zero_of_odd_card (F := F) hodd
    exact nbfus_of_model (ModelData.uni hF) e (mem_center_uni_iff hF hq) (nbfus_uni hF h2) hw hw1
      ht h1 htw

end CFSG.GH74.Generic.S1.Exo
