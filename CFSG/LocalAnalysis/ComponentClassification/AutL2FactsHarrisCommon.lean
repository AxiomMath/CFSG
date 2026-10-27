module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisShapeStd

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F] {K : Subgroup (PGammaL2 F)}

omit [Finite F] in
theorem mem_map_conj_iff (g : PGammaL2 F) (A : Subgroup (PGammaL2 F)) (x : PGammaL2 F) :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite F] in
theorem map_conj_inv_map_conj (g : PGammaL2 F) (A : Subgroup (PGammaL2 F)) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  ext x
  rw [mem_map_conj_iff, mem_map_conj_iff, inv_inv]
  constructor
  · intro h
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h
  · intro h
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group]

theorem IsFieldInvModel.right_ne_one {x : PGammaL2 F} (hx : IsFieldInvModel x) : x.right ≠ 1 := by
  obtain ⟨b, σ, hσ, rfl⟩ := hx
  rw [right_conj]
  intro h
  rw [SemidirectProduct.right_inr] at h
  rw [h, orderOf_one] at hσ
  norm_num at hσ

theorem HarrisHyp.pow_half_eq_of_shape (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {v : PGammaL2 F}
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (stdTS F K) v) :
    ∃ s : Fˣ, (s = 1 ∨ s = -1) ∧ v ^ (orderOf v / 2) = nm F s (epsR F) (psiF F) := by
  have hw : v ^ (orderOf v / 2) ∈ stdTS F K := pow_mem hv.mem _
  have hC := hv.comm_v₀
  rw [hH.stdTS_inf hK] at hC
  obtain ⟨s, hs, h | h⟩ := hH.eq_of_centralizes_rStd hw.1 hC
  · exfalso
    apply hv.field₀.right_ne_one
    rw [h]
    rfl
  · exact ⟨s, hs, h⟩

theorem mem_centralizer_pm_iff {s : Fˣ} (hs : s = 1 ∨ s = -1) {x : PGammaL2 F}
    (hx : x ∈ sylS0 F) :
    x ∈ centralizer {nm F s (epsR F) (psiF F)} ↔ x ∈ centralizer {v0Std F} := by
  obtain ⟨a, -, ε, σ, -, rfl⟩ := hx
  have hS : nm F s (epsR F) (psiF F) = nm F s false 1 * v0Std F := by
    rw [nm_mul]
    simp [fu_one]
  have hc := nm_pm_one_comm hs a ε σ
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hS]
  constructor
  · intro h
    apply mul_left_cancel (a := nm F s false 1)
    calc nm F s false 1 * (nm F a ε σ * v0Std F) = nm F a ε σ * (nm F s false 1 * v0Std F) := by
          rw [← mul_assoc, hc, mul_assoc]
      _ = nm F s false 1 * v0Std F * nm F a ε σ := h
      _ = nm F s false 1 * (v0Std F * nm F a ε σ) := by rw [mul_assoc]
  · intro h
    calc nm F a ε σ * (nm F s false 1 * v0Std F) = nm F s false 1 * (nm F a ε σ * v0Std F) := by
          rw [← mul_assoc, ← hc, mul_assoc]
      _ = nm F s false 1 * (v0Std F * nm F a ε σ) := by rw [h]
      _ = nm F s false 1 * v0Std F * nm F a ε σ := by rw [mul_assoc]

theorem HarrisHyp.sup_eq_of_shape (hH : HarrisHyp F) (hK : pGammaL2PSLRange F ≤ K)
    {v : PGammaL2 F}
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (stdTS F K) v) :
    (stdTS F K ⊓ pGammaL2PSLRange F) ⊔ zpowers v = stdTS F K ⊓ centralizer {v0Std F} := by
  obtain ⟨s, hs, hw⟩ := hH.pow_half_eq_of_shape hK hv
  rw [← hv.centralizer_v₀, hw]
  ext x
  constructor
  · rintro ⟨hxT, hxC⟩
    exact ⟨hxT, (mem_centralizer_pm_iff hs hxT.1).mp hxC⟩
  · rintro ⟨hxT, hxC⟩
    exact ⟨hxT, (mem_centralizer_pm_iff hs hxT.1).mpr hxC⟩

theorem SylowShape.conj_std {T : Subgroup (PGammaL2 F)} {v g : PGammaL2 F}
    (hT : T = (stdTS F K).map (MulAut.conj g).toMonoidHom)
    (hv : SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel T v) :
    SylowShape (pGammaL2PSLRange F) IsFieldInvModel IsFieldAutModel (stdTS F K)
      (MulAut.conj g⁻¹ v) := by
  have := hv.map (MulAut.conj g⁻¹) (pslRange_map_conj g⁻¹) (isFieldInvModel_conj_iff g⁻¹)
    (isFieldAutModel_conj_iff g⁻¹)
  rwa [hT, map_conj_inv_map_conj] at this

end CFSG.ComponentClassification.AutL2Facts
