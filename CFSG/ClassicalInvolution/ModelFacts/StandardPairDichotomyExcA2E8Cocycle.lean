module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Cocycle

variable {k : Type} [Field k] [IsAlgClosed k]

theorem signDiagE8_mem_levi (δ : Fin (Tag.rank .E8) → ℤ) :
    signDiagE8 k δ ∈ parabolicLevi .E8 k JE8 :=
  torusGroup_le_parabolicLevi JE8 (rootDiagUnit_mem_torusGroup _)

omit [IsAlgClosed k] in
theorem rootChar_thetaDiag_partnerE8 {δ : Fin (Tag.rank .E8) → ℤ} (hδ : IsPartnerE8 δ) :
    rootChar (thetaDiag δ (-1 : kˣ)) thetaE8 = -1 := by
  rw [rootChar_thetaDiag, iform_comm, hδ.2, zpow_neg_one]
  exact Units.ext (by simp)

theorem eq_levi_or_eq_levi_mul_WSL_E8 (hk : ringChar k ≠ 2) {δ : Fin (Tag.rank .E8) → ℤ}
    (hδ : IsPartnerE8 δ) {u : ModGL .E8 k} (hu : u ∈ h1E8 k)
    (hud : u * signDiagE8 k δ = signDiagE8 k δ * u) :
    u ∈ parabolicLevi .E8 k JE8 ∨
      ∃ m ∈ parabolicLevi .E8 k JE8, u = m * rootSL2 .E8 k thetaE8 WSL := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hinj : Function.Injective (rootSL2 .E8 k thetaE8) :=
    ((exceptional_Lang_root_rank_one_data .E8 k thetaE8).2.2.2.2.2.2.2.1 hk).1
  set ρ := rootSL2 .E8 k thetaE8 with hρ
  set d := signDiagE8 k δ with hd
  obtain ⟨s, yd, hydJ, hydc, hds'⟩ := exists_factor_levi_E8 (signDiagE8_mem_levi (k := k) δ)
  have hds : d = ρ (HSL s) * yd := hds'
  have hs2 : (s : k) ^ 2 = -1 := by
    have h1 := (rootDiagUnit_conj_rootSL2 (thetaDiag δ (-1 : kˣ)) isRoot_thetaE8 (1 : k)).1
    rw [rootChar_thetaDiag_partnerE8 hδ] at h1
    have h3 : d * ρ (uSL 1) * d⁻¹ = ρ (uSL ((s : k) ^ 2 * 1)) := by
      have hyu : yd * ρ (uSL 1) * yd⁻¹ = ρ (uSL 1) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hydc _
      calc d * ρ (uSL 1) * d⁻¹ = ρ (HSL s) * (yd * ρ (uSL 1) * yd⁻¹) * (ρ (HSL s))⁻¹ := by
            rw [hds]; group
        _ = ρ (HSL s) * ρ (uSL 1) * (ρ (HSL s))⁻¹ := by rw [hyu]
        _ = _ := by rw [hρ, rootSL2_HSL_conj_uSL]
    have h4 : ρ (uSL ((s : k) ^ 2 * 1)) = ρ (uSL (((-1 : kˣ) : k) * 1)) := by
      rw [← h3]
      exact h1
    have h5 := uSL_injective_of_field (hinj h4)
    simpa using h5
  obtain ⟨B, y, hyJ, hyc, hub⟩ := exists_factor_h1E8 hu
  let Yc : Subgroup (ModGL .E8 k) := Subgroup.centralizer (Set.range ρ)
  have hmemY : ∀ g : ModGL .E8 k, (∀ A : SL2 k, g * ρ A = ρ A * g) → g ∈ Yc := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun h ⟨A, hA⟩ => by rw [← hA]; exact (hg A).symm
  have hyY : y ∈ Yc := hmemY y hyc
  have hydY : yd ∈ Yc := hmemY yd hydc
  have hmain : ρ B * ρ (HSL s) * (y * yd) = ρ (HSL s) * ρ B * (yd * y) := by
    have h1 : u * d = d * u := hud
    rw [hub, hds] at h1
    calc ρ B * ρ (HSL s) * (y * yd) = ρ B * (ρ (HSL s) * y) * yd := by group
      _ = ρ B * (y * ρ (HSL s)) * yd := by rw [hyc (HSL s)]
      _ = (ρ B * y) * (ρ (HSL s) * yd) := by group
      _ = (ρ (HSL s) * yd) * (ρ B * y) := h1
      _ = ρ (HSL s) * (yd * ρ B) * y := by group
      _ = ρ (HSL s) * (ρ B * yd) * y := by rw [hydc B]
      _ = ρ (HSL s) * ρ B * (yd * y) := by group
  have hZ : ρ (B⁻¹ * (HSL s)⁻¹ * B * HSL s) ∈ Yc := by
    have e : ρ (B⁻¹ * (HSL s)⁻¹ * B * HSL s) = (yd * y) * (y * yd)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (ρ B)⁻¹ * (ρ (HSL s))⁻¹ * ρ B * ρ (HSL s) =
          (ρ (HSL s) * ρ B)⁻¹ * (ρ B * ρ (HSL s) * (y * yd)) * (y * yd)⁻¹ := by group
        _ = (ρ (HSL s) * ρ B)⁻¹ * (ρ (HSL s) * ρ B * (yd * y)) * (y * yd)⁻¹ := by rw [hmain]
        _ = _ := by group
    rw [e]
    exact mul_mem (mul_mem hydY hyY) (inv_mem (mul_mem hyY hydY))
  have hcent : ∀ A : SL2 k, (B⁻¹ * (HSL s)⁻¹ * B * HSL s) * A =
      A * (B⁻¹ * (HSL s)⁻¹ * B * HSL s) := by
    intro A
    apply hinj
    rw [map_mul ρ _ A, map_mul ρ A _]
    exact (Subgroup.mem_centralizer_iff.1 hZ (ρ A) ⟨A, rfl⟩).symm
  have hdiag : B * HSL s = HSL s * B ∨ B * HSL s = HSL (-1) * (HSL s * B) := by
    have e : B * HSL s = HSL s * B * (B⁻¹ * (HSL s)⁻¹ * B * HSL s) := by group
    rcases eq_one_or_HSL_neg_one_of_forall_commute hcent with h1 | h1
    · left
      rw [e, h1, mul_one]
    · right
      rw [e, h1]
      exact (HSL_neg_one_mul_comm_A2 _).symm
  rcases sl2_diag_or_anti h2 hs2 hdiag with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · left
    rw [hub]
    exact mul_mem (rootSL2_HSL_mem_levi_E8 a) hyJ
  · right
    refine ⟨ρ (HSL b) * y, mul_mem (rootSL2_HSL_mem_levi_E8 b) hyJ, ?_⟩
    rw [hub, map_mul]
    calc ρ (HSL b) * ρ WSL * y = ρ (HSL b) * (ρ WSL * y) := by group
      _ = ρ (HSL b) * (y * ρ WSL) := by rw [hyc WSL]
      _ = _ := by group

end Cocycle

end CFSG.ClassicalInvolution.ModelFacts.Levi
