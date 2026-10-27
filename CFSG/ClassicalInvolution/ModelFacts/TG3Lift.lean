module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

section Lift

variable {G E X : Type*} [Group G] [Group E] [Group X] (θ : G →* E)

theorem sq_mem_centralizer_of_comm (hker : θ.ker ≤ Subgroup.center G)
    (hker2 : ∀ x ∈ θ.ker, x * x = 1) {κ w : G} (h : θ κ * θ w = θ w * θ κ) :
    κ * κ * w = w * (κ * κ) := by
  set ε : G := κ * w * κ⁻¹ * w⁻¹ with hε
  have hεk : ε ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hε]
    simp only [map_mul, map_inv]
    calc θ κ * θ w * (θ κ)⁻¹ * (θ w)⁻¹ = (θ w * θ κ) * (θ κ)⁻¹ * (θ w)⁻¹ := by rw [h]
      _ = 1 := by group
  have hc : ∀ y : G, y * ε = ε * y := fun y => Subgroup.mem_center_iff.mp (hker hεk) y
  have h2 : ε * ε = 1 := hker2 ε hεk
  have e1 : κ * w = ε * w * κ := by rw [hε]; group
  calc κ * κ * w = κ * (κ * w) := by group
    _ = κ * (ε * w * κ) := by rw [e1]
    _ = (κ * ε) * w * κ := by group
    _ = (ε * κ) * w * κ := by rw [hc κ]
    _ = ε * (κ * w) * κ := by group
    _ = ε * (ε * w * κ) * κ := by rw [e1]
    _ = (ε * ε) * w * (κ * κ) := by group
    _ = w * (κ * κ) := by rw [h2, one_mul]

theorem exists_lift_sq (hker : θ.ker ≤ Subgroup.center G) (hker2 : ∀ x ∈ θ.ker, x * x = 1)
    {e₀ : E} (he₀ : e₀ ∈ θ.range) {w : G} (h : e₀ * θ w = θ w * e₀) :
    ∃ h' : G, θ h' = e₀ * e₀ ∧ h' * w = w * h' := by
  obtain ⟨κ, rfl⟩ := he₀
  exact ⟨κ * κ, by rw [map_mul], sq_mem_centralizer_of_comm θ hker hker2 h⟩

theorem range_le_sup_of_lifts (ψ : G →* X) (hker : θ.ker ≤ Subgroup.center G) {w₂ w₃ : G}
    {S₂ S₃ : Subgroup E} (h₂ : S₂ ≤ (Subgroup.centralizer ({w₂} : Set G)).map θ)
    (h₃ : S₃ ≤ (Subgroup.centralizer ({w₃} : Set G)).map θ) (hcov : θ.range ≤ S₂ ⊔ S₃) :
    ψ.range ≤ (Subgroup.centralizer ({ψ w₂} : Set X) ⊓ ψ.range) ⊔
      (Subgroup.centralizer ({ψ w₃} : Set X) ⊓ ψ.range) := by
  set T : Subgroup X := (Subgroup.centralizer ({ψ w₂} : Set X) ⊓ ψ.range) ⊔
    (Subgroup.centralizer ({ψ w₃} : Set X) ⊓ ψ.range) with hT
  have hker_le : θ.ker ≤ T.comap ψ := by
    intro c hc
    have hcc : ∀ y : G, y * c = c * y := fun y => Subgroup.mem_center_iff.mp (hker hc) y
    refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨c, rfl⟩⟩)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hcc]
  have hS₂ : S₂ ≤ (T.comap ψ).map θ := by
    intro e he
    obtain ⟨h, hh, rfl⟩ := h₂ he
    refine ⟨h, ?_, rfl⟩
    refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hh]
  have hS₃ : S₃ ≤ (T.comap ψ).map θ := by
    intro e he
    obtain ⟨h, hh, rfl⟩ := h₃ he
    refine ⟨h, ?_, rfl⟩
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩)
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hh]
  rintro _ ⟨g, rfl⟩
  have hθg : θ g ∈ (T.comap ψ).map θ := sup_le hS₂ hS₃ (hcov ⟨g, rfl⟩)
  obtain ⟨m, hm, hmg⟩ := hθg
  have hg : g = m * (m⁻¹ * g) := by group
  have hk : m⁻¹ * g ∈ T.comap ψ := hker_le (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel])
  have : g ∈ T.comap ψ := by
    rw [hg]
    exact (T.comap ψ).mul_mem hm hk
  exact this

end Lift

section Orth

variable {G : Type*} [Group G] {F V : Type} [Field F] [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V}

theorem elemOn_le_map_centralizer (h2 : (2 : F) ≠ 0) (θ : G →* (V ≃ₗ[F] V))
    (hrange : θ.range = elementaryGroup Q) (hker : θ.ker ≤ Subgroup.center G)
    (hker2 : ∀ x ∈ θ.ker, x * x = 1) {S : Submodule F V} {w : G}
    (hfix : elemOn Q S ≤ Subgroup.centralizer ({θ w} : Set (V ≃ₗ[F] V))) :
    elemOn Q S ≤ (Subgroup.centralizer ({w} : Set G)).map θ := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, v, hu, hv, hQu, huv, rfl⟩
  have hv' : (2 : F)⁻¹ • v ∈ S := S.smul_mem _ hv
  have hpol : polar Q u ((2 : F)⁻¹ • v) = 0 := by rw [polar_smul_right_eq, huv, mul_zero]
  have hsq : eichler Q u v = eichler Q u ((2 : F)⁻¹ • v) * eichler Q u ((2 : F)⁻¹ • v) := by
    rw [eichler_mul hpol hpol, ← two_smul F ((2 : F)⁻¹ • v), smul_smul, mul_inv_cancel₀ h2,
      one_smul]
  have hmem : eichler Q u ((2 : F)⁻¹ • v) ∈ elemOn Q S := eichler_mem_elemOn hu hv'
  have hcomm : eichler Q u ((2 : F)⁻¹ • v) * θ w = θ w * eichler Q u ((2 : F)⁻¹ • v) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hfix hmem)
  have hr : eichler Q u ((2 : F)⁻¹ • v) ∈ θ.range := by
    rw [hrange]
    exact eichler_mem_elementaryGroup Q _ _
  obtain ⟨h', hθ, hc⟩ := exists_lift_sq θ hker hker2 hr hcomm
  exact ⟨h', Subgroup.mem_centralizer_singleton_iff.mpr hc, by rw [hθ, hsq]⟩

end Orth

end CFSG.ClassicalInvolution.ModelFacts.TG3
