module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76G2Roots
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2Part1

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

theorem smul_gC_cases
    (w : WeylGroup .G2) :
    w • gC = gA ∨ w • gC = gB ∨ w • gC = gC ∨ w • gC = -gA ∨ w • gC = -gB ∨ w • gC = -gC := by
  have h : w • gC = w • g2a + w • g2a + (w • g2r + w • g2r + w • g2r) := smul_g2c w
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [h, ha, hr] <;> decide

variable
  {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem exists_conj_pinnedX_c {x : ModGL .G2 K} (hx : x ∈ adjointGroup .G2 K) :
    ∃ u ∈ posUnipotent .G2 K, ∃ w : WeylGroup .G2, ∃ κ : Kˣ, ∀ s : K,
      x * X gC s * x⁻¹ = u * X (w • gC) (κ * s) * u⁻¹ := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hx
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
  obtain ⟨c₂, hc₂⟩ := exists_torus_scale hh₂ isRoot_gC
  obtain ⟨ε, hε, hn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w isRoot_gC
  obtain ⟨c₁, hc₁⟩ := exists_torus_scale hh₁ (IsRoot.smul isRoot_gC w)
  set n := canonicalRep (coxeterSystem .G2) K w
  refine ⟨h₁ * u₁ * h₁⁻¹, torus_conj_mem_posUnipotent hh₁ hu₁, w, c₁ * ⟨ε, ε, hε, hε⟩ * c₂,
    fun s => ?_⟩
  have hu : u₂ * X gC s * u₂⁻¹ = X gC s := by
    have hc : Commute (X gC s) u₂ := commute_pinnedX_c_posUnipotent s hu₂
    rw [hc.symm.eq, mul_inv_cancel_right]
  calc h₁ * u₁ * n * (h₂ * u₂) * X gC s * (h₁ * u₁ * n * (h₂ * u₂))⁻¹ =
        h₁ * u₁ * (n * (h₂ * (u₂ * X gC s * u₂⁻¹) * h₂⁻¹) * n⁻¹) * u₁⁻¹ * h₁⁻¹ := by group
    _ = (h₁ * u₁ * h₁⁻¹) * (h₁ * X (w • gC) (ε * (c₂ * s)) * h₁⁻¹) * (h₁ * u₁ * h₁⁻¹)⁻¹ := by
        rw [hu, hc₂, hn]; group
    _ = _ := by
        rw [hc₁]
        congr 3
        simp only [Units.val_mul]
        ring

theorem exists_eq_mul_pinnedX_r {u : ModGL .G2 K} (hu : u ∈ posUnipotent .G2 K) :
    ∃ q ∈ Qg K, ∃ t : K, u = q * X gR t := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  have hq : X gA B * X gU C * X gV D * X gB E * X gC F ∈ Qg K :=
    mul_mem (mul_mem (mul_mem (mul_mem (X_mem_Qg isQRoot_a B) (X_mem_Qg isQRoot_u C))
      (X_mem_Qg isQRoot_v D)) (X_mem_Qg isQRoot_b E)) (X_mem_Qg isQRoot_c F)
  refine ⟨_, Xr_normalizes A _ hq, A, ?_⟩
  simp only [g2N]
  change X gR A * X gA B * X gU C * X gV D * X gB E * X gC F = _
  group

theorem exists_conj_pinnedX_c_forms {x : ModGL .G2 K} (hx : x ∈ adjointGroup .G2 K)
    (hxc : ¬ Commute (x * X gC 1 * x⁻¹) (X gC 1)) :
    ∃ q ∈ Qg K, ∃ κ : Kˣ,
      (∀ s : K, x * X gC s * x⁻¹ = q * X (-gC) (κ * s) * q⁻¹) ∨
      (∀ s : K, x * X gC s * x⁻¹ = q * X (-gA) (κ * s) * q⁻¹) ∨
      ∃ t : K, ∀ s : K, x * X gC s * x⁻¹ = q * X gR t * X (-gB) (κ * s) * (q * X gR t)⁻¹ := by
  obtain ⟨u, hu, w, κ, h⟩ := exists_conj_pinnedX_c hx
  obtain ⟨q, hq, t, rfl⟩ := exists_eq_mul_pinnedX_r hu
  have hpos : ∀ {γ : Fin Tag.G2.rank → ℤ}, IsRoot .G2 γ → 0 < height γ → w • gC = γ → False := by
    intro γ hγ hp hw
    refine hxc ?_
    rw [h 1, hw]
    have hX : ∀ s : K, X γ s ∈ posUnipotent .G2 K := fun s =>
      pinnedX_mem_rootSpan (S := {α | IsRoot .G2 α ∧ 0 < height α}) ⟨hγ, hp⟩ s
    exact (commute_pinnedX_c_posUnipotent 1 (mul_mem (mul_mem hu (hX _)) (inv_mem hu)) :
      Commute (X gC 1) _).symm
  refine ⟨q, hq, κ, ?_⟩
  rcases smul_gC_cases w with hw | hw | hw | hw | hw | hw
  · exact (hpos isRoot_gA (by decide) hw).elim
  · exact (hpos isRoot_gB (by decide) hw).elim
  · exact (hpos isRoot_gC (by decide) hw).elim
  · refine Or.inr (Or.inl fun s => ?_)
    rw [h s, hw, show q * X gR t * X (-gA) (κ * s) * (q * X gR t)⁻¹ =
      q * (X gR t * X (-gA) (κ * s) * (X gR t)⁻¹) * q⁻¹ by group,
      (commute_r_negA t (κ * s)).eq, mul_inv_cancel_right]
  · exact Or.inr (Or.inr ⟨t, fun s => by rw [h s, hw]⟩)
  · refine Or.inl fun s => ?_
    rw [h s, hw, show q * X gR t * X (-gC) (κ * s) * (q * X gR t)⁻¹ =
      q * (X gR t * X (-gC) (κ * s) * (X gR t)⁻¹) * q⁻¹ by group,
      (commute_r_negC t (κ * s)).eq, mul_inv_cancel_right]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max
