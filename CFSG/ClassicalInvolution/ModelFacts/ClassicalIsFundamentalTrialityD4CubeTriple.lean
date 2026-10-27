module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeUnip

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable {k : Type} [Field k]

theorem rho_neg_ne {β : Fin d4.rank → ℤ} (hne : rho β ≠ β) : rho (-β) ≠ -β := by
  intro h
  apply hne
  have h2 : -(rho β) = -β := (permLattice_neg _ β).symm.trans h
  exact neg_injective h2

theorem eq_fixedPointsIn_tripleGroup_sup_of_conj (F : ModGL d4 k →* ModGL d4 k)
    {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) (hne : rho β ≠ β) (u : ModGL d4 k)
    {J : Subgroup (ModGL d4 k)} (hJF : ∀ y ∈ J, F y = y) {Kf : Subfield k} {q : ℕ}
    (hKf : Nat.card Kf = q ^ 3) [Finite (fixedPointsIn (tripleGroup k β) F)]
    [Finite (fixedPointsIn (tripleGroup k (-β)) F)]
    (hcard : Nat.card (fixedPointsIn (tripleGroup k β) F) ≤ q ^ 3)
    (hcard' : Nat.card (fixedPointsIn (tripleGroup k (-β)) F) ≤ q ^ 3)
    (ψ : SL(2, Kf) →* ModGL d4 k)
    (hJ : ∀ y, y ∈ J.map (MulAut.conj u).toMonoidHom ↔ ∃ A, y = ψ A)
    (hX : ∃ α₀ : k, α₀ ≠ 0 ∧ ∀ c : Kf, ∃ b d : k, u⁻¹ * ψ (uSL c) * u =
      pinnedX d4 k β (α₀ * c) * pinnedX d4 k (rho β) b * pinnedX d4 k (rho (rho β)) d)
    (hY : ∃ δ₀ : k, δ₀ ≠ 0 ∧ ∀ c : Kf, ∃ b d : k, u⁻¹ * ψ (vSL c) * u =
      pinnedX d4 k (-β) (δ₀ * c) * pinnedX d4 k (rho (-β)) b *
        pinnedX d4 k (rho (rho (-β))) d) :
    J = fixedPointsIn (tripleGroup k β) F ⊔ fixedPointsIn (tripleGroup k (-β)) F := by
  classical
  have hβ' : IsRoot d4 (-β) := IsRoot.neg hβ
  have hne' : rho (-β) ≠ -β := rho_neg_ne hne
  obtain ⟨α₀, hα₀, hXc⟩ := hX
  obtain ⟨δ₀, hδ₀, hYc⟩ := hY
  have hρJ : ∀ A : SL(2, Kf), u⁻¹ * ψ A * u ∈ J := by
    intro A
    obtain ⟨y, hy, hyA⟩ := Subgroup.mem_map.1 ((hJ _).2 ⟨A, rfl⟩)
    have : y = u⁻¹ * ψ A * u := by
      rw [← hyA]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [← this]
  have hup : ∀ c : Kf, u⁻¹ * ψ (uSL c) * u ∈ fixedPointsIn (tripleGroup k β) F := by
    intro c
    obtain ⟨b, d, h⟩ := hXc c
    exact mem_fixedPointsIn.2 ⟨(mem_tripleGroup_iff hβ hne).2 ⟨_, b, d, h⟩, hJF _ (hρJ _)⟩
  have hvp : ∀ c : Kf, u⁻¹ * ψ (vSL c) * u ∈ fixedPointsIn (tripleGroup k (-β)) F := by
    intro c
    obtain ⟨b, d, h⟩ := hYc c
    exact mem_fixedPointsIn.2 ⟨(mem_tripleGroup_iff hβ' hne').2 ⟨_, b, d, h⟩, hJF _ (hρJ _)⟩
  apply le_antisymm
  ·
    intro y hy
    obtain ⟨A, hA⟩ := (hJ (u * y * u⁻¹)).1 (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    have hy' : y = u⁻¹ * ψ A * u := by
      rw [← hA]
      group
    rw [hy']
    set S := fixedPointsIn (tripleGroup k β) F ⊔ fixedPointsIn (tripleGroup k (-β)) F with hS
    let φ : SL(2, Kf) →* ModGL d4 k := (MulAut.conj u⁻¹).toMonoidHom.comp ψ
    have hφ : ∀ A, φ A = u⁻¹ * ψ A * u := fun A => by
      simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have htop : S.comap φ = ⊤ := by
      rw [eq_top_iff, ← sl2_closure_upper_lower (K := Kf), Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
        exact Subgroup.mem_sup_left (hup c)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
        exact Subgroup.mem_sup_right (hvp c)
    have hA' : A ∈ S.comap φ := by rw [htop]; exact Subgroup.mem_top A
    rw [Subgroup.mem_comap, hφ] at hA'
    exact hA'
  · refine sup_le ?_ ?_
    · let f : Kf → fixedPointsIn (tripleGroup k β) F := fun c => ⟨_, hup c⟩
      have hfi : Function.Injective f := by
        intro c c' h
        have h1 := congrArg Subtype.val h
        simp only [f] at h1
        obtain ⟨b, d, e1⟩ := hXc c
        obtain ⟨b', d', e2⟩ := hXc c'
        rw [e1, e2] at h1
        obtain ⟨h3, -, -⟩ := pinnedX_rho_mul_inj hβ hne h1
        exact Subtype.ext (mul_left_cancel₀ hα₀ h3)
      have hbij : Function.Bijective f := hfi.bijective_of_nat_card_le (by
        rw [hKf]
        exact hcard)
      intro g hg
      obtain ⟨c, hc⟩ := hbij.2 ⟨g, hg⟩
      have := congrArg Subtype.val hc
      simp only [f] at this
      rw [← this]
      exact hρJ _
    · let f : Kf → fixedPointsIn (tripleGroup k (-β)) F := fun c => ⟨_, hvp c⟩
      have hfi : Function.Injective f := by
        intro c c' h
        have h1 := congrArg Subtype.val h
        simp only [f] at h1
        obtain ⟨b, d, e1⟩ := hYc c
        obtain ⟨b', d', e2⟩ := hYc c'
        rw [e1, e2] at h1
        obtain ⟨h3, -, -⟩ := pinnedX_rho_mul_inj hβ' hne' h1
        exact Subtype.ext (mul_left_cancel₀ hδ₀ h3)
      have hbij : Function.Bijective f := hfi.bijective_of_nat_card_le (by
        rw [hKf]
        exact hcard')
      intro g hg
      obtain ⟨c, hc⟩ := hbij.2 ⟨g, hg⟩
      have := congrArg Subtype.val hc
      simp only [f] at this
      rw [← this]
      exact hρJ _

end CFSG.ClassicalInvolution.ModelFacts
