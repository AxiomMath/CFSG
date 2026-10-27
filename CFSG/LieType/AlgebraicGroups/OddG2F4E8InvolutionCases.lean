module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem exists_odd_prime_pow_card_of_odd (hK : Odd (Nat.card K)) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ ringChar K = p ∧ Nat.card K = p ^ f := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  refine ⟨ringChar K, n, hp, fun h2 => ?_, n.pos, rfl, by rw [Nat.card_eq_fintype_card, hcard]⟩
  rw [Nat.card_eq_fintype_card, hcard, h2] at hK
  exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)

theorem odd_F4_E8_G2_involution_inner_or_quadratic
    (hτ : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3)) (hK : Odd (Nat.card K))
    {α : MulAut (adjointGroup τ K)} (hα : α ^ 2 = 1) :
    (∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), ∀ h : adjointGroup τ K,
      (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹) ∨
    ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ Nat.card K = (p ^ e) ^ 2 ∧ ∃ δ : K ≃+* K,
      (∀ c, δ c = c ^ (p ^ e)) ∧ ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
          Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
            (g : ModGL τ K)⁻¹ := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have h1 : ∀ x : ModGL τ K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hhalf : Even f → 1 ≤ f / 2 ∧ Nat.card K = (p ^ (f / 2)) ^ 2 := fun hev => by
    refine ⟨?_, ?_⟩
    · obtain ⟨m, rfl⟩ := hev
      omega
    · rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hcard]
  have hτ' : τ = .E8 ∨ τ = .F4 ∨ (τ = .G2 ∧ p ≠ 3) := by
    rcases hτ with hτ | hτ | ⟨hτ, h3⟩
    · exact Or.inr (Or.inl hτ)
    · exact Or.inl hτ
    · exact Or.inr (Or.inr ⟨hτ, hchar ▸ h3⟩)
  rcases hτ' with hτ | hτ'
  ·
    obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form τ (Or.inr (Or.inr hτ)) K
    obtain ⟨Θ, -, -, -, hsq, hquad⟩ :=
      ordinary_E_field_graph_quotient_and_involutions τ (Or.inr (Or.inr hτ)) K
    obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF α
    have hQ : exactQ τ K ε = 1 := by
      subst hτ
      rfl
    have hα' : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
          (g : ModGL τ K)⁻¹ := fun h => by
      rw [hgaσ h, hQ, mul_one, inv_one, mul_one]
    by_cases hσ1 : σ = 1
    · subst hσ1
      exact Or.inl ⟨g, a, fun h => by rw [hα' h, h1]⟩
    · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hcard σ (hsq α g a σ ε hgaσ hα) hσ1
      obtain ⟨he, hKe⟩ := hhalf hev
      exact Or.inr ⟨p, f / 2, hp, he, hKe, σ, hσc, g, a, hα'⟩
  ·
    obtain ⟨hNF, Θ, hΘ, -, -, hinv⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hcard τ hτ'
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α
    have hΘα := hΘ α g σ hgσ
    rcases hinv α hα with hσ1 | ⟨hev, hσ, -⟩
    · refine Or.inl ⟨g, 1, fun h => ?_⟩
      rw [hgσ h, ← hΘα, hσ1, h1, rootDiagUnit_one]
      group
    · obtain ⟨he, hKe⟩ := hhalf hev
      refine Or.inr ⟨p, f / 2, hp, he, hKe, σ, fun c => by rw [← hΘα, hσ], g, 1, fun h => ?_⟩
      rw [hgσ h, rootDiagUnit_one]
      group

theorem G2_three_involution_inner_quadratic_or_exceptional
    [CharP K ReeTag.G2.prime] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) {α : MulAut (adjointGroup ReeTag.G2.tag K)}
    (hα : α ^ 2 = 1) :
    (∃ (g : adjointGroup ReeTag.G2.tag K) (a : Fin ReeTag.G2.tag.rank → Kˣ),
      ∀ h : adjointGroup ReeTag.G2.tag K, (α h : ModGL ReeTag.G2.tag K) =
        (g : ModGL ReeTag.G2.tag K) * rootDiagUnit ReeTag.G2.tag a * h *
          (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag K)⁻¹) ∨
    (∃ e : ℕ, 1 ≤ e ∧ Nat.card K = (3 ^ e) ^ 2 ∧ ∃ δ : K ≃+* K, (∀ c, δ c = c ^ (3 ^ e)) ∧
      ∃ (g : adjointGroup ReeTag.G2.tag K) (a : Fin ReeTag.G2.tag.rank → Kˣ),
        ∀ h : adjointGroup ReeTag.G2.tag K, (α h : ModGL ReeTag.G2.tag K) =
          (g : ModGL ReeTag.G2.tag K) * rootDiagUnit ReeTag.G2.tag a *
            Units.map (entrywiseHom δ.toRingHom) (h : ModGL ReeTag.G2.tag K) *
              (rootDiagUnit ReeTag.G2.tag a)⁻¹ * (g : ModGL ReeTag.G2.tag K)⁻¹) ∨
    ∃ (b : ℕ) (g : adjointGroup ReeTag.G2.tag K), f = 2 * b + 1 ∧
      α = MulAut.conj g * ReeTag.G2.finiteReeAut K b := by
  obtain ⟨-, hNF, -, hk, -, hEven, hOdd⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
  rcases hk α g k k.2 hgk hα with hk0 | hkf
  · refine Or.inl ⟨g, 1, fun h => ?_⟩
    rw [hgk, hk0, pow_zero, mul_one, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, rootDiagUnit_one]
    group
  · rcases Nat.even_or_odd f with hfe | ⟨b, hb⟩
    · obtain ⟨-, σ, -, -, hσ, -, hφσ⟩ := hEven hfe
      refine Or.inr (Or.inl ⟨f / 2, ?_, ?_, σ, hσ, g, 1, fun h => ?_⟩)
      · obtain ⟨m, rfl⟩ := hfe
        omega
      · rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hfe), hK]
      · rw [hgk, hkf, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, hφσ, rootDiagUnit_one]
        group
    · obtain ⟨-, hFb, -⟩ := hOdd b hb
      exact Or.inr (Or.inr ⟨b, g, hb, by rw [hgk, hkf, hFb]⟩)

end CFSG.LieType.AlgebraicGroups
