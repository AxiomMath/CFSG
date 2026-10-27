module

public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddRee
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddBasic

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem odd_quadratic_field_not_smallType (hK : ringChar K ≠ 2) {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup τ K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  classical
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (fixedSubgroup β).map (adjointGroup τ K).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ K) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(fixedSubgroup β) ≃* ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  exact not_smallType_of_subgroupEquiv (e₁.trans e₂)
    (fun M hM => entrywiseFixedGroup_component_not_smallType hK δ hM) hL

theorem odd_GFE_not_smallType (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (hK : Odd (Nat.card K))
    (α : MulAut (adjointGroup τ K)) (hα : α ^ 2 = 1) {L : Subgroup (adjointGroup τ K)}
    (hL : Assembly.IsComponentOf L (fixedSubgroup α)) : ¬ SmallType L := by
  obtain ⟨p, f, hp, hp2, hf, hchar, hcard⟩ := exists_odd_prime_pow_card_of_odd hK
  have hK2 : ringChar K ≠ 2 := hchar ▸ hp2
  have hτ4 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  by_cases h3 : τ = .G2 ∧ p = 3
  ·
    obtain ⟨hG2, rfl⟩ := h3
    obtain rfl : τ = ReeTag.G2.tag := hG2
    have : CharP K ReeTag.G2.prime := ringChar.of_eq hchar
    rcases G2_three_involution_inner_quadratic_or_exceptional hf hcard hα with ⟨g, a, hαg⟩ |
      ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hb, rfl⟩
    · exact odd_inner_diagonal_not_smallType hτ4 hK hαg hα hL
    · exact odd_quadratic_field_not_smallType hK2 Nat.prime_three he hKe δ hδ hαg hα hL
    · exact small_ree_involution_not_smallType (hb ▸ hcard) g hα hL
  · have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
      rcases hτ with h | h | h
      · exact Or.inr (Or.inr ⟨h, fun h' => h3 ⟨h, hchar ▸ h'⟩⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hK hα with ⟨g, a, hαg⟩ |
      ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
    · exact odd_inner_diagonal_not_smallType hτ4 hK hαg hα hL
    · exact odd_quadratic_field_not_smallType hK2 hq he hKe δ hδ hαg hα hL

end CFSG.ComponentClassification.ExcSelector
