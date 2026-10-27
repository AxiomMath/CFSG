module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Phase1
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Sect6

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Sect6LocalAnalysis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    CFSG.EvenSporadicStandard.StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .HS → FourHyp G L f → IsTight L s → y * y = 1 → y * f * y⁻¹ = f⁻¹ →
    y ∉ L ⊔ zpowers f → centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y →
    (∃ g : G, y = g * f ^ 2 * g⁻¹) → (∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹) →
    (¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) →
    (∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L) → f ∈ S₀ →
    S₀ ≤ centralizer ({f ^ 2} : Set G) → S₀ ≤ centralizer ({s ^ 2} : Set G) → IsPGroup 2 S₀ →
    ¬ 2 ∣ S₀.relIndex (centralizer ({f ^ 2} : Set G)) →
    (∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀) → n * f ^ 2 * n⁻¹ = s ^ 2 →
    ∃ T U : Subgroup G, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ f ∈ T ∧ U ≤ T ∧ U.relIndex T = 2 ∧
      f ∉ U ∧ (∀ g : G, g⁻¹ * f * g ∉ U) ∧
      ∀ g : G, g⁻¹ * f ^ 2 * g ∈ T → g⁻¹ * f ^ 2 * g ∈ U

theorem solomonSection6Fusion_of_localAnalysis
    (h : Sect6LocalAnalysis) : SolomonSection6Fusion := by
  intro G _ _ L hL hZ hq S hS
  obtain ⟨f, H, s, y, hs, hyy, hyf, hy, hN, hyc, hsc, hn, hu, S₀, hfS₀, hS₀f, hS₀s, hS₀2,
    hS₀rel, n, hn1, hn2⟩ := hL.solomon_lemma_two_one_sylow hZ hq S hS
  obtain ⟨T, U, hT, hTidx, hfT, hUT, hUidx, hfU, hconj, ht⟩ :=
    h G L f s y S₀ n hL hZ hq H hs hyy hyf hy hN hyc hsc hn hu hfS₀ hS₀f hS₀s hS₀2 hS₀rel hn1 hn2
  have hfC : f ∈ centralizer (L : Set G) := H.mem_cent
  have hcard : Nat.card (centralizer (L : Set G)) = 4 := by
    rw [H.cent, Nat.card_zpowers, H.order]
  have hStop : (S : Subgroup (centralizer (L : Set G))) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hS, hcard])
  have hfS : (⟨f, hfC⟩ : centralizer (L : Set G)) ∈ (S : Subgroup (centralizer (L : Set G))) := by
    rw [hStop]; exact mem_top _
  refine ⟨⟨f, hfC⟩, hfS, ?_, T, U, hT, hTidx, hfT, hUT, hUidx, hfU, hconj, ht⟩
  rw [Subgroup.orderOf_mk]
  exact H.order

end CFSG.EvenSporadicStandard.TwoHS
