module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69O
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest9

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def Lemma69Out {G : Type} [Group G] (L : Subgroup G) (z t : G) (E S : Subgroup G) :
    Prop :=
  ∃ α : G, AlphaSpec S z t α ∧
    (∀ c : G, (∀ u ∈ S ⊔ E, c * u = u * c) → c = 1 ∨ c = t) ∧
    XSet S E z = (blk z {1, t} ∪ blk z (E2 E t)) ∪ blk (α * z) (E4 E t) ∧
    (∀ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G),
      m * α * m⁻¹ = α ∨ m * α * m⁻¹ = α * t) ∧
    Nat.card ↥(normalizer ((S ⊔ E : Subgroup G) : Set G)) = 122880 ∧
    normalizer ((S ⊔ E : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G) =
      (L ⊓ centralizer ({t} : Set G)) ⊔ zpowers z

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G} {S : Subgroup G}

theorem lemma69 (h : Hyp69 L z t T₀ E Q x β B S) : Lemma69Out L z t E S := by
  obtain ⟨α, hα⟩ := h.exists_alpha
  exact ⟨α, hα, fun c hc => h.cent_U hc, h.X_eq hα, fun m hm => h.alpha_orbit hα hm,
    h.card_M hα, h.CMz_eq⟩

@[expose] def Fin76bInnerRest₁₀ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → BetaData65 E β →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) → z ∈ S →
      Nonempty (S ≃* DihedralGroup 4) → (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
      (∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) →
      (∃ hz : z ∈ centralizer ({β} : Set G),
        WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩)) →
      (∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) →
      (∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
        ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹) →
      Lemma69Out L z t E S →
      ∃ Rs R : Subgroup G, IsPGroup 2 Rs ∧ R ≤ Rs ∧ R.relIndex Rs = 2 ∧ z ∈ Rs ∧ z ∉ R ∧
        (∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹) ∧
        ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G))

theorem fin76bInnerRest₉_of_rest₁₀ (hE : Fin76bEFacts69) (hF : Fin76bFusion69)
    (h10 : Fin76bInnerRest₁₀) : Fin76bInnerRest₉ := by
  intro G _ _ L z t T₀ E Q x β B hconf hW hBD S hS2 hSC hSmax hzS hD8 hBS hodd h66 h67 h68
  have hH : Hyp69 L z t T₀ E Q x β B S :=
    ⟨hconf, hW, hE G L z t T₀ E Q x β B hconf, hS2, hSC, hSmax, hzS, hD8, hBS, hodd, h67, h68,
      hF G L z t T₀ E Q x β B hconf hW hBD h66⟩
  exact h10 G L z t T₀ E Q x β B hconf hW hBD S hS2 hSC hSmax hzS hD8 hBS hodd h66 h67 h68
    (lemma69 hH)

end CFSG.EvenSporadicStandard.Fin76b
