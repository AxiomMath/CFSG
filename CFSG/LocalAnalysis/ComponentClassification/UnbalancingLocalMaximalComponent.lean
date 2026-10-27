module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrFusionBridge
public import CFSG.Foundations.GilmanSolomonGrammarChains
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorConfiguration

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS

variable {G : Type*} [Group G]

theorem normalizer_zpowers_eq_centralizer {b : G} (hb : orderOf b = 2) :
    normalizer (zpowers b : Set G) = centralizer ({b} : Set G) := by
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by decide)
  have hzp : ∀ c ∈ zpowers b, c = 1 ∨ c = b := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  ext g
  rw [mem_normalizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hconj : g * b * g⁻¹ = b := by
      rcases hzp _ ((hg b).1 (mem_zpowers b)) with h | h
      · exfalso
        apply hb1
        calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
      · exact h
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · intro hg h
    have hconj : g * b * g⁻¹ = b := by rw [hg, mul_inv_cancel_right]
    have hgh : ∀ k : ℤ, g * b ^ k * g⁻¹ = b ^ k := fun k => by
      rw [← conj_zpow, hconj]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      rw [hgh]
      exact zpow_mem (mem_zpowers b) k
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      have : h = b ^ k := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = g⁻¹ * b ^ k * g := by rw [hk]
          _ = g⁻¹ * (g * b ^ k * g⁻¹) * g := by rw [hgh]
          _ = b ^ k := by group
      rw [this]
      exact zpow_mem (mem_zpowers b) k

theorem isComponentOf_of_pComponent [Finite G] (hB : CFSG.Assembly.ComponentType.LocalBProperty G)
    {b : G} (hb : orderOf b = 2) {L : Subgroup G} (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G)))) :
    CFSG.Assembly.IsComponentOf L (centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; exact absurd hb (by decide)
  have hS0 : zpowers b ≠ ⊥ := fun h => hb1 (by
    have hmem : b ∈ zpowers b := mem_zpowers b
    rw [h] at hmem
    exact hmem)
  have hS02 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hN := normalizer_zpowers_eq_centralizer hb
  have hcomp := CFSG.LocalAnalysis.ComponentInitial.two_components_ordinary_of_localB hB hS0
    hS02 (le_of_eq hN.symm) (by rw [hN]; exact CFSG.Assembly.IsSubnormal.refl _) _ hL
  exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLb).2
    hcomp

theorem pComponent_vertex [Finite G] (hB : CFSG.Assembly.ComponentType.LocalBProperty G)
    {b : G} (hb : orderOf b = 2) {L : Subgroup G} (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G)))) :
    IsQuasisimple L ∧ IsQuasisimple (L ⧸ pPrimeCore 2 L) ∧
      CFSG.Open.fusionZStar L = center L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLq : IsQuasisimple L := (AssemblyBPredicates.isQuasisimple_iff_native L).1
    (isComponentOf_of_pComponent hB hb hLb hL).2.2
  have hLq' : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLb).1 hL).2.2
  exact ⟨hLq, hLq', zStar_eq_center hLq hLq'⟩

theorem local_B_maximal_correspondence_component_existence [Finite G]
    (hcomp : CFSG.Assembly.IsComponentType G) (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G, J ≤ centralizer ({a} : Set G) ∧
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) ∧
      CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set G)) ∧
      CFSG.Open.fusionMaximalComponent J ∧
      (∀ b : G, orderOf b = 2 → ∀ L : Subgroup G, L ≤ centralizer ({b} : Set G) →
        IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))) →
          (CFSG.Open.fusionZStar L).index ≤ (CFSG.Open.fusionZStar J).index) ∧
      ∀ L : Subgroup G, CFSG.Open.fusionReach J L →
        IsQuasisimple L ∧ CFSG.Open.fusionZStar L = center L ∧
          Nonempty (L ⧸ center L ≃* J ⧸ center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := {p : G × Subgroup G // orderOf p.1 = 2 ∧ p.2 ≤ centralizer ({p.1} : Set G) ∧
    IsPComponent 2 (p.2.subgroupOf (centralizer ({p.1} : Set G)))}
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Nonempty P := by
    obtain ⟨t, ht, L₀, -, -, -, hL₀⟩ :=
      (CFSG.LocalAnalysis.ComponentInitial.component_type_perfect_local_lift G).2 hcomp
    refine ⟨⟨(t, L₀.map (centralizer ({t} : Set G)).subtype), ht, map_subtype_le L₀, ?_⟩⟩
    rwa [show (L₀.map (centralizer ({t} : Set G)).subtype).subgroupOf
      (centralizer ({t} : Set G)) = L₀ from
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) L₀]
  obtain ⟨⟨⟨a, J⟩, ha, hJa, hJcomp⟩, hmax⟩ :=
    Finite.exists_max (fun p : P => (CFSG.Open.fusionZStar p.1.2).index)
  have hbound : ∀ b : G, orderOf b = 2 → ∀ L : Subgroup G, L ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))) →
        (CFSG.Open.fusionZStar L).index ≤ (CFSG.Open.fusionZStar J).index :=
    fun b hb L hLb hL => hmax ⟨(b, L), hb, hLb, hL⟩
  have hvert : ∀ (a' : G) (L₁ : Subgroup G) (b' : G) (L₂ : Subgroup G), GSCorr a' L₁ b' L₂ →
      GSGrammar.InvolutionComponent (fun J K => IsPComponent 2 (J.subgroupOf K)) L₂ :=
    fun _ _ _ _ h => (gsCorr_iff_grammar.1 h).involutionComponent_right
  have hcmp : ∀ {a' b' : G} {L₁ L₂ : Subgroup G}, GSCorr a' L₁ b' L₂ →
      (CFSG.Open.fusionZStar L₁).index ≤ (CFSG.Open.fusionZStar L₂).index ∧
      ((CFSG.Open.fusionZStar L₁).index = (CFSG.Open.fusionZStar L₂).index →
        Nonempty (L₁ ⧸ CFSG.Open.fusionZStar L₁ ≃* L₂ ⧸ CFSG.Open.fusionZStar L₂)) := by
    intro a' b' L₁ L₂ h
    obtain ⟨ha', hb', -, hL₁a, hL₁comp, hL₂b, hL₂comp, -⟩ := id h
    obtain ⟨-, -, -, -, -, -, hle, heq⟩ := ordinary_local_correspondence_simple_quotient_comparison
      h (pComponent_vertex hB ha' hL₁a hL₁comp).1 (pComponent_vertex hB hb' hL₂b hL₂comp).1
    exact ⟨hle, heq⟩
  have hJmax : UnbalancedCorr.GSMaximalComponent J :=
    UnbalancedCorr.gsMaximalComponent_iff_grammar.2 <|
      GSGrammar.maximalComponent_of_le (fun L => (CFSG.Open.fusionZStar L).index)
        (fun _ _ _ _ h => (hcmp h).1) (fun _ _ _ _ h => (hcmp h).2) ⟨a, ha, hJa, hJcomp⟩
        fun L hL => by
          obtain ⟨b, hb, hLb, hLcomp⟩ := hL.vertex_right hvert
          exact hbound b hb L hLb hLcomp
  refine ⟨a, ha, J, hJa, hJcomp, isComponentOf_of_pComponent hB ha hJa hJcomp,
    UnbalancedCorr.fusionMaximalComponent_iff.2 hJmax, hbound, fun L hL => ?_⟩
  have hL' := UnbalancedCorr.fusionReach_iff_gsReach.1 hL
  obtain ⟨e⟩ := hJmax.2 L hL'
  obtain ⟨b, hb, hLb, hLcomp⟩ := (UnbalancedCorr.gsReach_iff_grammar.1 hL').vertex_right hvert
  obtain ⟨hJq, -, hZJ⟩ := pComponent_vertex hB ha hJa hJcomp
  obtain ⟨hLq, -, hZL⟩ := pComponent_vertex hB hb hLb hLcomp
  exact ⟨hLq, hZL, ⟨(QuotientGroup.quotientMulEquivOfEq hZL).symm.trans
    (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hZJ))⟩⟩

end CFSG.ComponentClassification.UnbalancingLocal
