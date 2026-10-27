module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBDichotomy
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem original_maximal_triple_critical_standard_dichotomy_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hCTI : LayerGeneratedUniversalComponentStandard)
    [IsSimpleGroup G] (hnonab : ∃ x y : G, x * y ≠ y * x)
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} (ha : orderOf a = 2) {J : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    {S P : Subgroup G} (hSX : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
    (hSsyl : ∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)))
    (hP : P = S ⊓ UnbalancedLayer.coreActionKernel J)
    (H R T X E V : Subgroup G → Subgroup G) (hH : ∀ B, H B = normalizer (B : Set G))
    (hR : ∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype)
    (hT : ∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype)
    (hX : ∀ B, X B = T B ⊔ R B) (hE : ∀ B, E B = (pLayer ↥(H B) 2).map (H B).subtype)
    (hV : ∀ B, V B = ⨆ e ∈ E B, conjugate (T B) e) (d : Subgroup G → ℕ)
    (hd : ∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W)))
    {x : G} (hmax : GSMaximalUnbalancingTriple a x J)
    (hiso : GSIsoAt a J)
    (htype : 2 ≤ pRank 2 ↥J ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) :
    (∀ b : G, orderOf b = 2 → b ∈ P → ∃ M : Subgroup G, UnbalancedGS.GSIsoCorr a J b M) ∨
    (GSUnbalancingTriple a x J ∧
    ∃ B : Subgroup G, B ≠ ⊥ ∧ B ≤ P ∧ ∃ haH : a ∈ H B,
      let θ := QuotientGroup.mk' (criticalOddTwoCore ↥(H B))
      let ā := θ ⟨a, haH⟩
      let L := ((T B).subgroupOf (H B)).map θ
      let W := ((V B).subgroupOf (H B)).map θ
      ((criticalOddTwoCore ↥(H B)).map (H B).subtype = R B ⊔ B ∧ R B ⊓ B = ⊥ ∧
        ⁅R B, B⁆ = ⊥ ∧ orderOf ā = 2 ∧ V B = E B ∧ ⁅V B, zpowers a⁆ = V B ∧
        B ≤ H B ⊓ UnbalancedLayer.coreActionKernel (V B) ∧
        (∃ P₀ : Sylow 2 ↥(H B ⊓ UnbalancedLayer.coreActionKernel (V B)),
          (P₀ : Subgroup _) = B.subgroupOf (H B ⊓ UnbalancedLayer.coreActionKernel (V B))) ∧
        S ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (B : Set G) ⊓ normalizer (X B : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (B : Set G)).subgroupOf
            (normalizer (B : Set G) ⊓ normalizer (X B : Set G))) ∧
      (L ≤ centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
        IsComponent (L.subgroupOf (centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) ∧
        2 ≤ pRank 2 ↥L ∧ IsStandardSubgroup L) ∧
      ((∃ e : ↥L ⧸ center ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
          ∀ (x : ↥((T B).subgroupOf (H B))) (hx : ((x : ↥(H B)) : G) ∈ J),
            e ((θ.subgroupMap ((T B).subgroupOf (H B)) x : ↥L) : ↥L ⧸ center ↥L) =
              ((⟨_, hx⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J)) ∧
        (⨆ e ∈ layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), conjugate L e) = W ∧
        ⁅W, zpowers ā⁆ = W ∧
        V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype =
          (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype) ∧
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
        (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
          Nat.card ↥(S ⊓ normalizer (B : Set G)) < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
        V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
          (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
          T C = UnbalancedGS.gsFixedLayer (V C) a) ∧
      ∀ (Y : Type) [Group Y], Nonempty (↥J ⧸ CFSG.Open.fusionZStar ↥J ≃* Y) →
        Nonempty (↥L ⧸ center ↥L ≃* Y)) := by
  classical
  by_cases hall : ∀ b : G, orderOf b = 2 → b ∈ P → ∃ M : Subgroup G, UnbalancedGS.GSIsoCorr a J b M
  · exact Or.inl hall
  right
  have hb : ∃ b : G, orderOf b = 2 ∧ b ∈ P ∧
      ∀ M : Subgroup G, ¬ UnbalancedGS.GSIsoCorr a J b M := by
    push Not at hall
    obtain ⟨b, hb, hbP, hbM⟩ := hall
    exact ⟨b, hb, hbP, hbM⟩
  have hJ2 : 2 ≤ pRank 2 ↥J := by
    rcases htype with h2 | hsmall
    · exact h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let e : J ⧸ oddCore J ≃* J ⧸ pPrimeCore 2 J :=
      QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two J)
    have hq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
      CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJa)
        (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJ)
    have hA : IsQuasisimple (J ⧸ oddCore J) := LocalCores.isQuasisimple_of_mulEquiv e.symm hq
    refine UnbalancedGS.small_source_models_force_rank_at_least_two hA ?_
    rcases hsmall with ⟨p, f, hp, hp2, hf, hm⟩ | h7 | h34
    · exact Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf,
        SectionRank.statedClassicalModel_of_mulEquiv e hm⟩
    · obtain ⟨e7⟩ := h7
      exact Or.inr (Or.inl ⟨e.trans e7⟩)
    · exact Or.inr (Or.inr h34)
  have hz : ∀ z : G, orderOf z = 2 → z ∈ P → z ∈ centralizer (S : Set G) →
      ∃ P₀ : Sylow 2 ↥(centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)),
        (P₀ : Subgroup _) =
          S.subgroupOf (centralizer ({z} : Set G) ⊓ normalizer (X (zpowers z) : Set G)) := by
    intro z hz hzP hzS
    rw [hP] at hzP
    have hXz : X (zpowers z) =
        (pLayer ↥(J ⊓ centralizer ((zpowers z : Subgroup G) : Set G)) 2).map
          (J ⊓ centralizer ((zpowers z : Subgroup G) : Set G)).subtype ⊔
        (pPrimeCore 2 ↥(normalizer ((zpowers z : Subgroup G) : Set G))).map
          (normalizer ((zpowers z : Subgroup G) : Set G)).subtype := by
      rw [hX, hT, hR, hH]
    exact (sylow_fixed_core_of_central hmax hiso hSX hSsyl hz (mem_inf.mp hzP).1
      (mem_inf.mp hzP).2 (fun s hs => (mem_centralizer_iff.mp hzS s hs)) _ hXz).2
  obtain ⟨B, hB, hBP, haH, h1, h2, ⟨⟨e, he⟩, h3⟩, h4⟩ :=
    critical_local_quotient_standard_component_producer_of_inputs hS hU hheld hCTI hnonab hK ha
      hJa hJ hSX hSsyl hP H R T X E V hH hR hT hX hE hV d hd hz hb hJ2
  exact ⟨hmax.1, B, hB, hBP, haH, h1, h2, ⟨⟨e, he⟩, h3⟩, h4,
    fun Y _ ⟨φ⟩ => ⟨e.trans φ⟩⟩

end CFSG.ComponentClassification.GSThmB
