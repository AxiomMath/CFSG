module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelCases
public import CFSG.LieType.Simplicity.Basic
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCritical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelQuotient
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrMaximalTriple

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open CFSG.ComponentClassification.UnbalancedLayer (GSUnbalancingTriple)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def OriginalCriticalStandardDichotomy : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    Assembly.KProper Blueprint.Catalog G → ∀ {a : G}, orderOf a = 2 → ∀ {J : Subgroup G},
    J ≤ centralizer ({a} : Set G) → IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) →
    ∀ {S P : Subgroup G}, S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
    (∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
      (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
    P = S ⊓ UnbalancedLayer.coreActionKernel J →
    ∀ (H R T X E V : Subgroup G → Subgroup G), (∀ B, H B = normalizer (B : Set G)) →
    (∀ B, R B = (pPrimeCore 2 ↥(H B)).map (H B).subtype) →
    (∀ B, T B = (pLayer ↥(J ⊓ centralizer (B : Set G)) 2).map
      (J ⊓ centralizer (B : Set G)).subtype) →
    (∀ B, X B = T B ⊔ R B) → (∀ B, E B = (pLayer ↥(H B) 2).map (H B).subtype) →
    (∀ B, V B = ⨆ e ∈ E B, conjugate (T B) e) → ∀ (d : Subgroup G → ℕ),
    (∀ W : Subgroup G,
      d W = Nat.card ((↥W ⧸ pPrimeCore 2 ↥W) ⧸ center (↥W ⧸ pPrimeCore 2 ↥W))) →
    ∀ {x : G}, GSMaximalUnbalancingTriple a x J →
    (∀ (u v : G) (K : Subgroup G), GSUnbalancingTriple u v K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) →
    (2 ≤ pRank 2 ↥J ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) →
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
        Nonempty (↥L ⧸ center ↥L ≃* Y))

omit [Finite G] in
theorem fusionZStar_eq_pPrimeCore_of_isSimpleGroup {Y : Type*} [Group Y]
    (hs : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y)) (hna : ∃ u v : Y ⧸ pPrimeCore 2 Y, u * v ≠ v * u) :
    CFSG.Open.fusionZStar Y = pPrimeCore 2 Y := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore Y
  have hc : center (Y ⧸ pPrimeCore 2 Y) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ pPrimeCore 2 Y)) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hna
      have hu : u ∈ center (Y ⧸ pPrimeCore 2 Y) := by rw [h]; exact mem_top u
      exact huv (mem_center_iff.mp hu v).symm
  let e : Y ⧸ CFSG.Open.fusionOddCore Y ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.quotientMulEquivOfEq hO
  ext x
  constructor
  · intro hx
    have h1 : QuotientGroup.mk' (CFSG.Open.fusionOddCore Y) x ∈
        center (Y ⧸ CFSG.Open.fusionOddCore Y) := hx
    have h2 : e (QuotientGroup.mk' _ x) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, mem_center_iff.mp h1 g']
    rw [hc, mem_bot] at h2
    have h3 : (x : Y ⧸ pPrimeCore 2 Y) = 1 := by
      rw [← h2]
      exact (QuotientGroup.quotientMulEquivOfEq_mk hO x).symm
    exact (QuotientGroup.eq_one_iff x).mp h3
  · intro hx
    have h1 : x ∈ CFSG.Open.fusionOddCore Y := by rw [hO]; exact hx
    show QuotientGroup.mk' (CFSG.Open.fusionOddCore Y) x ∈ center _
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr h1]
    exact one_mem _

omit [Finite G] in
theorem isSimpleGroup_of_statedClassicalModel_psl_two {Y : Type} [Group Y] {p f : ℕ}
    (hm : StatedClassicalModel Y .PSL 2 p f) : IsSimpleGroup Y :=
  CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hm

theorem original_critical_full_kernel_simple_or_diagonal_normal_closure_of_inputs
    (hS : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hDich : OriginalCriticalStandardDichotomy)
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
    (hbound : ∀ (u v : G) (K : Subgroup G), GSUnbalancingTriple u v K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index)
    (htype : 2 ≤ pRank 2 ↥J ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2)
    {b : G} (hb : orderOf b = 2) (hbP : b ∈ P)
    (hbM : ∀ M : Subgroup G, ¬ UnbalancedGS.GSIsoCorr a J b M) :
    ∃ B : Subgroup G, B ≠ ⊥ ∧ B ≤ P ∧ ∃ haH : a ∈ H B,
      let θ := QuotientGroup.mk' (criticalOddTwoCore ↥(H B))
      let ā := θ ⟨a, haH⟩
      let L := ((T B).subgroupOf (H B)).map θ
      let W := ((V B).subgroupOf (H B)).map θ
      let D := H B ⊓ UnbalancedLayer.coreActionKernel (V B)
      let ρ := QuotientGroup.mk' (pLayerCoreActionKernel ↥(H B))
      (H B < ⊤ ∧ SectionRank.IsKGroupCat ↥(H B) ∧
        SectionRank.IsKGroupCat (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∧
        (criticalOddTwoCore ↥(H B)).map (H B).subtype = R B ⊔ B ∧ R B ⊓ B = ⊥ ∧
        ⁅R B, B⁆ = ⊥ ∧ V B = E B ∧ ⁅V B, zpowers a⁆ = V B ∧
        (pLayerCoreActionKernel ↥(H B)).map (H B).subtype = D ∧ (D.subgroupOf (H B)).Normal ∧
        Group.IsSolvable ↥D ∧ (criticalOddTwoCore ↥(H B)).map (H B).subtype ≤ D ∧ B ≤ D ∧
        (∃ P₀ : Sylow 2 ↥D, (P₀ : Subgroup ↥D) = B.subgroupOf D) ∧
        S ⊓ normalizer (B : Set G) ≤ normalizer (B : Set G) ⊓ normalizer (X B : Set G) ∧
        ∃ P₀ : Sylow 2 ↥(normalizer (B : Set G) ⊓ normalizer (X B : Set G)),
          (P₀ : Subgroup _) = (S ⊓ normalizer (B : Set G)).subgroupOf
            (normalizer (B : Set G) ⊓ normalizer (X B : Set G))) ∧
      (orderOf ā = 2 ∧ L ≤ centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
        IsComponent (L.subgroupOf (centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) ∧
        2 ≤ pRank 2 ↥L ∧ IsStandardSubgroup L) ∧
      (V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype =
          (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype ∧
        V B ⊓ D = (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype ∧
        (∃ e : ↥L ⧸ center ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
          ∀ (y : ↥((T B).subgroupOf (H B))) (hy : ((y : ↥(H B)) : G) ∈ J),
            e ((θ.subgroupMap ((T B).subgroupOf (H B)) y : ↥L) : ↥L ⧸ center ↥L) =
              ((⟨_, hy⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J)) ∧
        pPrimeCore 2 (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) =
          centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
        centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) =
          (pLayerCoreActionKernel ↥(H B)).map θ ∧
        layer (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = W ∧
        (⨆ f : ↥(H B) ⧸ criticalOddTwoCore ↥(H B), conjugate L f) = W ∧ ⁅W, zpowers ā⁆ = W ∧
        pCore 2 (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = ⊥ ∧
        (∃ (ι : Type) (_ : Finite ι) (Sf : ι → Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B))),
          (Nat.card ι = 1 ∨ Nat.card ι = 2) ∧ (∀ i, IsSimpleGroup ↥(Sf i)) ∧
          (∀ i, ∃ u w : ↥(Sf i), u * w ≠ w * u) ∧
          (Pairwise fun i j => ∀ u w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B), u ∈ Sf i → w ∈ Sf j →
            Commute u w) ∧ iSupIndep Sf ∧ ⨆ i, Sf i = W) ∧
        ∀ h : ↥(H B), (∀ w ∈ W, θ h * w * (θ h)⁻¹ = w) ↔ (h : G) ∈ D) ∧
      (∃ η : (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) →* (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)),
        (∀ h : ↥(H B), η (θ h) = ρ h) ∧
        η.ker = pPrimeCore 2 (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∧
        (∃ e : ↥W ≃* ↥(W.map η), ∀ w : ↥W,
          (e w : ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = η w) ∧
        (∃ e : ↥L ≃* ↥(L.map η), ∀ y : ↥L,
          (e y : ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = η y) ∧
        SectionRank.IsKGroupCat (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) ∧
        centralizer ((W.map η : Subgroup _) : Set (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B))) = ⊥ ∧
        layer (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = W.map η ∧
        generalizedFitting (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = W.map η ∧
        fittingSubgroup (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = ⊥ ∧
        pPrimeCore 2 (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = ⊥ ∧
        pCore 2 (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = ⊥ ∧
        (⨆ g : ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B), conjugate (L.map η) g) = W.map η ∧
        ⁅W.map η, zpowers (ρ ⟨a, haH⟩)⁆ = W.map η ∧ orderOf (ρ ⟨a, haH⟩) = 2 ∧
        IsStandardSubgroup (L.map η) ∧
        centralizer ({ρ ⟨a, haH⟩} : Set (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B))) =
          (centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B)))).map η ∧
        L.map η ≤ centralizer ({ρ ⟨a, haH⟩} : Set (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B))) ∧
        IsComponent ((L.map η).subgroupOf
          (centralizer ({ρ ⟨a, haH⟩} : Set (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B))))) ∧
        (∃ e : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B) ≃* ↥W,
          ∀ (v : ↥(V B)) (hv : (v : G) ∈ H B),
            (e (v : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B)) :
              ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = θ ⟨v, hv⟩) ∧
        (∃ e : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B) ≃* ↥(W.map η),
          ∀ (v : ↥(V B)) (hv : (v : G) ∈ H B),
            (e (v : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B)) :
              ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = ρ ⟨v, hv⟩) ∧
        Xor
          (IsSimpleGroup ↥W ∧ (∃ u w : ↥W, u * w ≠ w * u) ∧ Blueprint.Catalog ↥W ∧ L < W ∧
            (∃ w ∈ W, ā * w * ā⁻¹ ≠ w) ∧
            ∃ ι : (↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) →* MulAut ↥W,
              Function.Injective ι ∧
              (∀ (h : ↥(H B)) (w : ↥W),
                ((ι (ρ h) w : ↥W) : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) =
                  θ h * w * (θ h)⁻¹) ∧
              ∀ w₀ : ↥W, ∃ g : ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B),
                ∀ w : ↥W, ι g w = w₀ * w * w₀⁻¹)
          (∃ K₁ : Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B)), IsComponent K₁ ∧
            conjugate K₁ ā ≠ K₁ ∧ K₁ ⊔ conjugate K₁ ā = W ∧ K₁ ⊓ conjugate K₁ ā = ⊥ ∧
            (∀ u ∈ K₁, ∀ w ∈ conjugate K₁ ā, u * w = w * u) ∧
            (L : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) =
              {g | ∃ k ∈ K₁, k * (ā⁻¹ * k * ā) = g} ∧
            L = W ⊓ centralizer ({ā} : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ∧
            ∃ δ : ↥K₁ ≃* ↥L, (∀ k : ↥K₁,
              (δ k : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = k * (ā⁻¹ * k * ā)) ∧
            ∃ ψ : ↥W ≃* ↥L × ↥L,
              (∀ (k l : ↥K₁) (hw : (k : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) *
                  (ā⁻¹ * l * ā) ∈ W), ψ ⟨_, hw⟩ = (δ k, δ l)) ∧
              (∀ (j : ↥L) (hj : (j : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∈ W),
                ψ ⟨j, hj⟩ = (j, j)) ∧
              (∀ (w : ↥W) (hw : ā⁻¹ * (w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) * ā ∈ W),
                ψ ⟨_, hw⟩ = (ψ w).swap) ∧
              IsSimpleGroup ↥L ∧
              ∃ χ : ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J,
                (∀ (y : ↥((T B).subgroupOf (H B))) (hy : ((y : ↥(H B)) : G) ∈ J),
                  χ (θ.subgroupMap ((T B).subgroupOf (H B)) y) =
                    ((⟨_, hy⟩ : J) : J ⧸ CFSG.Open.fusionZStar ↥J)) ∧
                (∀ (j : ↥L) (hj : (j : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∈ W),
                  (ψ.trans (MulEquiv.prodCongr χ χ)) ⟨j, hj⟩ = (χ j, χ j)) ∧
                (∀ (w : ↥W) (hw : ā⁻¹ * (w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) * ā ∈ W),
                  (ψ.trans (MulEquiv.prodCongr χ χ)) ⟨_, hw⟩ =
                    ((ψ.trans (MulEquiv.prodCongr χ χ)) w).swap) ∧
                (∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
                  StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f →
                  StatedClassicalModel ↥K₁ .PSL 2 p f ∧
                    StatedClassicalModel ↥(conjugate K₁ ā) .PSL 2 p f) ∧
                (Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) →
                  Nonempty (↥K₁ ≃* alternatingGroup (Fin 7)) ∧
                    Nonempty (↥(conjugate K₁ ā) ≃* alternatingGroup (Fin 7))) ∧
                (StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 →
                  StatedClassicalModel ↥K₁ .PSL 3 2 2 ∧
                    StatedClassicalModel ↥(conjugate K₁ ā) .PSL 3 2 2) ∧
                ∀ (Y : Type) [Group Y] (φ : ↥J ⧸ CFSG.Open.fusionZStar ↥J ≃* Y),
                  ∃ Ψ : ↥W ≃* Y × Y,
                    (∀ (j : ↥L) (hj : (j : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∈ W),
                      Ψ ⟨j, hj⟩ = (φ (χ j), φ (χ j))) ∧
                    ∀ (w : ↥W) (hw : ā⁻¹ * (w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) * ā ∈ W),
                      Ψ ⟨_, hw⟩ = (Ψ w).swap)) ∧
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ P →
        (Nat.card B < Nat.card C ∨ (Nat.card B = Nat.card C ∧
          Nat.card ↥(S ⊓ normalizer (B : Set G)) < Nat.card ↥(S ⊓ normalizer (C : Set G)))) →
        V C ≤ H C ∧ IsPComponent 2 ((V C).subgroupOf (H C)) ∧ conjugate (V C) a = V C ∧
          (T C : Set G) * ((pPrimeCore 2 ↥(V C)).map (V C).subtype : Set G) = V C ∧
          T C = UnbalancedGS.gsFixedLayer (V C) a) ∧
      GSUnbalancingTriple a x J ∧ ∀ M : Subgroup G, ¬ UnbalancedGS.GSIsoCorr a J b M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hDich hnonab hK ha hJa hJ hSX hSsyl hP H R T X E V hH hR hT hX hE hV d hd hmax hbound
    htype with hall | ⟨hxJ, B, hB1, hBP, haH, hD1, hD2, hD3, hD4, -⟩
  · obtain ⟨M, hM⟩ := hall b hb hbP
    exact absurd hM (hbM M)
  refine ⟨B, hB1, hBP, haH, ?_⟩
  intro θ ā L W D ρ
  obtain ⟨hNeq, hRBbot, hRBc, hā2, hVEeq, hVa, hBD, hBsylD, hQL, hQsyl⟩ := hD1
  obtain ⟨hLC, hLcomp, hL2, hLstd⟩ := hD2
  obtain ⟨⟨eLJ, heLJ⟩, hncl, hWa, hVN⟩ := hD3
  have hS2 : IsPGroup 2 S := by
    obtain ⟨P₀, hP₀⟩ := hSsyl
    have h1 : IsPGroup 2 (S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) :=
      hP₀ ▸ P₀.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hSX)
  have hA2 := actual_two_local_fixed_layer_orbits_of_inputs hS hU hheld hnonab hK ha hJa hJ hSX
    hSsyl hP H R T X E V hH hR hT hX hE hV d hd
  obtain ⟨⟨hHtop, hKH⟩, -, -, -, hTaH, hpcT, -, ⟨M, hMH, hM, hMa, hVM, hVE, -, -⟩, -, -, -,
    -⟩ := hA2.1 B hB1 hBP
  have hBP' : B ≤ S ⊓ UnbalancedLayer.coreActionKernel J := hBP.trans hP.le
  have hHB : H B = normalizer (B : Set G) := hH B
  have hBH : B ≤ H B := hHB ▸ le_normalizer
  have hEB : E B = (pLayer ↥(H B) 2).map (H B).subtype := hE B
  have hVE' : V B ≤ (pLayer ↥(H B) 2).map (H B).subtype := hEB ▸ hVE
  have hVH : V B ≤ H B := hVE'.trans (map_subtype_le _)
  have hMaH : conjugate M a ≤ H B := by
    have h1 := hVH
    rw [hVM] at h1
    exact le_sup_right.trans h1
  have hRBH : R B ≤ H B := by rw [hR B]; exact map_subtype_le _
  have hHR : H B ≤ normalizer (R B : Set G) := by
    rw [hR B]
    exact nested_le_normalizer_map_pPrimeCore (H B)
  have hTH : T B ≤ H B := hTaH.trans inf_le_left
  have hBn : (B.subgroupOf (H B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr hHB.le
  have hB2 : IsPGroup 2 B := hS2.to_le (hBP'.trans inf_le_left)
  have hB2' : IsPGroup 2 (B.subgroupOf (H B)) :=
    hB2.comap_of_injective (H B).subtype (H B).subtype_injective
  have hθker : θ.ker = pPrimeCore 2 ↥(H B) ⊔ B.subgroupOf (H B) := by
    rw [QuotientGroup.ker_mk']
    apply map_injective (H B).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBH, hNeq, hR B]
  have hHV : H B ≤ normalizer (V B : Set G) := by
    rw [hVEeq, hEB]
    have : (pLayer ↥(H B) 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
    intro h hh
    exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (H B) (pLayer ↥(H B) 2)
      (le_normalizer hh)
  have hV'n : ((V B).subgroupOf (H B)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVH).mpr hHV
  have hWn : W.Normal := hV'n.map θ (QuotientGroup.mk'_surjective _)
  have hTV : T B ≤ V B := by
    have hRf : R B = (pPrimeCore 2 ↥(normalizer (B : Set G))).map
        (normalizer (B : Set G)).subtype := by rw [hR, hH]
    obtain ⟨-, -, h, -, -, -⟩ := two_local_conj_facts hS hU hheld hnonab hK ha hJa hJ hSX hS2
      hB1 hBP' (hT B) hRf (hX B) (by rw [hE, hH]) (hV B)
    exact h
  have hLW : L ≤ W := map_mono (fun x hx => hTV hx)
  have hLq : IsQuasisimple ↥L := LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLC)
    hLcomp.1
  have hW1 : W ≠ ⊥ := fun h => (nontrivial_iff_ne_bot L).mp
    (LocalCores.isQuasisimple_nontrivial hLq) (le_bot_iff.mp (h ▸ hLW))
  have hMperf : ⁅M, M⁆ = M := commutator_eq_of_isPComponent hMH hM
  have hVperf : ⁅V B, V B⁆ = V B := by
    have h2 : ⁅conjugate M a, conjugate M a⁆ = conjugate M a := by
      unfold conjugate
      rw [← map_commutator, hMperf]
    rw [hVM]
    apply le_antisymm (commutator_le_self _)
    refine sup_le ?_ ?_
    · calc M = ⁅M, M⁆ := hMperf.symm
        _ ≤ ⁅M ⊔ conjugate M a, M ⊔ conjugate M a⁆ := commutator_mono le_sup_left le_sup_left
    · calc conjugate M a = ⁅conjugate M a, conjugate M a⁆ := h2.symm
        _ ≤ ⁅M ⊔ conjugate M a, M ⊔ conjugate M a⁆ :=
          commutator_mono le_sup_right le_sup_right
  have hOV : (pPrimeCore 2 ↥(V B)).map (V B).subtype = V B ⊓ R B := by
    rw [hR B]
    exact map_pPrimeCore_eq_inf_of_subgroupOf hVH hV'n.isSubnormal
  have hRN : R B ≤ (criticalOddTwoCore ↥(H B)).map (H B).subtype := hNeq ▸ le_sup_left
  have hON : (pPrimeCore 2 ↥(V B)).map (V B).subtype ≤
      (criticalOddTwoCore ↥(H B)).map (H B).subtype := hOV ▸ inf_le_right.trans hRN
  have hDk : pLayerCoreActionKernel ↥(H B) = D.subgroupOf (H B) := by
    have h1 : (V B).subgroupOf (H B) = pLayer ↥(H B) 2 := by
      rw [hVEeq, hEB]
      exact comap_map_eq_self_of_injective (H B).subtype_injective _
    ext h
    rw [pLayerCoreActionKernel, ← h1, mem_coreActionKernel_subgroupOf_iff hVH, mem_subgroupOf]
    exact ⟨fun hh => mem_inf.mpr ⟨h.2, hh⟩, fun hh => (mem_inf.mp hh).2⟩
  have hDH : D ≤ H B := inf_le_left
  have hDmap : (pLayerCoreActionKernel ↥(H B)).map (H B).subtype = D := by
    rw [hDk]
    exact map_subgroupOf_eq_of_le hDH
  have hDn : (D.subgroupOf (H B)).Normal := hDk ▸ inferInstance
  have hRD : R B ≤ D := by
    intro r hr
    refine mem_inf.mpr ⟨hRBH hr, UnbalancedLayer.mem_coreActionKernel.mpr
      ⟨hHV (hRBH hr), fun v hv => ?_⟩⟩
    rw [hOV]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem (hHV (hRBH hr))) v).mp hv
      rw [inv_inv] at h1
      rw [show v⁻¹ * r⁻¹ * v * r = v⁻¹ * (r⁻¹ * v * r) by group]
      exact mul_mem (inv_mem hv) h1
    · have h1 := (mem_normalizer_iff.mp (inv_mem (hHR (hVH hv))) r⁻¹).mp (inv_mem hr)
      rw [inv_inv] at h1
      exact mul_mem h1 hr
  have hND : (criticalOddTwoCore ↥(H B)).map (H B).subtype ≤ D := by
    rw [hNeq]
    exact sup_le hRD hBD
  have hDsolv : Group.IsSolvable ↥D := by
    obtain ⟨P₀, hP₀⟩ := hBsylD
    have hBD' : B ≤ D := hBD
    have hBDn : (B.subgroupOf D).Normal :=
      (normal_subgroupOf_iff_le_normalizer hBD').mpr (hDH.trans hHB.le)
    have hodd : Odd (Nat.card (↥D ⧸ B.subgroupOf D)) := by
      rw [← Subgroup.index_eq_card, ← hP₀]
      exact Nat.not_even_iff_odd.mp fun he => P₀.not_dvd_index (even_iff_two_dvd.mp he)
    have : Group.IsSolvable ↥(B.subgroupOf D) := by
      have h1 : IsPGroup 2 (B.subgroupOf D) :=
        hB2.comap_of_injective D.subtype D.subtype_injective
      have : Group.IsNilpotent ↥(B.subgroupOf D) := h1.isNilpotent
      infer_instance
    have : Group.IsSolvable (↥D ⧸ B.subgroupOf D) := Milestones.odd_order_solvable hodd
    exact Group.isSolvable_of_subgroup_quotient (B.subgroupOf D)
  have hVD : V B ⊓ D = (CFSG.Open.fusionZStar ↥(V B)).map (V B).subtype := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvV, hvD⟩ := mem_inf.mp hv
      exact ⟨⟨v, hvV⟩, (mem_coreActionKernel_iff_mem_fusionZStar ⟨v, hvV⟩).mp
        (mem_inf.mp hvD).2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact mem_inf.mpr ⟨w.2, mem_inf.mpr ⟨hVH w.2,
        (mem_coreActionKernel_iff_mem_fusionZStar w).mpr hw⟩⟩
  have hcentW : ∀ h : ↥(H B), θ h ∈ centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) ↔
      (h : G) ∈ UnbalancedLayer.coreActionKernel (V B) :=
    fun h => mem_centralizer_map_iff hVH hHV hVperf hON hVN h
  have hCW : centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) =
      (pLayerCoreActionKernel ↥(H B)).map θ := by
    ext f
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (criticalOddTwoCore ↥(H B)) f
    constructor
    · intro hf
      have h1 := (hcentW h).mp hf
      refine ⟨h, ?_, rfl⟩
      show h ∈ pLayerCoreActionKernel ↥(H B)
      rw [hDk, mem_subgroupOf]
      exact mem_inf.mpr ⟨h.2, h1⟩
    · rintro ⟨d', hd', hdh⟩
      have hd'' : d' ∈ pLayerCoreActionKernel ↥(H B) := hd'
      rw [hDk, mem_subgroupOf] at hd''
      have h1 := (hcentW d').mpr (mem_inf.mp hd'').2
      rw [← hdh]
      exact h1
  have hCodd : Odd (Nat.card (centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))))) := by
    have hφ : (θ.comp (inclusion hDH)).range = (pLayerCoreActionKernel ↥(H B)).map θ := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range, hDk]
    rw [hCW, ← hφ, ← Subgroup.index_ker]
    obtain ⟨P₀, hP₀⟩ := hBsylD
    have hBk : B.subgroupOf D ≤ (θ.comp (inclusion hDH)).ker := by
      intro y hy
      have hyN : (y : G) ∈ (criticalOddTwoCore ↥(H B)).map (H B).subtype := by
        rw [hNeq]
        exact mem_sup_right hy
      obtain ⟨z, hz, hzy⟩ := hyN
      have hz' : z = inclusion hDH y := Subtype.ext hzy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hz']
      exact (QuotientGroup.eq_one_iff z).mpr hz
    have h1 := Subgroup.index_dvd_of_le hBk
    have h2 : ¬ 2 ∣ (B.subgroupOf D).index := by
      rw [← hP₀]
      exact P₀.not_dvd_index
    exact Nat.not_even_iff_odd.mp fun he => h2 (dvd_trans (even_iff_two_dvd.mp he) h1)
  have hBbot : B.subgroupOf (H B) ≠ ⊥ := by
    intro h
    apply hB1
    have h1 := congrArg (Subgroup.map (H B).subtype) h
    rwa [map_subgroupOf_eq_of_le hBH, Subgroup.map_bot] at h1
  have hNBtop : normalizer ((B.subgroupOf (H B) : Subgroup (H B)) : Set (H B)) = ⊤ :=
    normalizer_eq_top_iff.mpr hBn
  have hcompθ : ∀ K : Subgroup G, K ≤ H B → IsPComponent 2 (K.subgroupOf (H B)) →
      IsComponent ((K.subgroupOf (H B)).map θ) := by
    intro K hKHB hKc
    have hKA : K.subgroupOf (H B) ≤ normalizer ((B.subgroupOf (H B) : Subgroup (H B)) :
        Set (H B)) := by
      rw [hNBtop]
      exact le_top
    have hKc' : IsPComponent 2 ((K.subgroupOf (H B)).subgroupOf
        (normalizer ((B.subgroupOf (H B) : Subgroup (H B)) : Set (H B)))) := by
      rw [hNBtop, ← subgroupOf_self (H B),
        isPComponent_subgroupOf_subgroupOf_iff' le_rfl 2 Nat.prime_two]
      exact hKc
    obtain ⟨-, -, -, -, -, -, -, hcomp, -⟩ :=
      kGroup_odd_times_two_normalizer_component_transport_of_inputs hS hU hheld hKH
        (B.subgroupOf (H B)) hB2' θ (QuotientGroup.mk'_surjective _) hθker
        (B.subgroupOf (H B)) hB2' hBbot le_rfl (K.subgroupOf (H B)) hKA hKc'
    have hBθ : (B.subgroupOf (H B)).map θ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hθker]
      exact le_sup_right
    rw [hBθ] at hcomp
    have htop : normalizer ((⊥ : Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :
        Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) = ⊤ :=
      normalizer_eq_top_iff.mpr inferInstance
    rw [htop] at hcomp
    have hq : IsQuasisimple ↥((K.subgroupOf (H B)).map θ) :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe le_top) hcomp.1
    obtain ⟨-, -, hs, -, -⟩ := id hKc
    exact ⟨hq, hs.map (QuotientGroup.mk'_surjective _)⟩
  have hS₁ := hcompθ M hMH hM
  have hS₂ := hcompθ _ hMaH hMa
  have hWsup : (M.subgroupOf (H B)).map θ ⊔ ((conjugate M a).subgroupOf (H B)).map θ = W := by
    show _ = ((V B).subgroupOf (H B)).map θ
    rw [hVM, subgroupOf_sup hMH hMaH, Subgroup.map_sup]
  have hZW : W ⊓ centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) = ⊥ :=
    map_inf_centralizer_eq_bot hVH hVperf hVN
  have hc12 : (M.subgroupOf (H B)).map θ = ((conjugate M a).subgroupOf (H B)).map θ ∨
      ∀ x ∈ (M.subgroupOf (H B)).map θ, ∀ y ∈ ((conjugate M a).subgroupOf (H B)).map θ,
        x * y = y * x := by
    rcases LocalCores.distinct_components_commute hS₁ hS₂ with h | h
    · exact Or.inl h
    · refine Or.inr fun x hx y hy => ?_
      have h1 := commutator_mem_commutator hx hy
      rw [h, mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
  obtain ⟨ι, hι, Sf, hcard, hSs, hSab, hScomm, hSind, hSW⟩ :=
    exists_simple_factors_of_sup hS₁.1 hS₂.1 hWsup hZW hc12
  have := hWn
  have hKeq : pPrimeCore 2 (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) =
      centralizer (W : Set (↥(H B) ⧸ criticalOddTwoCore ↥(H B))) :=
    (OutcomeLocal.odd_centralizer_semisimple_layer_faithful_standard_quotient Sf hSs hSab hScomm
      hSind hSW hW1 hCodd).1
  have hNDk : criticalOddTwoCore ↥(H B) ≤
      (pLayerCoreActionKernel ↥(H B)).comap (MonoidHom.id ↥(H B)) := by
    intro h hh
    show h ∈ pLayerCoreActionKernel ↥(H B)
    rw [hDk, mem_subgroupOf]
    exact hND ⟨h, hh, rfl⟩
  let η := QuotientGroup.map (criticalOddTwoCore ↥(H B)) (pLayerCoreActionKernel ↥(H B))
    (MonoidHom.id ↥(H B)) hNDk
  have hηθ : ∀ h : ↥(H B), η (θ h) = ρ h := fun h => rfl
  have hηs : Function.Surjective η := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pLayerCoreActionKernel ↥(H B)) q
    exact ⟨θ h, rfl⟩
  have hηker : η.ker = pPrimeCore 2 (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) := by
    rw [QuotientGroup.ker_map, Subgroup.comap_id, hKeq, hCW]
  obtain ⟨-, -, hlayerF, hLconj, hO2F, ⟨eW, heW⟩, ⟨eL, heL⟩, hCA, hlayerA, hgFitA, hfitA, hOA,
    hO2A, hA0, hWtA, hηt, hstdA, hCtA, hLtA, hcompA⟩ :=
    faithful_quotient_facts Sf hSs hSab hScomm hSind hSW hW1 hCodd η hηs hηker hLW hLstd hLC hā2
      hLcomp hncl hWa
  have hKF : SectionRank.IsKGroupCat (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) := hKH.quotient _
  have hVW : ∃ e : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B) ≃* ↥W,
      ∀ (v : ↥(V B)) (hv : (v : G) ∈ H B),
        (e (v : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B)) : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) =
          θ ⟨v, hv⟩ := by
    let f : ↥(V B) →* ↥W := (θ.comp (inclusion hVH)).codRestrict W
      (fun v => ⟨inclusion hVH v, v.2, rfl⟩)
    have hfs : Function.Surjective f := by
      rintro ⟨_, ⟨h, hh, rfl⟩⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    have hfk : f.ker = CFSG.Open.fusionZStar ↥(V B) := by
      ext v
      rw [MonoidHom.mem_ker]
      constructor
      · intro hv
        have h1 : θ (inclusion hVH v) = 1 := congrArg Subtype.val hv
        have h2 : inclusion hVH v ∈ criticalOddTwoCore ↥(H B) :=
          (QuotientGroup.eq_one_iff _).mp h1
        have h3 : (v : G) ∈ V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype :=
          mem_inf.mpr ⟨v.2, ⟨_, h2, rfl⟩⟩
        rw [hVN] at h3
        obtain ⟨w, hw, hwv⟩ := h3
        rwa [show w = v from Subtype.ext hwv] at hw
      · intro hv
        have h3 : (v : G) ∈ V B ⊓ (criticalOddTwoCore ↥(H B)).map (H B).subtype := by
          rw [hVN]
          exact ⟨v, hv, rfl⟩
        obtain ⟨n, hn, hnv⟩ := (mem_inf.mp h3).2
        have hn' : n = inclusion hVH v := Subtype.ext hnv
        apply Subtype.ext
        show θ (inclusion hVH v) = 1
        rw [← hn']
        exact (QuotientGroup.eq_one_iff n).mpr hn
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun v hv => rfl⟩
  have hVW₀ : ∃ e : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B) ≃* ↥(W.map η),
      ∀ (v : ↥(V B)) (hv : (v : G) ∈ H B),
        (e (v : ↥(V B) ⧸ CFSG.Open.fusionZStar ↥(V B)) :
          ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B)) = ρ ⟨v, hv⟩ := by
    let f : ↥(V B) →* ↥(W.map η) := (ρ.comp (inclusion hVH)).codRestrict (W.map η)
      (fun v => ⟨θ (inclusion hVH v), ⟨inclusion hVH v, v.2, rfl⟩, rfl⟩)
    have hfs : Function.Surjective f := by
      rintro ⟨_, ⟨_, ⟨h, hh, rfl⟩, rfl⟩⟩
      exact ⟨⟨h, hh⟩, rfl⟩
    have hfk : f.ker = CFSG.Open.fusionZStar ↥(V B) := by
      ext v
      rw [MonoidHom.mem_ker]
      constructor
      · intro hv
        have h1 : ρ (inclusion hVH v) = 1 := congrArg Subtype.val hv
        have h2 : inclusion hVH v ∈ pLayerCoreActionKernel ↥(H B) :=
          (QuotientGroup.eq_one_iff _).mp h1
        rw [hDk, mem_subgroupOf] at h2
        have h3 : (v : G) ∈ V B ⊓ D := mem_inf.mpr ⟨v.2, h2⟩
        rw [hVD] at h3
        obtain ⟨w, hw, hwv⟩ := h3
        rwa [show w = v from Subtype.ext hwv] at hw
      · intro hv
        have h3 : (v : G) ∈ V B ⊓ D := by
          rw [hVD]
          exact ⟨v, hv, rfl⟩
        apply Subtype.ext
        show ρ (inclusion hVH v) = 1
        apply (QuotientGroup.eq_one_iff _).mpr
        rw [hDk, mem_subgroupOf]
        exact (mem_inf.mp h3).2
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun v hv => rfl⟩
  have hαker : ∀ h : ↥(H B), (∀ w ∈ W, θ h * w * (θ h)⁻¹ = w) ↔ (h : G) ∈ D := by
    intro h
    rw [show (h : G) ∈ D ↔ (h : G) ∈ UnbalancedLayer.coreActionKernel (V B) from
      ⟨fun hh => (mem_inf.mp hh).2, fun hh => mem_inf.mpr ⟨h.2, hh⟩⟩, ← hcentW h,
      mem_centralizer_iff]
    constructor
    · intro hw w hwW
      have h1 := hw w hwW
      calc w * θ h = θ h * w * (θ h)⁻¹ * θ h := by rw [h1]
        _ = θ h * w := by group
    · intro hc w hwW
      rw [← hc w hwW, mul_inv_cancel_right]
  let α : ↥(H B) →* MulAut ↥W :=
    (MulAut.conjNormal : (↥(H B) ⧸ criticalOddTwoCore ↥(H B)) →* MulAut ↥W).comp θ
  have hαk : α.ker = pLayerCoreActionKernel ↥(H B) := by
    ext h
    rw [MonoidHom.mem_ker, hDk, mem_subgroupOf, ← hαker h]
    constructor
    · intro hf w hw
      have h1 := congrArg Subtype.val (MulEquiv.congr_fun hf ⟨w, hw⟩)
      rw [MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact h1
    · intro hf
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply]
      exact hf w w.2
  let ιA := QuotientGroup.lift (pLayerCoreActionKernel ↥(H B)) α hαk.ge
  have hιinj : Function.Injective ιA :=
    (QuotientGroup.injective_lift_iff _ α hαk.ge).mpr hαk.symm
  have hιρ : ∀ (h : ↥(H B)) (w : ↥W),
      ((ιA (ρ h) w : ↥W) : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = θ h * w * (θ h)⁻¹ :=
    fun h w => by
      show ((α h w : ↥W) : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) = _
      rw [MonoidHom.comp_apply, MulAut.conjNormal_apply]
  have hιinn : ∀ w₀ : ↥W, ∃ g : ↥(H B) ⧸ pLayerCoreActionKernel ↥(H B),
      ∀ w : ↥W, ιA g w = w₀ * w * w₀⁻¹ := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    refine ⟨ρ h, fun w => Subtype.ext ?_⟩
    rw [hιρ]
    rfl
  have hne : ∀ {K : Subgroup (↥(H B) ⧸ criticalOddTwoCore ↥(H B))}, IsComponent K → K ≠ ⊥ :=
    fun hK h => (nontrivial_iff_ne_bot _).mp (LocalCores.isQuasisimple_nontrivial hK.1) h
  refine ⟨⟨lt_top_iff_ne_top.mpr hHtop, hKH, hKF, hNeq, hRBbot, hRBc, hVEeq, hVa, hDmap, hDn,
      hDsolv, hND, hBD, hBsylD, hQL, hQsyl⟩,
    ⟨hā2, hLC, hLcomp, hL2, hLstd⟩,
    ⟨hVN, hVD, ⟨eLJ, heLJ⟩, hKeq, hCW, hlayerF, hLconj, hWa, hO2F,
      ⟨ι, hι, Sf, hcard, hSs, hSab, hScomm, hSind, hSW⟩, hαker⟩,
    ⟨η, hηθ, hηker, ⟨eW, heW⟩, ⟨eL, heL⟩, hKH.quotient _, hCA, hlayerA, hgFitA, hfitA, hOA,
      hO2A, hA0, hWtA, hηt, hstdA, hCtA, hLtA, hcompA, hVW, hVW₀, ?_⟩,
    hD4, hxJ, hbM⟩
  by_cases h12 : (M.subgroupOf (H B)).map θ = ((conjugate M a).subgroupOf (H B)).map θ
  ·
    have hWS : (M.subgroupOf (H B)).map θ = W := by rw [← hWsup, ← h12, sup_idem]
    have hWs : IsSimpleGroup ↥W := by
      rw [← hWS]
      exact isSimpleGroup_of_sup_centerless hS₁.1 hWsup hZW hc12
    have hWna : ∃ u w : ↥W, u * w ≠ w * u := by
      rw [← hWS]
      exact exists_ne_of_isQuasisimple hS₁.1
    obtain ⟨hcat, hLlt, hnontriv⟩ := simple_layer_facts hKF hWs hWa hLW hLC
    refine Or.inl ⟨⟨hWs, hWna, hcat, hLlt, hnontriv, ιA, hιinj, hιρ, hιinn⟩, ?_⟩
    rintro ⟨K₁, hK₁, -, hsup, hdisj, hcomm, -⟩
    have hK₂ : IsComponent (conjugate K₁ ā) :=
      LocalCores.isComponent_map_mulEquiv (MulAut.conj ā⁻¹) hK₁
    exact not_isSimpleGroup_of_prod hsup hdisj hcomm (hne hK₁) (hne hK₂) hWs
  ·
    have hcomm := hc12.resolve_left h12
    have hSd : (M.subgroupOf (H B)).map θ ⊓ ((conjugate M a).subgroupOf (H B)).map θ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
      have hxc : (⟨x, hx₁⟩ : ↥((M.subgroupOf (H B)).map θ)) ∈
          center ↥((M.subgroupOf (H B)).map θ) := mem_center_iff.mpr fun y =>
        Subtype.ext (hcomm y y.2 x hx₂)
      rw [center_eq_bot_of_sup_centerless hWsup hZW hc12, mem_bot] at hxc
      exact mem_bot.mpr (congrArg Subtype.val hxc)
    have hWns : ¬ IsSimpleGroup ↥W :=
      not_isSimpleGroup_of_prod hWsup hSd hcomm (hne hS₁) (hne hS₂)
    obtain ⟨K₁, hK₁, hsw, hsup, hdisj, hcomm', hLset, hLC', δ, hδ, ψ, hψa, hψb, hψc, hLs⟩ :=
      swapped_layer_facts hā2 hlayerF hZW hWsup hSd hcomm (hne hS₁) (hne hS₂) hLW hLC hLcomp
        hncl
    have hLcen : center ↥L = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥L) with h | h
      · exact h
      · exfalso
        obtain ⟨u, v, huv⟩ := exists_ne_of_isQuasisimple hLq
        have hu : u ∈ center ↥L := by rw [h]; exact mem_top u
        exact huv (mem_center_iff.mp hu v).symm
    let eZ : ↥L ≃* ↥L ⧸ center ↥L := MulEquiv.ofBijective (QuotientGroup.mk' (center ↥L))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk']; exact hLcen),
        QuotientGroup.mk'_surjective _⟩
    let χ : ↥L ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J := eZ.trans eLJ
    have hΨa : ∀ (j : ↥L) (hj : (j : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∈ W),
        (ψ.trans (MulEquiv.prodCongr χ χ)) ⟨j, hj⟩ = (χ j, χ j) := by
      intro j hj
      rw [MulEquiv.trans_apply, hψb j hj]
      rfl
    have hΨb : ∀ (w : ↥W) (hw : ā⁻¹ * (w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) * ā ∈ W),
        (ψ.trans (MulEquiv.prodCongr χ χ)) ⟨_, hw⟩ =
          ((ψ.trans (MulEquiv.prodCongr χ χ)) w).swap := by
      intro w hw
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψc w hw]
      rfl
    let eK : ↥K₁ ≃* ↥J ⧸ CFSG.Open.fusionZStar ↥J := δ.trans χ
    let eKa : ↥(conjugate K₁ ā) ≃* ↥K₁ :=
      (K₁.equivMapOfInjective (MulAut.conj ā⁻¹).toMonoidHom (MulAut.conj ā⁻¹).injective).symm
    have hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J) :=
      ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).mp hJ).2.2
    have hJna := exists_ne_of_isQuasisimple hJq
    have hm1 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
        StatedClassicalModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f →
        StatedClassicalModel ↥K₁ .PSL 2 p f ∧
          StatedClassicalModel ↥(conjugate K₁ ā) .PSL 2 p f := by
      intro p f _ _ _ hm
      have hZO := fusionZStar_eq_pPrimeCore_of_isSimpleGroup
        (isSimpleGroup_of_statedClassicalModel_psl_two hm) hJna
      let e' : ↥K₁ ≃* J ⧸ pPrimeCore 2 J := eK.trans (QuotientGroup.quotientMulEquivOfEq hZO)
      exact ⟨SectionRank.statedClassicalModel_of_mulEquiv e' hm,
        SectionRank.statedClassicalModel_of_mulEquiv (eKa.trans e') hm⟩
    have hm2 : Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) →
        Nonempty (↥K₁ ≃* alternatingGroup (Fin 7)) ∧
          Nonempty (↥(conjugate K₁ ā) ≃* alternatingGroup (Fin 7)) := by
      rintro ⟨e7⟩
      have hs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
        (LieType.Simplicity.fam_alternating_converse _ ⟨7, by norm_num, ⟨e7⟩⟩).2.2
      have hZO := fusionZStar_eq_pPrimeCore_of_isSimpleGroup hs hJna
      let e' : ↥K₁ ≃* J ⧸ pPrimeCore 2 J := eK.trans (QuotientGroup.quotientMulEquivOfEq hZO)
      exact ⟨⟨e'.trans e7⟩, ⟨(eKa.trans e').trans e7⟩⟩
    have hm3 : StatedClassicalModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 →
        StatedClassicalModel ↥K₁ .PSL 3 2 2 ∧ StatedClassicalModel ↥(conjugate K₁ ā) .PSL 3 2 2 :=
      fun hm => ⟨SectionRank.statedClassicalModel_of_mulEquiv eK hm,
        SectionRank.statedClassicalModel_of_mulEquiv (eKa.trans eK) hm⟩
    have htr : ∀ (Y : Type) [Group Y] (φ : ↥J ⧸ CFSG.Open.fusionZStar ↥J ≃* Y),
        ∃ Ψ : ↥W ≃* Y × Y,
          (∀ (j : ↥L) (hj : (j : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) ∈ W),
            Ψ ⟨j, hj⟩ = (φ (χ j), φ (χ j))) ∧
          ∀ (w : ↥W) (hw : ā⁻¹ * (w : ↥(H B) ⧸ criticalOddTwoCore ↥(H B)) * ā ∈ W),
            Ψ ⟨_, hw⟩ = (Ψ w).swap := by
      intro Y _ φ
      refine ⟨(ψ.trans (MulEquiv.prodCongr χ χ)).trans (MulEquiv.prodCongr φ φ),
        fun j hj => ?_, fun w hw => ?_⟩
      · rw [MulEquiv.trans_apply, hΨa j hj]
        rfl
      · rw [MulEquiv.trans_apply, hΨb w hw]
        rfl
    refine Or.inr ⟨⟨K₁, hK₁, hsw, hsup, hdisj, hcomm', hLset, hLC', δ, hδ, ψ, hψa, hψb, hψc, hLs,
      χ, fun y hy => heLJ y hy, hΨa, hΨb, hm1, hm2, hm3, htr⟩, fun hi => hWns hi.1⟩

end CFSG.ComponentClassification.UnbalancedCorr
