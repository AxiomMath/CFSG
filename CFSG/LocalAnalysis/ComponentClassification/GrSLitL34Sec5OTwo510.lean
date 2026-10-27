module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5PumpOdd510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5StdEven

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem odd_card_zStarIn_of_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hStd : GSThmB.L34StandardEvenInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hUnit : L34UnbalancingUnitaryStep)
    (hUA : L34UnitaryAutFact) (h41 : L34Prop41) (hElem : L34ElementaryCenterSylowFact)
    (hBd : L34Lemma510OTwoBoundStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁))
    (hmax₁ : GSWeakMaximalComponent K₁)
    (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x)
    (hT91 : ∀ b : G, orderOf b = 2 → K₁ ≤ centralizer ({b} : Set G) →
      (⨆ (g : G) (_ : conjugate K₁ g ≤ centralizer ({b} : Set G)), conjugate K₁ g) ≤
        oddIn (centralizer ({b} : Set G)) ⊔ K₁) :
    Odd (Nat.card ↥(zStarIn K₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have h3 := three_le_pRank_of_l34 htype₁
  have hT92 := (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
    (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) u hu2 hK₁u).2 h3
  have hCN₁ := centralizer_le_normalizer_of_isPComponent hT92 hK₁u hK₁p
  have hSN : S ≤ normalizer (K₁ : Set G) := fun s hs =>
    hCN₁ (mem_centralizer_singleton_iff.mpr (huc s hs))
  obtain ⟨-, hrk, -⟩ := hUA G K₁ S t (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p)
    htype₁ (hUnit G u t K₁ hT₁ htype₁) hS2
    (le_inf hSN fun s hs => mem_centralizer_singleton_iff.mpr (hZS s hs))
  obtain ⟨E, hEP, hEl, hEc⟩ := exists_elemTwo_sixtyFour h59 hset
  have hES : E ≤ S := hEP.trans (sup_le inf_le_left ((omegaOne_le _).trans inf_le_left))
  have hF8 : 8 ≤ Nat.card ↥(E ⊓ coreActionKernel K₁) := by
    have := hrk E hES hEl
    omega
  have hF : IsElemTwo (E ⊓ coreActionKernel K₁) := hEl.mono inf_le_left
  have hFK : E ⊓ coreActionKernel K₁ ≤ coreActionKernel K₁ := inf_le_right
  refine (Nat.even_or_odd _).resolve_left fun hev => ?_
  have hA : ∀ S₁ : Subgroup G, IsSylowTwoIn S₁ (normalizer (K₁ : Set G)) → S ≤ S₁ →
      ∀ b ∈ S₁ ⊓ zStarIn K₁, orderOf b = 2 → (∀ s ∈ S₁, s * b = b * s) →
        pumpUp K₁ b ≠ K₁ := by
    intro S₁ hS₁ hSS₁ b hb hbo hbc hPb
    have hbS₁ : b ∈ S₁ := (mem_inf.mp hb).1
    have hbZ : b ∈ zStarIn K₁ := (mem_inf.mp hb).2
    have hK₁b := le_centralizer_of_mem_zStarIn hK₁u hK₁p hO hbZ
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp at hbo
    have hbG : b ∉ center G := by
      have : IsSimpleGroup G := hbase.1
      exact not_mem_center_of_ne_one hbase.2.1 hb1
    have hTb := gsUnbalancingTriple_of_pumpUp_eq hS hbase.2.2.1 hT₁ hbo hbG (hbc u (hSS₁ huS))
      (hbc t (hSS₁ htS)) hK₁b hPb
    have hset₁ : L34Sec4Setting G b t K₁ S₁ := ⟨hbase, hTb, htype₁, hmax₁, hS₁, hbS₁, hSS₁ htS⟩
    have hW₁ := h41 G b t K₁ S₁ hset₁ hbc fun _ => hb
    obtain ⟨v, hK₁v, hfam, hsup⟩ := exists_isL34Family_of_component hS hSol hMax hbase hTb
      htype₁ hmax₁ hS₁ hbc (not_isStandardSubgroup_of_mem_zStarIn hU hStd hbase htype₁ hbo hbZ)
      hW₁
    have hbL₁ : b ∈ pumpUp K₁ v :=
      map_subtype_le _ (mem_zStarIn_of_sup_oddIn (le_sup_left.trans hsup.le) hsup hbZ)
    have hbv : b * v = v * b :=
      mem_centralizer_singleton_iff.mp (pumpUp_le_centralizer K₁ v hbL₁)
    by_cases hbv' : b = v
    ·
      rw [← hbv', hPb] at hfam
      exact hfam.2.2.2.1 (oddIn_le_map_center hO)
    · exact false_of_pumpUp_family hS hU hheld hSol hGW h58 h59 hBd hset hu huc hmax hK₁u hK₁p
        hK₁n htype₁ hO hev hFK hF hF8 hS₁ hSS₁ hb hbo hbc hPb hW₁ hbv hbv' hK₁b hK₁v hfam hsup
  obtain ⟨S₁, hS₁, hSS₁, b, hb, hbo, hbc⟩ := exists_sylow_central_involution_zStarIn hSN hS2 hev
  have hK₁b := le_centralizer_of_mem_zStarIn hK₁u hK₁p hO (mem_inf.mp hb).2
  have hub : u * b = b * u := hbc u (hSS₁ huS)
  have hgs := gsFixedLayer_eq_of_le hK₁u hK₁p hK₁b
  have hsupb := sup_oddIn_pumpUp hK₁b hgs (hT91 b hbo hK₁b)
  have hPb := hA S₁ hS₁ hSS₁ b hb hbo hbc
  have hbad : ¬ oddIn (pumpUp K₁ b) ≤ (center ↥K₁).map K₁.subtype := fun h => hPb
    (le_antisymm (hsupb.symm.le.trans (sup_le le_rfl (h.trans (map_subtype_le _))))
      (le_pumpUp hgs))
  obtain ⟨F₀, hF₀F, hF₀c⟩ := exists_le_card_eight hF.isPGroup hF8
  have hF₀E : F₀ ≤ E := hF₀F.trans inf_le_left
  exact hbad (oddIn_pumpUp_le_center_of_eight hS hU hheld hSol hGW h58 hElem hset hu2 hK₁u hK₁p
    hbo hub hK₁b (hT91 b hbo hK₁b) ⟨hF.mono hF₀F, hF₀c⟩ (hF₀E.trans hEP) (hF₀F.trans hFK)
    fun f hf => hbc f (hSS₁ (hES (hF₀E hf))))

theorem l34Lemma510OTwoStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hStd : GSThmB.L34StandardEvenInput)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hUnit : L34UnbalancingUnitaryStep)
    (hUA : L34UnitaryAutFact) (hComp : L34Cor217ComponentStep)
    (h41 : L34Prop41) (hElem : L34ElementaryCenterSylowFact) (hBd : L34Lemma510OTwoBoundStep) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (S T : Subgroup G),
      L34Sec5Setting G L t S T → ∀ u ∈ L34UnbalancingSet L t S, (∀ s ∈ S, s * u = u * s) →
      (∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
        Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) →
      ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
        IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
        ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
        IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → (∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) →
        Odd (Nat.card ↥(zStarIn K₁)) := by
  intro G _ _ L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n htype₁ hO
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have hmax₁ :=
    hComp G L t S T hset u huS₀ hu2 K₁ hK₁u hK₁p hK₁n htype₁
  have hbase := hset.1
  obtain ⟨hsF, hnF, hoF⟩ := fstar_facts hbase
  have : IsSimpleGroup G := hbase.1
  have h3 := three_le_pRank_of_l34 htype₁
  exact odd_card_zStarIn_of_component hS hU hheld hSol hGW hMax hStd h58 h59 hUnit hUA h41
    hElem hBd hset hu huc hmax hK₁u hK₁p hK₁n htype₁ hmax₁ hO fun b hb hK₁b =>
      (hMax G hsF hnF hoF hbase.2.2.1 K₁ hmax₁ (by omega)
        (Sol78.not_psp4_of_l34 htype₁) (Or.inl ⟨htype₁, hbase⟩) b hb hK₁b).1

end CFSG.ComponentClassification.GrSLit.GrS5
