module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Choice59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Conj59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Triple59
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem omegaOne_ne_zpowers_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hStd : GSThmB.L34StandardEvenInput) (h56 : L34Lemma56) (hAut : L34AutRankOneNormalFact)
    (hF1 : L34SylowCentralizerFact) (hUCen : L34UnitaryCenterFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUC : L34UnitaryCentralizerFact)
    (hUA : L34UnitaryAutFact) (hComp : L34Cor217ComponentStep)
    (h41 : L34Prop41) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) : omegaOne (S ⊓ coreActionKernel L) ≠ zpowers t := by
  intro hΩ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ := eq_zpowers_of_omegaOne_eq hS hU hheld hSol hGW hMax h56 hAut hset hΩ
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -⟩, -, hSyl, htS, hST, hTsyl⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by rintro rfl; simp at hto
  have hT2 : IsPGroup 2 T := IsSylowTwoIn.isPGroup hTsyl
  obtain ⟨x, hx⟩ := l34Lemma59TripleStep_of_inputs hS hU hheld hSol hGW G L t S T hset hQ
  obtain ⟨x₁, hx₁S, hx₁⟩ := exists_unitary_mem hS hU hheld hSol hGW hMax hUnit hset hx
  obtain ⟨H, hHle, hH4, htH, hcen⟩ :=
    exists_card_le_four_of_unitary hS hU hheld hSol hGW hF1 hUCen hset hQ hx₁S hx₁
  have hSlt : S < T := lt_of_le_of_ne hST fun h => h56 G L t S T hset (h ▸ hTsyl)
  have hTne : T ≠ ⊥ := fun h => ht1 (by rw [← mem_bot, ← h]; exact hST htS)
  obtain ⟨u, huT, hu2, huc⟩ := GSLit.exists_involution_mem_center hT2 le_rfl le_normalizer hTne
  have huT' : ∀ y ∈ T, u * y = y * u := fun y hy => (huc y hy).symm
  have huS : u ∈ S := mem_of_mem_center_of_le hSyl htS hST hT2 hCN huT huT'
  have huZS : ∀ s ∈ S, u * s = s * u := fun s hs => huT' s (hST hs)
  have huH : u ∈ H := hcen u huS huZS
  have hu1 : u ≠ 1 := by rintro rfl; simp at hu2
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have htu : t * u = u * t := (huZS t htS).symm
  have hut : u ≠ t := by
    rintro rfl
    have hTN : T ≤ normalizer (L : Set G) := fun y hy =>
      hCN (mem_centralizer_singleton_iff.mpr (huc y hy))
    exact hSlt.ne (IsSylowTwoIn.eq_of_le hSyl hST hTN hT2).symm
  obtain ⟨n, hnT, hnS, hnN⟩ := exists_normalizer_not_mem_of_lt_two hT2 hSlt
  set s := n⁻¹ * t * n with hs
  have hsS : s ∈ S := by
    have h := (mem_normalizer_iff.mp (inv_mem hnN) t).mp htS
    rwa [inv_inv] at h
  have hsZ : ∀ y ∈ S, s * y = y * s := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ S := (mem_normalizer_iff.mp hnN y).mp hy
    have h2 := hZS _ h1
    calc s * y = n⁻¹ * (t * (n * y * n⁻¹)) * n := by rw [hs]; group
      _ = n⁻¹ * (n * y * n⁻¹ * t) * n := by rw [h2]
      _ = y * s := by rw [hs]; group
  have hts : t = n * s * n⁻¹ := by rw [hs]; group
  have hs1 : s ≠ 1 := fun h => ht1 (by rw [hts, h, mul_one, mul_inv_cancel])
  have hst : s ≠ t := by
    intro h
    have hnC : n ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc n * t = n * s := by rw [h]
        _ = t * n := by rw [hs]; group
    have hle : S ⊔ zpowers n ≤ T := sup_le hST (zpowers_le.mpr hnT)
    have heq := IsSylowTwoIn.eq_of_le hSyl le_sup_left
      (sup_le hSyl.1 (zpowers_le.mpr (hCN hnC))) (hT2.to_le hle)
    exact hnS (heq ▸ mem_sup_right (mem_zpowers n))
  have hsu : s ≠ u := by
    intro h
    apply hut
    have h2 : t = n * u * n⁻¹ := by rw [hts, h]
    rw [h2, show n * u = u * n from (huT' n hnT).symm, mul_inv_cancel_right]
  have hsut : s = u * t :=
    eq_mul_of_card_le_four hH4 ht2 hu2' htu htH huH (hcen s hsS hsZ) ht1 hu1 hut hs1 hst hsu
  have hXut : oddIn L ⊓ centralizer ({u * t} : Set G) ≤
      oddIn (centralizer ({u * t} : Set G)) := by
    have h := oddIn_inf_centralizer_le_of_conj hS hU hheld hSol hGW hMax hL34 hUnit hUC hset hnN
    rwa [← hs, hsut] at h
  have huK : u ∉ coreActionKernel L := fun h => by
    have h1 : u ∈ zpowers t := hQ ▸ mem_inf.mpr ⟨huS, h⟩
    rcases eq_one_or_eq_of_mem_zpowers' ht2 h1 with h2 | h2
    · exact hu1 h2
    · exact hut h2
  have huU0 : u ∈ S ⊓ L ⊔ zpowers t := by
    rw [sup_comm]
    exact hHle huH
  have huLt : u ∈ L ⊔ zpowers t := sup_le_sup_right (inf_le_right : S ⊓ L ≤ L) (zpowers t) huU0
  have hY : ¬ oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn (centralizer ({u} : Set G)) := by
    obtain ⟨-, u₁, hu₁, hu₁n⟩ :=
      l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset u huS hu2 huK huLt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu₁
    rcases hu₁ with rfl | rfl
    · exact hu₁n
    · exact absurd hXut hu₁n
  have hZT : ∀ w ∈ T, (∀ y ∈ T, y * w = w * y) → orderOf w = 2 → w = u := by
    intro w hwT hwc hw2
    have hwc' : ∀ y ∈ T, w * y = y * w := fun y hy => (hwc y hy).symm
    have hwH : w ∈ H := hcen w (mem_of_mem_center_of_le hSyl htS hST hT2 hCN hwT hwc')
      fun s hs => hwc' s (hST hs)
    have htc : ¬ ∀ y ∈ T, y * t = t * y := fun h => hSlt.ne (IsSylowTwoIn.eq_of_le hSyl hST
      (fun y hy => hCN (mem_centralizer_singleton_iff.mpr (h y hy))) hT2).symm
    by_contra hwu
    have hw1 : w ≠ 1 := by rintro rfl; simp at hw2
    have hwt : w ≠ t := fun h => htc (by rw [← h]; exact hwc)
    have hw := eq_mul_of_card_le_four hH4 ht2 hu2' htu htH huH hwH ht1 hu1 hut hw1 hwt hwu
    apply htc
    intro y hy
    have htw : t = u * w := by rw [hw, ← mul_assoc, hu2', one_mul]
    rw [htw, mul_assoc, ← hwc y hy, ← mul_assoc, huc y hy, mul_assoc]
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  obtain ⟨K₁, hK₁u, hK₁p, hK₁n⟩ := exists_isPComponent_not_le hSol hto hu2 htu hYD hY
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hmax₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → GSWeakMaximalComponent K₁ :=
    hComp G L t S T hset u huU0 hu2 K₁ hK₁u hK₁p hK₁n
  obtain ⟨huK₁, htype₁⟩ :=
    mem_zStarIn_of_unbalancing_center hMax hset.1 hTsyl huT (hST htS) huc hZT hT₁ hmax₁
  exact false_of_mem_zStarIn_component hS hU hheld hSol hGW hMax hStd hUnit hUA h41 hset hQ
    huT huc hu2 hT₁ huK₁ (hmax₁ htype₁)

end CFSG.ComponentClassification.GrSLit.GrS5
