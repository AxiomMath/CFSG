module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FooteUnbalanced
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Assembly
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate2022
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2198
public import Certificates.Certificate2199
public import Certificates.Certificate2200
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2203
public import Certificates.Certificate2204
public import Certificates.Certificate2205
public import Certificates.Certificate2233
public import Certificates.Certificate2234
public import Certificates.Certificate2235
public import Certificates.Certificate2278
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3046
public import Certificates.Certificate3086
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3157
public import Certificates.Certificate3168
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitCases
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitThmBReach
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitOddInput
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

theorem gsL34ClosedType_of_noHeld_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hnoHe : ¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He))
    {a₀ x₀ : X} {J₀ : Subgroup X} (hU₀ : GSUnbalancingTriple a₀ x₀ J₀) :
    GSL34ClosedType J₀ := by
  obtain ⟨a, x, J, hmax, hR, hbound⟩ :=
    exists_maximal_unbalancing_triple_weakReach_of_simple hTB hSA hS hnonab hK hz hU hU₀
  have hJ : GSL34ClosedType J := by
    rcases GSFM.he_or_l34_of_reach_bound_of_footeUnbalanced hTB hSA hB hH hFU hHSF hCI hnonab hK hz hU hmax
        hbound with
      hHe | ⟨h34, -⟩
    · exact (hnoHe ⟨a, J, hmax.1.1, hmax.1.2.2.2.1, hmax.1.2.2.2.2.1, hHe⟩).elim
    · exact Or.inl h34
  exact gsL34ClosedType_of_gsWeakReach hS hK
    (fun z hz' => GSLit.not_mem_center_of_orderOf_eq_two hnonab hz') hR hJ

theorem l2_or_l34_of_noHeld_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hnoHe : ¬ ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ L ≤ centralizer ({t} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He))
    {c v : X} {K : Subgroup X} (hUK : GSUnbalancingTriple c v K) :
    IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K) ∨
      IsL34Type (K ⧸ Open.fusionZStar K) := by
  have hcl := gsL34ClosedType_of_noHeld_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hnonab hK hz hU hnoHe hUK
  have hcard := card_of_gsL34ClosedType hcl
  have hne : Open.fusionZStar K ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (K ⧸ Open.fusionZStar K) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩
    omega
  obtain ⟨hc, -, -, hKc, hKp, -⟩ := id hUK
  rcases hTB X hnonab hK hz hU c v K hUK with ⟨n, hodd, hn, he⟩ | hsmall | hbig
  · exact absurd ⟨c, K, n, hc, hodd, hn, hKc, hKp, he⟩ (hSA X hnonab hK hz hU)
  · rcases hsmall with heA | ⟨p, f, hp, hp2, -, -, hL⟩
    · exfalso
      obtain ⟨eA⟩ := heA
      have hsA : IsSimpleGroup (alternatingGroup (Fin 7)) :=
        alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
      have hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K) := @MulEquiv.isSimpleGroup _ _ _ _ hsA eA
      have hZ := fusionZStar_eq_pPrimeCore_of_simple hs hne
      have h2520 : Nat.card (K ⧸ Open.fusionZStar K) = 2520 := by
        rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
          Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      omega
    · have hs := FooteLit.isSimpleGroup_of_lieModel_psl_two hL
      have hZ := fusionZStar_eq_pPrimeCore_of_simple hs hne
      have heq : Nat.card (K ⧸ Open.fusionZStar K) = Open.ordA 1 (p ^ f) := by
        rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
          GSThmB.card_of_lieModel_psl_two hp2 hL]
      have hpodd : p ^ f ≠ 4 := by
        intro h4
        have h2 : 2 ∣ p ^ f := by rw [h4]; norm_num
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)
        exact hp2 this.symm
      rcases hcard with h1 | h1 | h1
      · rcases hcl with h34 | h5 | h7
        · exact (false_of_psl34_of_psl_two h34 hp2 hL).elim
        · rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h5] at h1
          exact absurd h1 (by decide)
        · rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h7] at h1
          exact absurd h1 (by decide)
      · rw [heq] at h1
        rcases eq_of_ordA_one_eq_sixty h1 with h4 | h5
        · exact absurd h4 hpodd
        · obtain ⟨rfl, rfl⟩ := eq_and_eq_one_of_pow_eq_prime hp Nat.prime_five h5
          exact Or.inl hL
      · rw [heq] at h1
        obtain ⟨rfl, rfl⟩ := eq_and_eq_one_of_pow_eq_prime hp (by norm_num : Nat.Prime 7)
          (eq_of_ordA_one_eq_168 h1)
        exact Or.inr (Or.inl hL)
  · rcases hbig with hHe | h34
    · exact (hnoHe ⟨c, K, hc, hKc, hKp, hHe⟩).elim
    · exact Or.inr (Or.inr h34)

namespace L34Central

variable {G : Type} [Group G] [Finite G]

theorem exists_max_setting_of_footeUnbalanced
    (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (hbase : L34BaseSetting G)
    (hex : ∃ (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J ∧
      IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ (a x : G) (J S : Subgroup G), L34Sec4Setting G a x J S ∧
      ∀ (a' x' : G) (J' S' : Subgroup G), L34Sec4Setting G a' x' J' S' →
        Nat.card S' ≤ Nat.card S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnonab, hK, hz, hU, -, hnoHe, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have hne : {p : G × G × Subgroup G × Subgroup G |
      L34Sec4Setting G p.1 p.2.1 p.2.2.1 p.2.2.2}.Nonempty := by
    obtain ⟨a₀, x₀, J₀, hU₀, -⟩ := hex
    obtain ⟨a, x, J, hmax, -, hbound⟩ :=
      exists_maximal_unbalancing_triple_weakReach_of_simple hTB hSA hS hnonab hK hz hU hU₀
    rcases GSFM.he_or_l34_of_reach_bound_of_footeUnbalanced hTB hSA hB hH hFU hHSF hCI hnonab hK hz hU hmax
        hbound with
      hHe | ⟨h34, hmaxJ⟩
    · exact (hnoHe ⟨a, J, hmax.1.1, hmax.1.2.2.2.1, hmax.1.2.2.2.2.1, hHe⟩).elim
    have hT := hmax.1
    obtain ⟨ha, hx, hax, hJa, -, hJx, -⟩ := gsUnbalancingTriple_iff.mp hT
    have haN : a ∈ normalizer (J : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun j hj =>
        mem_centralizer_singleton_iff.mp (hJa hj))
    have hxN : x ∈ normalizer (J : Set G) :=
      (le_normalizer_iff_commutator_le_left.mpr (le_of_eq hJx)) (mem_zpowers x)
    have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    obtain ⟨S, hSyl, hQS⟩ := exists_isSylowTwoIn_le
      (sup_le (zpowers_le.mpr haN) (zpowers_le.mpr hxN)) (isPGroup_sup_zpowers ha2 hx2 hax)
    exact ⟨⟨a, x, J, S⟩, hbase, hT, h34, hmaxJ, hSyl, hQS (mem_sup_left (mem_zpowers a)),
      hQS (mem_sup_right (mem_zpowers x))⟩
  obtain ⟨⟨a, x, J, S⟩, hset, hmaxS⟩ := Set.exists_max_image _
    (fun p : G × G × Subgroup G × Subgroup G => Nat.card ↥p.2.2.2) (Set.toFinite _) hne
  exact ⟨a, x, J, S, hset, fun a' x' J' S' h => hmaxS ⟨a', x', J', S'⟩ h⟩

end L34Central

theorem exists_l34Sec4Setting_central_zStar_of_footeUnbalanced
    (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (hMax : MaximalTwoComponentInput) {G : Type} [Group G] [Finite G]
    (hbase : L34BaseSetting G)
    (hex : ∃ (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J ∧
      IsL34Type (J ⧸ Open.fusionZStar J)) :
    ∃ (a x : G) (J S : Subgroup G), L34Sec4Setting G a x J S ∧ (∀ s ∈ S, s * a = a * s) ∧
      (S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) := by
  obtain ⟨a, x, J, S, hset, hmaxS⟩ :=
    L34Central.exists_max_setting_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hbase hex
  by_cases hZ : S ⊓ zStarIn J = ⊥
  · have hset' : L34Sec4Setting G a x J S := hset
    obtain ⟨-, hT, -, -, hSyl, haS, -⟩ := hset'
    obtain ⟨ha, -, -, hJa, -, -, -⟩ := gsUnbalancingTriple_iff.mp hT
    have hH : S ⊓ centralizer (J : Set G) ≠ ⊥ := by
      intro h
      have haH : a ∈ S ⊓ centralizer (J : Set G) := mem_inf.mpr ⟨haS,
        mem_centralizer_iff.mpr fun j hj => mem_centralizer_singleton_iff.mp (hJa hj)⟩
      rw [h, mem_bot] at haH
      rw [haH, orderOf_one] at ha
      exact absurd ha (by norm_num)
    obtain ⟨b, hbH, hb, hbc⟩ := exists_central_involution hSyl.isPGroup inf_le_left
      (L34Central.le_normalizer_inf_centralizer hSyl.1) hH
    obtain ⟨hbS, hbC⟩ := mem_inf.mp hbH
    have hJb : J ≤ centralizer ({b} : Set G) := fun j hj =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hbC) j hj)
    obtain ⟨M, hsetM, -⟩ := L34Central.exists_setting_of_central_step hS hMax hset hmaxS hb hbS
      hbc (GrS4.mem_coreActionKernel_of_le_centralizer hJb)
    by_cases hZM : S ⊓ zStarIn M = ⊥
    · exact ⟨b, x, M, S, hsetM, hbc, fun h => (h hZM).elim⟩
    · obtain ⟨b', M', hsetM', hbc', hb'⟩ :=
        L34Central.exists_setting_zStar_step hS hMax hsetM hmaxS hZM
      exact ⟨b', x, M', S, hsetM', hbc', fun _ => hb'⟩
  · obtain ⟨b, M, hsetM, hbc, hb⟩ := L34Central.exists_setting_zStar_step hS hMax hset hmaxS hZ
    exact ⟨b, x, M, S, hsetM, hbc, fun _ => hb⟩

theorem l34Case_of_steps_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (hMax : MaximalTwoComponentInput)
    (h51 : L34Prop51Five) (h510 : L34Lemma510) (h511 : L34Lemma511)
    (hne : L34UnbalancingSetNonempty) : L34Case := by
  intro X _ _ _ hnonab hK hz hU hloc hnoHe ⟨x, y, L, hT, h34⟩
  have hbase : L34BaseSetting X := ⟨inferInstance, hnonab, hK, hz, hU, hloc, hnoHe,
    fun c v K hUK => l2_or_l34_of_noHeld_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hnonab hK hz hU hnoHe hUK⟩
  obtain ⟨L₀, t₀, hfam₀⟩ := h51 X hbase
    (exists_l34Sec4Setting_central_zStar_of_footeUnbalanced hTB hSA hS hB hH hFU hHSF hCI hMax hbase
      ⟨x, y, L, hT, h34⟩)
  obtain ⟨⟨L₁, t₁⟩, hfam, hmax⟩ := Set.exists_max_image
    {p : Subgroup X × X | IsL34Family p.1 p.2}
    (fun p => toLex (twoExp (zStarIn p.1), twoExp (coreActionKernel p.1)))
    (Set.toFinite _) ⟨⟨L₀, t₀⟩, hfam₀⟩
  obtain ⟨⟨a, x', J, -, -, ht2, -, hLJ⟩, -⟩ := id hfam
  have hLJ' : L₁ = pumpUp J t₁ := hLJ
  have htL : L₁ ≤ centralizer ({t₁} : Set X) := by
    rw [hLJ']
    exact pumpUp_le_centralizer
  have htN : t₁ ∈ normalizer (L₁ : Set X) :=
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun l hl =>
      (mem_centralizer_singleton_iff.mp (htL hl)))
  obtain ⟨S, hSyl, htS⟩ := exists_isSylowTwoIn_mem htN ht2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hSQ⟩ := hSyl.isPGroup.exists_le_sylow
  have hQ : IsSylowTwoIn (Q : Subgroup X) ⊤ := ⟨le_top, Q.subtype le_top, Q.coe_subtype le_top⟩
  exact false_of_sec5_steps h510 h511 hne
    ⟨hbase, hfam, fun L' t' hfam' => hmax ⟨L', t'⟩ hfam', hSyl, htS, hSQ, hQ⟩

end CFSG.ComponentClassification.GrSLit
