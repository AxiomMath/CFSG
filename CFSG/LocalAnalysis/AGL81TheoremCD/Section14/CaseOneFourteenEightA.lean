module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneThreeStarImg
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.OddOrderClosurePResidual
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerData
import CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.PrimeRankSylowTransport
import CFSG.Quasithin.Background.A1bReduced
import CFSG.Quasithin.Background.A3Structure318Star
import CFSG.RankThree.PartOne.S11d.FinalLemmas
import CFSG.Quasithin.Background.B682Ambient
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
open CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (gnV gnC gnImg)

variable {G : Type} [Group G] [Finite G]

private theorem centerQuotient_surjective {J B : Subgroup G}
    (hB : IsPGroup 3 B) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hcomm : ⁅B, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype) :
    Function.Surjective
      ((QuotientGroup.mk' (Subgroup.center (threeStar J))).comp
        ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)).comp
          (Subgroup.inclusion (inf_le_left :
            J ⊓ Subgroup.centralizer (B : Set G) ≤ J)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let D : Subgroup G := (CFSG.pPrimeCore 3 ↥J).map J.subtype
  let πJ : ↥J →* threeStar J := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)
  let πZ : threeStar J →* threeStar J ⧸ Subgroup.center (threeStar J) :=
    QuotientGroup.mk' (Subgroup.center (threeStar J))
  change Function.Surjective (πZ.comp (πJ.comp (Subgroup.inclusion inf_le_left)))
  have hDcop : Nat.Coprime 3 (Nat.card D) := by
    have hcard : Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥J) :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hDnot : ¬ 3 ∣ Nat.card D :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hDcop
  have hNJ : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
      J (CFSG.pPrimeCore 3 ↥J) (CFSG.pPrimeCore_characteristic (p := 3))
  have hJN : J ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer.trans hNJ
  have hBN : B ≤ Subgroup.normalizer (D : Set G) := hBJ.trans hNJ
  intro y
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (threeStar J)) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥J) w
  obtain ⟨d, hdD, hxdJ, hxdC⟩ :=
    exists_coset_translate_centralizer (x := x) hB (Subgroup.map_subtype_le _)
      hJN hBN hDnot hcomm
  let c : ↥(J ⊓ Subgroup.centralizer (B : Set G)) :=
    ⟨(x : G) * d, ⟨hxdJ, hxdC⟩⟩
  refine ⟨c, ?_⟩
  have hdJ : d ∈ J := (Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥J)) hdD
  have hdP : ⟨d, hdJ⟩ ∈ CFSG.pPrimeCore 3 ↥J :=
    (Subgroup.mem_map_iff_mem J.subtype_injective).mp hdD
  have hdmk : πJ ⟨d, hdJ⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hdP
  have hq : πJ ⟨(x : G) * d, hxdJ⟩ = πJ x := by
    have hmul : πJ ⟨(x : G) * d, hxdJ⟩ =
        πJ x * πJ ⟨d, hdJ⟩ := by
      rw [show (⟨(x : G) * d, hxdJ⟩ : ↥J) = x * ⟨d, hdJ⟩ from
        Subtype.ext rfl, map_mul]
    rw [hmul, hdmk, mul_one]
  change πZ (πJ ⟨(x : G) * d, hxdJ⟩) = πZ (πJ x)
  rw [hq]

theorem not_isPSolvable_inf_centralizer {J B : Subgroup G}
    (hq : CFSG.IsQuasisimple (threeStar J))
    (h3 : 3 ∣ Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)))
    (hB : IsPGroup 3 B) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hcomm : ⁅B, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(J ⊓ Subgroup.centralizer (B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hsolv
  let φ : ↥(J ⊓ Subgroup.centralizer (B : Set G)) →*
      threeStar J ⧸ Subgroup.center (threeStar J) :=
    (QuotientGroup.mk' (Subgroup.center (threeStar J))).comp
      ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J)).comp
        (Subgroup.inclusion (inf_le_left :
          J ⊓ Subgroup.centralizer (B : Set G) ≤ J)))
  have hsurj : Function.Surjective φ := centerQuotient_surjective hB hBJ hcomm
  have himg : CFSG.HallHigman.IsPSolvable 3
      (threeStar J ⧸ Subgroup.center (threeStar J)) := by
    have hsolv' : CFSG.HallHigman.IsPSolvable 3
        ↥(⊤ : Subgroup ↥(J ⊓ Subgroup.centralizer (B : Set G))) :=
      isPSolvable_of_mulEquiv
        (Subgroup.topEquiv (G := ↥(J ⊓ Subgroup.centralizer (B : Set G)))).symm hsolv
    have h := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map
      (p := 3) φ (N := ⊤) hsolv'
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj] at h
    exact isPSolvable_of_mulEquiv Subgroup.topEquiv h
  have hnc : ¬ IsMulCommutative (threeStar J ⧸ Subgroup.center (threeStar J)) := by
    intro h
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab (isMulCommutative_iff.mp h a b)
  exact CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer.not_isPSolvable_of_simple
    hq.2.1 hnc h3 himg

private theorem three_dvd_card_centerQuotient_of_isSL34Star {J : Subgroup G}
    (h : IsSL34Star J) :
    3 ∣ Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) := by
  have hmul := Subgroup.card_mul_index (Subgroup.center (threeStar J))
  rw [h.2, Subgroup.index_eq_card, IsSL34Star.card_threeStar h] at hmul
  have hq : Nat.card (threeStar J ⧸ Subgroup.center (threeStar J)) = 20160 := by
    omega
  rw [hq]
  norm_num

theorem CaseOneCtx.pRank_centralizer_center_le
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    (h142 : FourteenTwoCaseOneAt M) (h145 : FourteenFiveCaseOneAt M) {p : ℕ}
    (hp : p ∈ sigmaSet G M) :
    CFSG.Open.pRank p (M ⊓ Subgroup.centralizer
      (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G)) ≤ 1 := by
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  have hA_le_J : A ≤ J := by
    rw [hAdef]
    exact (c.center_le_commutator h142).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  by_contra hle
  have h2 : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) := by omega
  have h142' := h142 H E Q J c.choice c.typeA
  have hAcard : Nat.card A = 3 := h142'.1.2.2.2
  have hAQ : A ≤ Q := Subgroup.map_subtype_le _
  have hA3 : IsPGroup 3 A := c.choice.sylow.isPGroup.to_le hAQ
  have hAE : ⁅A, E⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro a ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hq (⟨e, c.choice.E_le_Q he⟩ : ↥Q))
  have hoTwo : CFSG.Open.pCoreOf 2 J ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono
      (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))
  obtain ⟨Q₀, hQ₀Q, -, hQ₀J, hAQ₀, -, -, -, -⟩ := c.exists_Q₀ h142
  have hsolv : CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer (A : Set G)) :=
    h145 H E Q J c.choice c.typeA p hp A hAQ hAcard h2
      ((Subgroup.commutator_mono hAQ₀ le_rfl).trans hQ₀J) (Or.inl hAE)
  have hA_le_J : A ≤ J :=
    (c.center_le_commutator h142).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  have hcommA : ⁅A, J⁆ ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype :=
    (Subgroup.commutator_mono hAQ₀ le_rfl).trans (hQ₀J.trans hoTwo)
  have hnot := not_isPSolvable_inf_centralizer (J := J) (B := A)
    c.isKComp.isQuasisimple (three_dvd_card_centerQuotient_of_isSL34Star c.isSL34Star)
    hA3 (hA_le_J.trans Subgroup.le_normalizer) hcommA
  exact hnot (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    hsolv (fun x hx => ⟨c.choice.J_comp.1 hx.1, hx.2⟩))

private theorem exists_plane_facts
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {Q₀ : Subgroup G} (hQ₀Q : Q₀ ≤ Q)
    (hAQ₀ : (Subgroup.center ↥Q).map Q.subtype ≤ Q₀)
    (hQ₀f : ∃ f ∈ Q₀, f ∉ J) :
    ∃ (A F : Subgroup G) (f : G), A = (Subgroup.center ↥Q).map Q.subtype ∧
      F = A ⊔ Subgroup.zpowers f ∧ IsElemAbelian 3 F ∧ Nat.card F = 9 ∧
      F ≤ Q₀ ∧ F ≤ Q := by
  classical
  have h142' := h142 H E Q J c.choice c.typeA
  have hAcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3 := h142'.1.2.2.2
  have hAQ : (Subgroup.center ↥Q).map Q.subtype ≤ Q := Subgroup.map_subtype_le _
  have hA_le_J : (Subgroup.center ↥Q).map Q.subtype ≤ J :=
    (c.center_le_commutator h142).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  have hAcentQ : (Subgroup.center ↥Q).map Q.subtype ≤
      Subgroup.centralizer (Q : Set G) := by
    rintro a ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hq ⟨y, hy⟩)
  have hAea : IsElemAbelian 3 ((Subgroup.center ↥Q).map Q.subtype) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp (hAcentQ y.2) x.1 (hAQ x.2)
    · intro x hx
      exact h142'.1.2.1 x (hAQ hx)
  obtain ⟨f, hfQ₀, hfJ⟩ := hQ₀f
  have hfQ : f ∈ Q := hQ₀Q hfQ₀
  have hfpow : f ^ 3 = 1 := h142'.1.2.1 f hfQ
  have hfne : f ≠ 1 := by
    intro h
    exact hfJ (h ▸ J.one_mem)
  have hford : orderOf f = 3 := orderOf_eq_prime hfpow hfne
  have hfA : f ∉ (Subgroup.center ↥Q).map Q.subtype := by
    intro h
    exact hfJ (hA_le_J h)
  have hcommAf : ∀ a ∈ (Subgroup.center ↥Q).map Q.subtype, a * f = f * a := by
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hAcentQ ha) f hfQ).symm
  obtain ⟨hFea, hFcard⟩ :=
    CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hAcard hford hfA hcommAf
  have hFQ₀ : (Subgroup.center ↥Q).map Q.subtype ⊔ Subgroup.zpowers f ≤ Q₀ :=
    sup_le hAQ₀ (Subgroup.zpowers_le.mpr hfQ₀)
  refine ⟨(Subgroup.center ↥Q).map Q.subtype,
    (Subgroup.center ↥Q).map Q.subtype ⊔ Subgroup.zpowers f, f, rfl, rfl,
    hFea, ?_, hFQ₀, hFQ₀.trans hQ₀Q⟩
  rw [hFcard]
  norm_num

private theorem exists_plane_element
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {Q₀ P : Subgroup G} (hQ₀Q : Q₀ ≤ Q)
    (hAQ₀ : (Subgroup.center ↥Q).map Q.subtype ≤ Q₀)
    (hQ₀f : ∃ f ∈ Q₀, f ∉ J)
    (hPD : P ≤ CFSG.inSubgroup (CFSG.pPrimeCore 3) M)
    (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hPA : ⁅P, (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥) :
    ∃ x : G, x ∈ Q₀ ∧ x ≠ 1 ∧ x ^ 3 = 1 ∧
      ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
        (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥ := by
  classical
  obtain ⟨A, F, f, hAdef, hFdef, hFea, hFcard, hFQ₀, hFQ⟩ :=
    exists_plane_facts c h142 hQ₀Q hAQ₀ hQ₀f
  have hDcop : Nat.Coprime 3 (Nat.card (CFSG.inSubgroup (CFSG.pPrimeCore 3) M)) := by
    have hcard : Nat.card (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) =
        Nat.card (CFSG.pPrimeCore 3 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  have hPcop : Nat.Coprime 3 (Nat.card P) :=
    hDcop.coprime_dvd_right (Subgroup.card_dvd_of_le hPD)
  have hcompl : ¬ 3 ∣ Nat.card P :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPcop
  have hFpow : ∀ member : ↥F, member ^ 3 = 1 := by
    intro member
    exact Subtype.ext (hFea.2 member member.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    3 Nat.prime_three F P hFpow (by rw [hFcard]; norm_num) hcompl (hFQ.trans hQP)
  have hex : ∃ x : G, x ∈ F ∧ x ≠ 1 ∧
      ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
        (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥ := by
    by_contra h
    push Not at h
    have hle : P ≤ Subgroup.centralizer ((Subgroup.center ↥Q).map Q.subtype : Set G) := by
      rw [hgen]
      refine iSup_le fun m => iSup_le fun hm => ?_
      have hbot : ⁅P ⊓ Subgroup.centralizer ({(m : G)} : Set G),
          (Subgroup.center ↥Q).map Q.subtype⁆ = ⊥ :=
        h (m : G) m.2 (fun h1 => hm (Subtype.ext h1))
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact hPA (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle)
  obtain ⟨x, hxF, hxne, hxcomm⟩ := hex
  exact ⟨x, hFQ₀ hxF, hxne, hFea.2 x hxF, hxcomm⟩

private theorem exists_sylow_not_centralizes
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M) {p : ℕ} (hp : p ∈ sigmaSet G M)
    (h2D : 2 ≤ CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M)) :
    ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ∧
      P ≤ M ∧ Q ≤ Subgroup.normalizer (P : Set G) ∧
      ⁅P, (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥ := by
  set D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M with hDdef
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hDcop : ¬ 3 ∣ Nat.card D := by
    have hcard : Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        M (CFSG.pPrimeCore 3 ↥M) (CFSG.pPrimeCore_characteristic (p := 3)))
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) := (c.choice.Q_le_M c.nine).trans hMD
  obtain ⟨P : Subgroup G, hPsylow, -, hQP⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := 3) (r := p)
      Nat.prime_three hp_prime c.choice.sylow.isPGroup hQD hDcop (P := ⊥) bot_le
      IsPGroup.of_bot (by
        have h : Subgroup.normalizer (G := G) (⊥ : Subgroup G) = ⊤ := by
          rw [Subgroup.normalizer_eq_top_iff]
          exact inferInstance
        exact le_top.trans h.ge)
  have hPM : P ≤ M := hPsylow.le.trans (Subgroup.map_subtype_le _)
  have hPA : ⁅P, A⁆ ≠ ⊥ := by
    intro hbot
    have hPC : P ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hleRank : CFSG.Open.pRank p P ≤
        CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) :=
      CFSG.SectionRank.pRank_mono hp_prime.one_lt (fun y hy => ⟨hPM hy, hPC hy⟩)
    have hle1 : CFSG.Open.pRank p
        (M ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 := by
      simpa [hAdef] using c.pRank_centralizer_center_le h142 h145 hp
    have h2P : 2 ≤ CFSG.Open.pRank p P := by
      rw [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hp_prime hPsylow]
      exact h2D
    omega
  exact ⟨P, hPsylow, hPM, hQP, by simpa [hAdef] using hPA⟩

private theorem not_isCyclic_inf_centralizer_of_plane
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {Q₀ P : Subgroup G} {x : G}
    (hQ₀C : Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G))
    (hxQ₀ : x ∈ Q₀) (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hxcomm : ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
      (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥) :
    ¬ IsCyclic ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) := by
  intro hcyc
  haveI : IsCyclic ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) := hcyc
  have hder := commutator_normalizer_le_centralizer
    (P ⊓ Subgroup.centralizer ({x} : Set G))
  have hQJcent : Q ⊓ J ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp (hQ₀C hxQ₀) y hy).symm
  have hQJN : Q ⊓ J ≤
      Subgroup.normalizer ((P ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) := by
    have hNp : Q ⊓ J ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans hQP
    have hNc : Q ⊓ J ≤ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G) :=
      hQJcent.trans (Subgroup.le_normalizer
        (H := Subgroup.centralizer ({x} : Set G)))
    exact (le_inf hNp hNc).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hA_le_der : (Subgroup.center ↥Q).map Q.subtype ≤ ⁅Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({x} : Set G)) : Set G),
      Subgroup.normalizer ((P ⊓ Subgroup.centralizer ({x} : Set G)) : Set G)⁆ :=
    (c.center_le_commutator h142).trans (Subgroup.commutator_mono hQJN hQJN)
  have hbot : ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
      (Subgroup.center ↥Q).map Q.subtype⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hA_le_der.trans hder)
  exact hxcomm hbot

private theorem plane_element_A_normalizes
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {Q₀ P : Subgroup G} {x : G}
    (hQ₀C : Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G))
    (hxQ₀ : x ∈ Q₀) (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hxcomm : ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
      (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥) :
    (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) ∧
    ⁅(Subgroup.center ↥Q).map Q.subtype,
      P ⊓ Subgroup.centralizer ({x} : Set G)⁆ ≠ ⊥ := by
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  have hA_le_J : A ≤ J := by
    rw [hAdef]
    exact (c.center_le_commutator h142).trans
      ((Subgroup.commutator_le_self (Q ⊓ J)).trans inf_le_right)
  have hA_le_QJ : A ≤ Q ⊓ J := fun a ha =>
    ⟨Subgroup.map_subtype_le _ ha, hA_le_J ha⟩
  have hAcentx : A ≤ Subgroup.centralizer ({x} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp (hQ₀C hxQ₀) a (hA_le_QJ ha)).symm
  have hA_normP : A ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.map_subtype_le _).trans hQP
  have hA_normC : A ≤ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G) :=
    hAcentx.trans (Subgroup.le_normalizer
      (H := Subgroup.centralizer ({x} : Set G)))
  have hA_norm : A ≤ Subgroup.normalizer
      ((P ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) :=
    (le_inf hA_normP hA_normC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hxcomm' : ⁅A, P ⊓ Subgroup.centralizer ({x} : Set G)⁆ ≠ ⊥ := by
    rw [Subgroup.commutator_comm]
    simpa [hAdef] using hxcomm
  exact ⟨by simpa [hAdef] using hA_norm, by simpa [hAdef] using hxcomm'⟩

private theorem plane_element_contradiction
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M) {p : ℕ} (hp : p ∈ sigmaSet G M)
    {Q₀ P : Subgroup G} {x : G}
    (hQ₀C : Q₀ ≤ Subgroup.centralizer ((Q ⊓ J : Subgroup G) : Set G))
    (hxQ₀ : x ∈ Q₀) (hQP : Q ≤ Subgroup.normalizer (P : Set G))
    (hPsylow : CFSG.ABGLocalTools.IsSylowOf p P
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M))
    (hx3 : x ^ 3 = 1) (hxne : x ≠ 1)
    (hA0Q : Subgroup.zpowers x ≤ Q)
    (hA0J : ⁅Subgroup.zpowers x, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hP'p : IsPGroup p ↥(P ⊓ Subgroup.centralizer ({x} : Set G)))
    (h2CM : 2 ≤ CFSG.Open.pRank p
      (M ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)))
    (hP'centA0 : P ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers x : Set G))
    (hxcomm : ⁅P ⊓ Subgroup.centralizer ({x} : Set G),
      (Subgroup.center ↥Q).map Q.subtype⁆ ≠ ⊥) :
    False := by
  have hA0card : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
  have hoTwo : CFSG.Open.pCoreOf 2 J ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono
      (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))
  have hB0 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hA0card]; norm_num)
  have hA0NJ : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set G) :=
    hA0Q.trans (c.choice.Q_le_normalizer_J c.pre c.nine)
  have hP'M_cent : P ⊓ Subgroup.centralizer ({x} : Set G) ≤
      M ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    fun y hy => ⟨(inf_le_left.trans hPsylow.le).trans (Subgroup.map_subtype_le _) hy,
      hP'centA0 hy⟩
  obtain ⟨hA_norm, hxcomm'⟩ :=
    plane_element_A_normalizes c h142 hQ₀C hxQ₀ hQP hxcomm
  have hsolv : CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) :=
    h145 H E Q J c.choice c.typeA p hp (Subgroup.zpowers x) hA0Q hA0card h2CM hA0J
      (Or.inr ⟨P ⊓ Subgroup.centralizer ({x} : Set G),
        hP'M_cent, hP'p, hA_norm, hxcomm'⟩)
  have hnot := not_isPSolvable_inf_centralizer (J := J) (B := Subgroup.zpowers x)
    c.isKComp.isQuasisimple (three_dvd_card_centerQuotient_of_isSL34Star c.isSL34Star)
    hB0 hA0NJ (hA0J.trans hoTwo)
  exact hnot (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
    hsolv (fun y hy => ⟨c.choice.J_comp.1 hy.1, hy.2⟩))

theorem CaseOneCtx.fourteenEight_one
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M) {p : ℕ} (hp : p ∈ sigmaSet G M) :
    CFSG.Open.pRank p (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1 := by
  classical
  set D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M with hDdef
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  by_contra hle
  have h2D : 2 ≤ CFSG.Open.pRank p D := by omega
  obtain ⟨P, hPsylow, hPM, hQP, hPA⟩ :=
    exists_sylow_not_centralizes c h142 h145 hp (by simpa [hDdef] using h2D)
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  obtain ⟨Q₀, hQ₀Q, -, hQ₀J, hAQ₀, hQ₀C, -, f, hfQ₀, hfJ⟩ := c.exists_Q₀ h142
  obtain ⟨x, hxQ₀, hxne, hx3, hxcomm⟩ :=
    exists_plane_element c h142 hQ₀Q hAQ₀ ⟨f, hfQ₀, hfJ⟩ hPsylow.le hQP hPA
  have hA0Q : Subgroup.zpowers x ≤ Q := (Subgroup.zpowers_le.mpr hxQ₀).trans hQ₀Q
  have hA0card : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hxne]
  have hA0J : ⁅Subgroup.zpowers x, J⁆ ≤ CFSG.Open.pCoreOf 2 J :=
    (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hxQ₀) le_rfl).trans hQ₀J
  have hoTwo : CFSG.Open.pCoreOf 2 J ≤ (CFSG.pPrimeCore 3 ↥J).map J.subtype := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact Subgroup.map_mono
      (CFSG.Quasithin.A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num))
  have hB0 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hA0card]; norm_num)
  have hA0NJ : Subgroup.zpowers x ≤ Subgroup.normalizer (J : Set G) :=
    hA0Q.trans (c.choice.Q_le_normalizer_J c.pre c.nine)
  have hP'p : IsPGroup p ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) :=
    IsPGroup.to_le (H := P ⊓ Subgroup.centralizer ({x} : Set G))
      hPsylow.isPGroup
      (show P ⊓ Subgroup.centralizer ({x} : Set G) ≤ P from inf_le_left)
  have hP'nc : ¬ IsCyclic ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) :=
    not_isCyclic_inf_centralizer_of_plane c h142 hQ₀C hxQ₀ hQP hxcomm
  have h2P' : 2 ≤ CFSG.Open.pRank p (P ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic
      hp_prime hp2 hP'p hP'nc
  have hcentEq : Subgroup.centralizer (Subgroup.zpowers x : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hP'centA0 : P ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [hcentEq]
    exact inf_le_right
  have hP'M : P ⊓ Subgroup.centralizer ({x} : Set G) ≤ M :=
    (inf_le_left.trans hPsylow.le).trans (Subgroup.map_subtype_le _)
  have h2CM : 2 ≤ CFSG.Open.pRank p
      (M ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) :=
    h2P'.trans (CFSG.SectionRank.pRank_mono hp_prime.one_lt
      (fun y hy => ⟨hP'M hy, hP'centA0 hy⟩))
  exact plane_element_contradiction c h142 h145 hp hQ₀C hxQ₀ hQP hPsylow hx3 hxne
    hA0Q hA0J hP'p h2CM hP'centA0 hxcomm

theorem CaseOneCtx.exists_sylow_D_le_centralizer
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M) {p : ℕ} (hp : p ∈ sigmaSet G M) :
    ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ∧
      P ≤ Subgroup.centralizer
        (((Subgroup.center ↥Q).map Q.subtype : Subgroup G) : Set G) := by
  set D : Subgroup G := CFSG.inSubgroup (CFSG.pPrimeCore 3) M with hDdef
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hDcop : ¬ 3 ∣ Nat.card D := by
    have hcard : Nat.card D = Nat.card (CFSG.pPrimeCore 3 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hMD : M ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        M (CFSG.pPrimeCore 3 ↥M) (CFSG.pPrimeCore_characteristic (p := 3)))
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    (c.choice.Q_le_M c.nine).trans hMD
  obtain ⟨P : Subgroup G, hPsylow, -, hQP⟩ :=
    CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime (q := 3) (r := p)
      Nat.prime_three hp_prime c.choice.sylow.isPGroup hQD hDcop (P := ⊥) bot_le
      IsPGroup.of_bot (by
        have h : Subgroup.normalizer (G := G) (⊥ : Subgroup G) = ⊤ := by
          rw [Subgroup.normalizer_eq_top_iff]
          exact inferInstance
        exact le_top.trans h.ge)
  have hPcyc : IsCyclic ↥P :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one hp2 hPsylow.le hPsylow.isPGroup
      (c.fourteenEight_one h142 h145 hp)
  have hder :=
    commutator_normalizer_le_centralizer
      P
  have hAeq : ⁅Q, Q⁆ = A := by
    rw [hAdef]
    exact (h142 H E Q J c.choice c.typeA).1.2.2.1
  have hA_le_CP : A ≤ Subgroup.centralizer (P : Set G) := by
    rw [← hAeq]
    exact (Subgroup.commutator_mono hQP hQP).trans hder
  refine ⟨P, hPsylow, ?_⟩
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hA_le_CP ha) y hy).symm

theorem pRank_sup_le_of_sylow_le {p : ℕ} (hp : p.Prime) {D C P : Subgroup G}
    (hCD : C ≤ Subgroup.normalizer (D : Set G))
    (hP : CFSG.ABGLocalTools.IsSylowOf p P D) (hPC : P ≤ C) :
    CFSG.Open.pRank p (D ⊔ C) ≤ CFSG.Open.pRank p C := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨S, hS, hPS⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (p := p) (K := C) (Q := P) hPC hP.isPGroup
  have hSC : S ≤ C := hS.le
  have hSCsup : S ≤ D ⊔ C := hSC.trans le_sup_right
  have hSnot : ¬ p ∣ S.relIndex C := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2
  have hDCnot : ¬ p ∣ C.relIndex (D ⊔ C) := by
    have hsup : C.relIndex (D ⊔ C) = (C ⊓ D).relIndex D := by
      rw [sup_comm]
      exact (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hCD).1
    have hDP : P ≤ C ⊓ D := fun x hx => ⟨hPC hx, hP.le hx⟩
    have hdvd : C.relIndex (D ⊔ C) ∣ P.relIndex D := by
      rw [hsup]
      exact Subgroup.relIndex_dvd_of_le_left D hDP
    have hPnot : ¬ p ∣ P.relIndex D := (CFSG.ABGLocalTools.isSylowOf_iff.mp hP).2.2
    intro h
    exact hPnot (h.trans hdvd)
  have hSsup : CFSG.ABGLocalTools.IsSylowOf p S (D ⊔ C) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hSCsup, hS.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S C (D ⊔ C) hSC le_sup_right]
    exact Nat.Prime.not_dvd_mul hp hSnot hDCnot
  have h1 : CFSG.Open.pRank p (D ⊔ C) = CFSG.Open.pRank p S :=
    (CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hp hSsup).symm
  have h2 : CFSG.Open.pRank p S = CFSG.Open.pRank p C :=
    CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow hp hS
  rw [h1, h2]

theorem not_sq_dvd_card_mulAut_of_elem {V : Type*} [Group V] [Finite V] {k p : ℕ}
    (hcomm : ∀ a b : V, a * b = b * a) (hpow : ∀ a : V, a ^ 3 = 1)
    (hcard : Nat.card V = 3 ^ k) (hk : k ≤ 3) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card (MulAut V) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 3) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
    CFSG.SectionRank.Ccomm.card_GL_zmod (p := 3) k]
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk3 with rfl | rfl | rfl | rfl
  · intro h
    have hle : p ^ 2 ≤ 1 := Nat.le_of_dvd (by norm_num) h
    have hp2 : 25 ≤ p ^ 2 := by nlinarith
    omega
  · rw [show (∏ i : Fin 1, (3 ^ 1 - 3 ^ (i : ℕ))) = 2 by decide]
    intro h
    have hle : p ^ 2 ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hp2 : 25 ≤ p ^ 2 := by nlinarith
    omega
  · rw [show (∏ i : Fin 2, (3 ^ 2 - 3 ^ (i : ℕ))) = 48 by decide]
    intro h
    have hle : p ^ 2 ≤ 48 := Nat.le_of_dvd (by norm_num) h
    have hp2 : 25 ≤ p ^ 2 := by nlinarith
    have hp_le : p ≤ 6 := by nlinarith
    interval_cases p
    · norm_num at h
    · norm_num at hp
  · rw [show (∏ i : Fin 3, (3 ^ 3 - 3 ^ (i : ℕ))) = 11232 by decide]
    intro h
    have hpdvd : p ∣ 11232 := by
      simpa using (pow_dvd_pow p (by norm_num : 1 ≤ 2)).trans h
    have hp13 : p = 13 := by
      have hfac : (11232 : ℕ) = 2 ^ 5 * 3 ^ 3 * 13 := by norm_num
      rw [hfac] at hpdvd
      rcases hp.dvd_mul.mp hpdvd with h | h
      · rcases hp.dvd_mul.mp h with h2 | h3
        · have h2' : p ∣ 2 := hp.dvd_of_dvd_pow h2
          have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'
          omega
        · have h3' : p ∣ 3 := hp.dvd_of_dvd_pow h3
          have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).mp h
    rw [hp13] at h
    norm_num at h

private theorem ker_conjNormal_le_sup {X : Type*} [Group X] [Finite X]
    {M A : Subgroup G} {Z₀ : Subgroup X} [Z₀.Normal] (π : ↥M →* X)
    (hπker : π.ker = CFSG.pPrimeCore 3 ↥M)
    (hAM : A ≤ M) (hA3 : IsPGroup 3 A)
    (hAbar_le : (A.subgroupOf M).map π ≤ Z₀) :
    ((MulAut.conjNormal (G := X) (H := Z₀)).comp π).ker.map M.subtype ≤
      (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
  intro x hxker
  obtain ⟨xM, hxMker, rfl⟩ := Subgroup.mem_map.mp hxker
  have hPnorm : (CFSG.pPrimeCore 3 ↥M).Normal := CFSG.pPrimeCore_normal
  have hfix : ∀ w : ↥Z₀,
      (MulAut.conjNormal (G := X) (H := Z₀)) (π xM) w = w := by
    intro w
    have h2 : (MulAut.conjNormal (G := X) (H := Z₀)) (π xM) = 1 := by
      simpa using hxMker
    rw [h2]
    rfl
  have hxcomm : ∀ b ∈ A, (xM : G)⁻¹ * (b * (xM : G) * b⁻¹) ∈
      CFSG.inSubgroup (CFSG.pPrimeCore 3) M := by
    intro b hb
    have hbM : b ∈ M := hAM hb
    have hbAbar : π ⟨b, hbM⟩ ∈ (A.subgroupOf M).map π :=
      Subgroup.mem_map.mpr ⟨⟨b, hbM⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hfixb := hfix ⟨π ⟨b, hbM⟩, hAbar_le hbAbar⟩
    have hqeq : π (xM * ⟨b, hbM⟩ * xM⁻¹) = π ⟨b, hbM⟩ := by
      have := congrArg Subtype.val hfixb
      simpa [MulAut.conjNormal_apply, mul_assoc] using this
    let c : ↥M := (xM * ⟨b, hbM⟩ * xM⁻¹) * ⟨b, hbM⟩⁻¹
    have hmem : c ∈ CFSG.pPrimeCore 3 ↥M := by
      have h1 : π c = 1 := by
        rw [show c = (xM * ⟨b, hbM⟩ * xM⁻¹) * ⟨b, hbM⟩⁻¹ from rfl, map_mul, hqeq]
        simpa using mul_inv_cancel (π ⟨b, hbM⟩)
      rw [← hπker]
      exact MonoidHom.mem_ker.mpr h1
    have hinv : c⁻¹ ∈ CFSG.pPrimeCore 3 ↥M := (CFSG.pPrimeCore 3 ↥M).inv_mem hmem
    have hconj : xM⁻¹ * c⁻¹ * (xM⁻¹)⁻¹ ∈ CFSG.pPrimeCore 3 ↥M :=
      hPnorm.conj_mem c⁻¹ hinv xM⁻¹
    have heq : xM⁻¹ * c⁻¹ * (xM⁻¹)⁻¹ = xM⁻¹ * ⟨b, hbM⟩ * xM * ⟨b, hbM⟩⁻¹ := by
      dsimp [c]
      group
    rw [heq] at hconj
    have hconj' : xM⁻¹ * (⟨b, hbM⟩ * xM * ⟨b, hbM⟩⁻¹) ∈ CFSG.pPrimeCore 3 ↥M := by
      simpa [mul_assoc] using hconj
    exact Subgroup.mem_map_of_mem M.subtype hconj'
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section14.mem_centralizer_sup_core_of_commute_mod
    (M := M) (B := A) (x := (xM : G)) xM.2 hAM hA3 hxcomm

private theorem center_omega_data {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hKn : K.Normal) (hKne : K ≠ ⊥) (hKp : IsPGroup 3 ↥K) :
    ∃ Z₀ : Subgroup X, Z₀.Normal ∧ Z₀ ≤ CFSG.Quasithin.centerOf K ∧
      IsElemAbelian 3 Z₀ ∧
      (∀ z ∈ CFSG.Quasithin.centerOf K, z ^ 3 = 1 → z ∈ Z₀) ∧
      3 ∣ Nat.card (CFSG.Quasithin.centerOf K) := by
  have hHnorm : (CFSG.Quasithin.centerOf K).Normal :=
    @CFSG.Quasithin.A1c.centerOf_normal X _ K hKn
  haveI : (CFSG.Quasithin.centerOf K).Normal := hHnorm
  have hHdvd : 3 ∣ Nat.card (CFSG.Quasithin.centerOf K) := by
    have hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    have hcNt : Nontrivial ↥(Subgroup.center ↥K) :=
      IsPGroup.center_nontrivial (p := 3) hKp
    have hcP : IsPGroup 3 ↥(Subgroup.center ↥K) :=
      IsPGroup.to_subgroup hKp (Subgroup.center ↥K)
    obtain ⟨n, hn, hcard⟩ := (IsPGroup.nontrivial_iff_card hcP).mp hcNt
    have hdvdC : 3 ∣ Nat.card ↥(Subgroup.center ↥K) := by
      rw [hcard]
      exact dvd_pow_self 3 (by omega)
    change 3 ∣ Nat.card ↥(K ⊓ Subgroup.centralizer (K : Set X))
    rw [CFSG.GroupTheory.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact hdvdC
  let S : Set X := {x | x ∈ CFSG.Quasithin.centerOf K ∧ x ^ 3 = 1}
  let Z₀ : Subgroup X := Subgroup.normalClosure S
  have hS_conj : ∀ g x : X, x ∈ S → g * x * g⁻¹ ∈ S := by
    intro g x hx
    refine ⟨hHnorm.conj_mem x hx.1 g, ?_⟩
    rw [conj_pow, hx.2, mul_one]
    exact mul_inv_cancel g
  have hZ₀eq : Z₀ = Subgroup.closure S :=
    CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant hS_conj
  have hcl_le_H : Subgroup.closure S ≤ CFSG.Quasithin.centerOf K :=
    (Subgroup.closure_le (CFSG.Quasithin.centerOf K)).mpr (fun y hy => hy.1)
  have hHcomm : ∀ x ∈ CFSG.Quasithin.centerOf K, ∀ y ∈ CFSG.Quasithin.centerOf K,
      x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp hx.2 y hy.1).symm
  have hZ₀ea : IsElemAbelian 3 Z₀ := by
    rw [hZ₀eq]
    refine ⟨⟨⟨fun x y => Subtype.ext (hHcomm x.1 (hcl_le_H x.2) y.1 (hcl_le_H y.2))⟩⟩, ?_⟩
    intro x hx
    exact CFSG.Quasithin.A1b.pow_eq_one_of_mem_closure_of_comm
      (S := S) (n := 3) (fun y hy => hy.2)
      (fun u hu v hv => hHcomm u (hcl_le_H hu) v (hcl_le_H hv)) hx
  refine ⟨Z₀, Subgroup.normalClosure_normal, hZ₀eq.le.trans hcl_le_H, hZ₀ea, ?_, hHdvd⟩
  intro z hzH hz3
  exact Subgroup.subset_normalClosure ⟨hzH, hz3⟩

private theorem pRank_conj_range_le_one {M : Subgroup G} {Z₀ : Subgroup (threeStar M)}
    {p : ℕ} [Z₀.Normal] (hZ₀ea : IsElemAbelian 3 Z₀)
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p
      ((MulAut.conjNormal (G := threeStar M) (H := Z₀)).comp
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).range ≤ 1 := by
  let qπ : ↥M →* threeStar M := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let f : ↥M →* MulAut ↥Z₀ := (MulAut.conjNormal (G := threeStar M) (H := Z₀)).comp qπ
  have hZ₀p : IsPGroup 3 Z₀ := hZ₀ea.isPGroup
  obtain ⟨k, hkcard⟩ := IsPGroup.iff_card.mp hZ₀p
  have hk3 : k ≤ 3 := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
      (H := (⊤ : Subgroup (threeStar M))) (E := Z₀) le_top hZ₀ea hkcard
    exact h.trans h3M
  have hnoAut : ¬ p ^ 2 ∣ Nat.card (MulAut ↥Z₀) :=
    not_sq_dvd_card_mulAut_of_elem (V := ↥Z₀) (k := k) (p := p)
      (fun a b => isMulCommutative_iff.mp hZ₀ea.1 a b)
      (fun a => Subtype.ext (hZ₀ea.2 a a.2)) hkcard hk3 hp hp5
  change CFSG.Open.pRank p f.range ≤ 1
  by_contra h
  have h2 : 2 ≤ CFSG.Open.pRank p f.range := by omega
  obtain ⟨E, hE, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt f.range
  have h1 : p ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p h2
  have h2dvd : Nat.card E ∣ Nat.card (MulAut ↥Z₀) := by
    simpa using Subgroup.card_dvd_of_le (hE.trans (le_top : f.range ≤ ⊤))
  exact hnoAut (h1.trans h2dvd)

private theorem pRank_sup_centralizer_le_one {M A : Subgroup G} {p : ℕ}
    (hp : p.Prime)
    (hS81 : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) ≤ 1)
    (hSylow : ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ∧
      P ≤ Subgroup.centralizer (A : Set G)) :
    CFSG.Open.pRank p ((M ⊓ Subgroup.centralizer (A : Set G)) ⊔
      CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ≤ 1 := by
  obtain ⟨P, hPsylow, hPC⟩ := hSylow
  have hMD : M ≤ Subgroup.normalizer
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map
        M (CFSG.pPrimeCore 3 ↥M) (CFSG.pPrimeCore_characteristic (p := 3)))
  have hCD : (M ⊓ Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M : Set G) := inf_le_left.trans hMD
  have hPC' : P ≤ M ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
    ⟨hPsylow.le.trans (Subgroup.map_subtype_le _) hx, hPC hx⟩
  have hbound : CFSG.Open.pRank p
      (CFSG.inSubgroup (CFSG.pPrimeCore 3) M ⊔
        (M ⊓ Subgroup.centralizer (A : Set G))) ≤
      CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) :=
    pRank_sup_le_of_sylow_le hp hCD hPsylow hPC'
  rw [sup_comm]
  exact hbound.trans hS81

private theorem pRank_conj_ker_le_one {M A : Subgroup G} {Z₀ : Subgroup (threeStar M)}
    {p : ℕ} [Z₀.Normal] (hAM : A ≤ M) (hA3 : IsPGroup 3 A)
    (hZ₀ea : IsElemAbelian 3 Z₀) (hAbar_le : threeStarImg M A ≤ Z₀)
    (hp : p ∈ sigmaSet G M)
    (h3M : CFSG.Open.pRank 3 (⊤ : Subgroup (threeStar M)) ≤ 3)
    (hp3 : p ≠ 3) (hrankM : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥M))
    (hS81 : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) ≤ 1)
    (hSylow : ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ∧
      P ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  have hp_prime : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp5 : 5 ≤ p := by
    by_contra h
    have hp_le : p ≤ 4 := by omega
    interval_cases p
    · norm_num at hp_prime
    · norm_num at hp_prime
    · exact hp2 rfl
    · exact hp3 rfl
    · norm_num at hp_prime
  let qπ : ↥M →* threeStar M := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)
  let f : ↥M →* MulAut ↥Z₀ := (MulAut.conjNormal (G := threeStar M) (H := Z₀)).comp qπ
  have hker_le : f.ker.map M.subtype ≤
      (M ⊓ Subgroup.centralizer (A : Set G)) ⊔ CFSG.inSubgroup (CFSG.pPrimeCore 3) M :=
    ker_conjNormal_le_sup (X := threeStar M) (M := M) (A := A) (Z₀ := Z₀)
      qπ (QuotientGroup.ker_mk' _) hAM hA3 hAbar_le
  have hrange : CFSG.Open.pRank p f.range ≤ 1 :=
    pRank_conj_range_le_one (M := M) (Z₀ := Z₀) hZ₀ea h3M hp_prime hp5
  have hker : 2 ≤ CFSG.Open.pRank p f.ker := by
    have hineq :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_top_le_pRank_ker_add_pRank_range
        (p := p) hp_prime f
    omega
  have hsup_le := pRank_sup_centralizer_le_one hp_prime hS81 hSylow
  have hmap : CFSG.Open.pRank p f.ker ≤ CFSG.Open.pRank p (f.ker.map M.subtype) :=
    CFSG.SectionRank.pRank_le_map hp_prime.one_lt M.subtype M.subtype_injective f.ker
  have hmono : CFSG.Open.pRank p (f.ker.map M.subtype) ≤ CFSG.Open.pRank p
      ((M ⊓ Subgroup.centralizer (A : Set G)) ⊔ CFSG.inSubgroup (CFSG.pPrimeCore 3) M) :=
    CFSG.SectionRank.pRank_mono hp_prime.one_lt hker_le
  omega

private theorem exists_centralizing_order_three
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T)
    {Z₀ : Subgroup (threeStar M)}
    (hHnorm : (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M))).Normal)
    (hZ₀mem : ∀ z ∈ CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M)),
      z ^ 3 = 1 → z ∈ Z₀)
    (hHdvd : 3 ∣ Nat.card
      (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M)))) :
    ∃ z ∈ Z₀, orderOf z = 3 ∧
      threeStarImg M Q ≤ Subgroup.centralizer ({z} : Set (threeStar M)) := by
  haveI : (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M))).Normal := hHnorm
  have hPbar : IsPGroup 3 (threeStarImg M Q) := by
    rw [threeStarImg]
    exact (c.choice.sylow.isPGroup.comap_subtype (K := M)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  have hPH : threeStarImg M Q ≤ Subgroup.normalizer
      (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M)) : Set (threeStar M)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHnorm]
    exact le_top
  obtain ⟨z, hzH, hzord, hzcent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer (p := 3) hPbar hPH hHdvd
  have hzQ : threeStarImg M Q ≤ Subgroup.centralizer ({z} : Set (threeStar M)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp hzcent y hy).symm
  exact ⟨z, hZ₀mem z hzH (by simpa [hzord] using pow_orderOf_eq_one z), hzord, hzQ⟩

private theorem exists_centerImg_le_omega
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    {Z₀ : Subgroup (threeStar M)}
    (hHnorm : (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M))).Normal)
    (hZ₀mem : ∀ z ∈ CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M)),
      z ^ 3 = 1 → z ∈ Z₀)
    (hHdvd : 3 ∣ Nat.card
      (CFSG.Quasithin.centerOf (CFSG.pCore 3 (threeStar M)))) :
    ∃ A : Subgroup G, A = (Subgroup.center ↥Q).map Q.subtype ∧
      threeStarImg M A ≤ Z₀ ∧ IsPGroup 3 A ∧ A ≤ M := by
  obtain ⟨z, hzZ₀, hzord, hzQ⟩ :=
    exists_centralizing_order_three c hHnorm hZ₀mem hHdvd
  set A : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hAdef
  have hAcard : Nat.card A = 3 := (h142 H E Q J c.choice c.typeA).1.2.2.2
  have hAM : A ≤ M :=
    (Subgroup.map_subtype_le _).trans (c.choice.Q_le_M c.nine)
  have hAQ : A ≤ Q := Subgroup.map_subtype_le _
  have hzAbar : z ∈ threeStarImg M A := c.mem_centerImg_of_centralizes h142 hzord hzQ
  have hAbar_card : Nat.card (threeStarImg M A) = 3 := by
    rw [card_threeStarImg_of_isPGroup (c.choice.sylow.isPGroup.to_le hAQ) hAM, hAcard]
  have hAbar_eq : threeStarImg M A = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers z)
      (K := threeStarImg M A) ?_ ?_).symm
    · exact Subgroup.zpowers_le.mpr hzAbar
    · rw [Nat.card_zpowers, hzord, hAbar_card]
  have hAbar_le_Z₀ : threeStarImg M A ≤ Z₀ := by
    rw [hAbar_eq]
    exact Subgroup.zpowers_le.mpr hzZ₀
  exact ⟨A, rfl, hAbar_le_Z₀, c.choice.sylow.isPGroup.to_le hAQ, hAM⟩

theorem CaseOneCtx.fourteenEight_two
    {M H E Q J R T : Subgroup G}
    (c : CaseOneCtx G M H E Q J R T) (h142 : FourteenTwoCaseOneAt M)
    (h145 : FourteenFiveCaseOneAt M) :
    CFSG.pCore 3 (threeStar M) = ⊥ := by
  classical
  obtain ⟨p, hp⟩ := c.choice.sigma_nonempty
  set K : Subgroup (threeStar M) := CFSG.pCore 3 (threeStar M) with hKdef
  by_contra hKne
  have hKn : K.Normal := by
    rw [hKdef]
    exact CFSG.pCore_normal (p := 3) (G := threeStar M)
  have hKp : IsPGroup 3 ↥K := by
    rw [hKdef]
    exact CFSG.pCore_isPGroup (p := 3) (G := threeStar M)
  obtain ⟨Z₀, hZ₀norm, -, hZ₀ea, hZ₀mem, hHdvd⟩ := center_omega_data hKn hKne hKp
  haveI : Z₀.Normal := hZ₀norm
  have hHnorm : (CFSG.Quasithin.centerOf K).Normal :=
    @CFSG.Quasithin.A1c.centerOf_normal (threeStar M) _ K hKn
  have hHdvd' : 3 ∣ Nat.card (CFSG.Quasithin.centerOf K) := hHdvd
  obtain ⟨A, hAdef, hAbar_le_Z₀, hA3, hAM⟩ :=
    exists_centerImg_le_omega c h142 (by simpa [hKdef] using hHnorm)
      (by simpa [hKdef] using hZ₀mem) (by simpa [hKdef] using hHdvd')
  have hp3 : p ≠ 3 := fun h3 => c.choice.hypCGen.not_mem_sigmaSet (h3 ▸ hp)
  have hrankM : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥M) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) M]
    exact c.choice.cstar.three_le_pRank_of_mem_sigmaSet c.choice.maxLocal hp
  have hS81 : CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 := by
    simpa [hAdef] using c.pRank_centralizer_center_le h142 h145 hp
  have hSylow : ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.inSubgroup (CFSG.pPrimeCore 3) M) ∧
      P ≤ Subgroup.centralizer (A : Set G) := by
    obtain ⟨P, hP, hPC⟩ := c.exists_sylow_D_le_centralizer h142 h145 hp
    exact ⟨P, hP, by simpa [hAdef] using hPC⟩
  exact pRank_conj_ker_le_one hAM hA3 hZ₀ea hAbar_le_Z₀ hp c.pRank_threeStar_le hp3
    hrankM hS81 hSylow
