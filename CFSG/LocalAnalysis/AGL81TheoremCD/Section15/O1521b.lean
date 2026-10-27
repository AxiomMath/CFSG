module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S14Facts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KQuotFix
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.QuotientCentralizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

private theorem kSub_le_of_mem_quotientCentralizer {M E H : Subgroup G}
    (h : HypCGen G M 3 E H) (hK : KNormalAt M)
    (hOp : IsPGroup 2 ((CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype))
    {q : ℕ} (hqemb : CFSG.RankThree.PartOne.IsStronglyPEmbedded q M)
    (hq : q.Prime) (hq2 : q ≠ 2) {w : G} (hwH : w ∈ H) (hwM : w ∈ M)
    (hword : orderOf w = q)
    (hwX : w ∈ quotientCentralizer H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H))
      (kSub_le 3 M H) (hK 3 E H h)) :
    kSub 3 M H ≤ M := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let O : Subgroup G := (CFSG.pPrimeCore 3 ↥(kSub 3 M H)).map (kSub 3 M H).subtype
  have hOH : O ≤ H :=
    (Subgroup.map_subtype_le (CFSG.pPrimeCore 3 ↥(kSub 3 M H))).trans (kSub_le 3 M H)
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    (hK 3 E H h).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (K := CFSG.pPrimeCore 3 ↥(kSub 3 M H)))
  have hcop : Nat.Coprime q (Nat.card O) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.gen49e_coprime_card_two hq hq2 hOp
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hword
    exact hq.ne_one hword.symm
  have hwq : w ^ q = 1 := by
    rw [← hword]
    exact pow_orderOf_eq_one w
  intro k hk
  have hkH : k ∈ H := (kSub_le 3 M H) hk
  have hcomm : w * k * w⁻¹ * k⁻¹ ∈ O :=
    commutator_mem_map_of_mem_quotientCentralizer (CFSG.pPrimeCore 3 ↥(kSub 3 M H))
      (kSub_le 3 M H) (hK 3 E H h) hwX hk
  have hcomm' : k * w * k⁻¹ * w⁻¹ ∈ O := by
    simpa [mul_assoc] using O.inv_mem hcomm
  obtain ⟨o, hoO, c, -, hca, hoc⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.gen49e_mem_mul_centralizer hq hOH hHO hcop hwH hkH
      hword hcomm'
  have hcM : c ∈ M := by
    have hcCen : c ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hca.symm
    exact hqemb.centralizer_le hw1 hwq hwM hcCen
  have hoM : o ∈ M := h.pPrimeCore_map_le hK hoO
  rw [← hoc]
  exact M.mul_mem hoM hcM

theorem o1521bAt_of_s14
    {M : Subgroup G} (hC : CStarGen G) (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty)
    (hemb : ∀ q ∈ sigmaSet G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M)
    (hF : Section14.S14FactsAt M) : O1521bAt G M := by
  intro h3 E hEM hE hEc hΓ H hH2 hEH hHM q hqσ hqdiv
  rw [sigmaM_eq_sigmaSet] at h3 hqσ
  have hq : q.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime q hqσ.1
  have hq2 : q ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd q hqσ.1
  have hq3 : q ≠ 3 := fun hq3 => h3 (hq3 ▸ hqσ)
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    have h2 : 2 ≤ q := hq.two_le
    omega
  have h : HypCGen G M 3 E H :=
    hypCGen_of_isMaxTwoLocal hC hM hσ hEM hE hEc hΓ hH2 hEH hHM
  have hC3 : CaseThree M H := hF.three H h.mem_H2StarAll
  obtain ⟨A, hA, hNA⟩ := hF.normalizerSylowKLe 3 E H h
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ M)) q hqdiv
  set w : G := (x : G) with hwdef
  have hwH : w ∈ H := by simpa [hwdef] using x.2.1
  have hwM : w ∈ M := by simpa [hwdef] using x.2.2
  have hword : orderOf w = q := by
    rw [hwdef, Subgroup.orderOf_coe, hxord]
  have hαq : conjQuotAction H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H))
      (kSub_le 3 M H) (hF.normal 3 E H h) ⟨w, hwH⟩ ^ q = 1 := by
    have hpow : (⟨w, hwH⟩ : ↥H) ^ q = 1 := by
      apply Subtype.ext
      change w ^ q = 1
      rw [← hword]
      exact pow_orderOf_eq_one w
    rw [← map_pow, hpow, map_one]
  have hα1 :=
    HypCGen.conjQuotAction_eq_one_of_pow_eq_one h hC3 hF.normal hF.layer hA hNA
      (x := ⟨w, hwH⟩) hwM hq hq5 hαq
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  have hLN : K ≤ H := kSub_le 3 M H
  have hNL : H ≤ Subgroup.normalizer (K : Set G) := hF.normal 3 E H h
  have hwX : w ∈ quotientCentralizer H K N hLN hNL :=
    (mem_quotientCentralizer N hLN hNL).mpr
      ⟨⟨w, hwH⟩, rfl, by simpa [K, N] using hα1⟩
  have hOp : IsPGroup 2 (N.map K.subtype) := by
    simpa [K, N] using h.isPGroup_pPrimeCore_kSub hC3 hF.two
  have hKleM : K ≤ M :=
    kSub_le_of_mem_quotientCentralizer h hF.normal hOp (hemb q hqσ) hq hq2 hwH hwM hword hwX
  exact (not_kSub_le_of_not_pLayerIn_le (p := 3) (hF.layer 3 E H h)) hKleM

theorem o1521bGen_of_s14
    (hF : Section14.S14FactsGen) : O1521bGen :=
  fun G _ _ hC M hM hσ hemb => o1521bAt_of_s14 hC hM hσ hemb (hF G hC M hM hσ)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
