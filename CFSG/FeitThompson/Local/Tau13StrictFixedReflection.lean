module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.TauTwoFactorContainsPlaneRegularActions
import CFSG.FeitThompson.Local.TauOneHallFixedCentralizer
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05 (centralizerIn_eq)
open CFSG.FeitThompson.Prep09 (centIn_def)

universe u

theorem le_normalizer_of_le_isCyclic_of_le_normalizer {G : Type*} [Group G] [Finite G]
    {E A R : Subgroup G} (hA : IsCyclic ↥A) (hRA : R ≤ A) (hE : E ≤ normalizer (A : Set G)) :
    E ≤ normalizer (R : Set G) := by
  intro g hg
  rw [FreeCore.mem_normalizer_iff_map]
  have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
    (FreeCore.mem_normalizer_iff_map A g).1 (hE hg)
  refine eq_of_le_of_natCard_eq_of_isCyclic (A := A) ?_ hRA ?_
  · rw [← hAg]; exact Subgroup.map_mono hRA
  · exact (Nat.card_congr (R.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm

theorem normalizer_ne_top_of_natCard_prime {G : Type*} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnc : ¬ IsMulCommutative G) {R : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hcard : Nat.card ↥R = r) : normalizer (R : Set G) ≠ ⊤ := by
  intro h
  have hnorm : R.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact h
  rcases hs.eq_bot_or_eq_top_of_normal R with hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    exact hr.ne_one hcard.symm
  · have hG : Nat.card G = r := by
      rw [← hcard, ht]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    have hfr := Fact.mk hr
    exact hnc (@IsCyclic.isMulCommutative _ _ (isCyclic_of_prime_card hG))

theorem FNI_tau13_strict_fixed_reflection
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_tau13_strict_fixed_reflection.{u} := by
  intro G _ _ hG M E E₁ E₂ E₃ hfac p hp P hPE₁ hPcard r hr R hRcent hRcard hlt
  simp only [centralizerIn_eq] at hRcent hlt
  have hM : IsCoatom M := hfac.isSigmaComplement.isCoatom
  have hsd := hfac.isSigmaComplement.semidirect
  have hEM : E ≤ M := hsd.right_le
  have hamb04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb09 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hsplit : _root_.CFSG.FeitThompson.IsTauHallSplitting M E E₁ E₂ E₃ :=
    ⟨hfac.le_E₁, hfac.le_E₂, hfac.le_E₃, hfac.hall_E₁, hfac.hall_E₂, hfac.hall_E₃,
      hfac.semidirect_E, hfac.semidirect_E₂₁⟩
  have hsigma : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hsd⟩
  have hRE₃ : R ≤ E₃ := hRcent.trans inf_le_left
  have hRE : R ≤ E := hRE₃.trans hfac.le_E₃
  have hRne : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hRcard
    exact hr.ne_one hRcard.symm
  have hCRne : (sigmaCore M ⊓ centralizer (R : Set G) : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h] at hlt
    exact absurd hlt not_lt_bot
  have hE₂ : E₂ = ⊥ := by
    by_contra hne
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
      (show Nat.card ↥E₂ ≠ 1 from fun h => hne (Subgroup.card_eq_one.1 h))
    have hq2 : q ∈ tauTwoPrimes M :=
      mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf hfac.le_E₂ hfac.hall_E₂ hq hqd
    have hqE : q ∣ Nat.card ↥E := hqd.trans (Subgroup.card_dvd_of_le hfac.le_E₂)
    have hpd := FNI_sigma_complement_prime_data h₁ G hamb04 M E hsigma
    have hrank : elementaryAbelianPRank q ↥E = 2 := by
      rw [(hpd.2.1 q ⟨hq, hqE⟩).1, elementaryAbelianPRank_eq_two_of_mem_tauTwoPrimes hq2]
    have hmem : (2 : ℕ) ∈ elementaryAbelianRanks q ↥E := by
      have := elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥E) (p := q) hq.one_lt
      rwa [hrank] at this
    obtain ⟨H, ⟨f⟩⟩ := mem_elementaryAbelianRanks.1 hmem
    set A : Subgroup G := H.map E.subtype with hA
    have hAE : A ≤ E := Subgroup.map_subtype_le _
    have hplane : _root_.CFSG.FeitThompson.IsElementaryAbelianPlane q A :=
      ⟨(H.equivMapOfInjective E.subtype (Subgroup.subtype_injective E)).symm.trans f⟩
    have hout : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane q M A :=
      ⟨hM, hq, notMem_sigmaPrimes_of_mem_tauTwoPrimes hq2, hAE.trans hEM, hplane⟩
    have hreg := (FNI_sigma_complement_regular_factors h₂ h₃ h₄ G hamb04 q M A E E₁ E₂ E₃
      hout hsigma hAE hsplit).2
    obtain ⟨⟨x, hxR⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hRne
    have hx1' : x ≠ 1 := by simpa using hx1
    have hfree := hreg x hx1' (Or.inl (hRE₃ hxR))
    refine hCRne (le_bot_iff.1 ?_)
    rw [← hfree]
    exact inf_le_inf_left _ (centralizer_le (by simpa using hxR))
  refine ⟨hE₂, ?_⟩
  have hEnormR : E ≤ normalizer (R : Set G) :=
    le_normalizer_of_le_isCyclic_of_le_normalizer hfac.isCyclic_E₃ hRE₃
      hfac.semidirect_E.le_normalizer
  obtain ⟨T, hT, hNT⟩ := exists_isCoatom_ge_of_ne_top
    (normalizer_ne_top_of_natCard_prime hG.isSimpleGroup hG.not_isMulCommutative hr hRcard)
  have hET : E ≤ T := hEnormR.trans hNT
  refine ⟨T, hT, hNT, hET, ?_⟩
  have hrτ₃ : r ∈ tau3Primes M :=
    mem_of_dvd_natCard_of_isHallPiSubgroup_subgroupOf hfac.le_E₃ hfac.hall_E₃ hr
      (hRcard ▸ Subgroup.card_dvd_of_le hRE₃)
  have hRM : R ≤ M := hRE.trans hEM
  have htrans := h₆ G hamb09 M hM E hEM hsd r (Or.inr hrτ₃) R hRM hRcard T hT hNT
  have hCRJ : (sigmaCore M ⊓ centralizer (R : Set G) : Subgroup G) ≤ sigmaCore M ⊓ T :=
    le_inf inf_le_left
      (inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNT))
  have hPM : P ≤ M := (hPE₁.trans hfac.le_E₁).trans hEM
  have hPT : P ≤ T := (hPE₁.trans hfac.le_E₁).trans hET
  have hcomm : (⁅sigmaCore M ⊓ T, M ⊓ T⁆ : Subgroup G) ≠ ⊥ := by
    intro hb
    have hJcent : (sigmaCore M ⊓ T : Subgroup G) ≤ centralizer ((M ⊓ T : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hb
    have hJP : (sigmaCore M ⊓ T : Subgroup G) ≤ centralizer (P : Set G) :=
      hJcent.trans (centralizer_le (SetLike.coe_subset_coe.2 (le_inf hPM hPT)))
    have hle : (sigmaCore M ⊓ centralizer (R : Set G) : Subgroup G) ≤
        sigmaCore M ⊓ centralizer (P : Set G) :=
      le_inf inf_le_left (hCRJ.trans hJP)
    exact absurd (le_antisymm hlt.le hle) (by simpa using hlt.ne)
  obtain ⟨hrσ, -⟩ := htrans.2.2 hcomm
  refine ⟨hrσ, ?_⟩
  intro s hs
  by_contra hsT
  obtain ⟨hsp, hsdvd, -⟩ := Nat.mem_primeFactors.1 hs
  obtain ⟨y, hyE₁, hy⟩ := exists_mem_orderOf_eq_of_dvd hsp hsdvd
  set Y : Subgroup G := zpowers y with hY
  have hYE₁ : Y ≤ E₁ := zpowers_le.2 hyE₁
  have hYE : Y ≤ E := hYE₁.trans hfac.le_E₁
  have hYcard : Nat.card ↥Y = s := by rw [hY, Nat.card_zpowers, hy]
  have hYne : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hYcard
    exact hsp.ne_one hYcard.symm
  have hYcent : Y ≤ centralizer ((sigmaCore M ⊓ T : Subgroup G) : Set G) := by
    refine htrans.2.1 Y (le_inf hYE (hYE.trans hET)) ?_
    intro t ht
    rw [hYcard, hsp.primeFactors, Finset.mem_singleton] at ht
    exact ht ▸ hsT
  have hkey := FTS_tau_one_hall_fixed_centralizer h₁ h₅ h₆ G hamb09 M hM E hEM hsd E₁
    hfac.le_E₁ hfac.hall_E₁
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact (prime_of_mem_tau1Primes hp).ne_one hPcard.symm
  have hY' := hkey.2 Y hYE₁ hYne
  have hP' := hkey.2 P hPE₁ hPne
  rw [centIn_def, centIn_def] at hY' hP'
  have hCRY : (sigmaCore M ⊓ centralizer (R : Set G) : Subgroup G) ≤
      sigmaCore M ⊓ centralizer (Y : Set G) :=
    le_inf inf_le_left (hCRJ.trans (Subgroup.le_centralizer_iff.1 hYcent))
  have hle : (sigmaCore M ⊓ centralizer (R : Set G) : Subgroup G) ≤
      sigmaCore M ⊓ centralizer (P : Set G) := by
    rw [hP', ← hY']
    exact hCRY
  exact absurd (le_antisymm hlt.le hle) (by simpa using hlt.ne)

end

end CFSG.FeitThompson.Proofs
