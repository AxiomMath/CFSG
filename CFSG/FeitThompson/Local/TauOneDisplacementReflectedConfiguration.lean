module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Local.BetaPrimesSigmaCompatibility
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.InvariantComplementFittingSelfCentralizing
import CFSG.FeitThompson.Local.SinglePrimeOrbitFixedLine
import CFSG.FeitThompson.Local.MinimalPrimeCentralizerCounterexample
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.OddOrder.ComparisonWordFixedVector
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem inf_centralizer_commutator_eq_bot_of_coprime [Finite G] {V R : Subgroup G}
    (hR : R ≤ normalizer (V : Set G)) (hV : IsMulCommutative ↥V)
    (hcop : (Nat.card ↥R).Coprime (Nat.card ↥V)) :
    (⁅V, R⁆ : Subgroup G) ⊓ centralizer (R : Set G) = ⊥ := by
  set W : Subgroup G := V ⊔ R with hW
  have hVW : V ≤ W := le_sup_left
  have hRW : R ≤ W := le_sup_right
  have hWnorm : W ≤ normalizer (V : Set G) := sup_le le_normalizer hR
  have : (V.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWnorm
  have hcomm : (⁅V, R⁆ : Subgroup G) ≤ V := commutator_le_left_of_le_normalizer hR
  have key := inf_centralizer_inf_commutator_eq_bot (L := ↥W) (V.subgroupOf W) (R.subgroupOf W)
    (isMulCommutative_subgroupOf_of_isMulCommutative hV)
    (by rwa [natCard_subgroupOf hRW, natCard_subgroupOf hVW])
  set X : Subgroup G := (⁅V, R⁆ : Subgroup G) ⊓ centralizer (R : Set G) with hX
  have hXW : X ≤ W := (inf_le_left.trans hcomm).trans hVW
  have hsub : X.subgroupOf W ≤
      V.subgroupOf W ⊓ centralizer ((R.subgroupOf W : Subgroup ↥W) : Set ↥W)
      ⊓ ⁅V.subgroupOf W, R.subgroupOf W⁆ := by
    rw [commutator_subgroupOf hVW hRW, centralizer_subgroupOf hRW]
    exact le_inf (le_inf (Subgroup.subgroupOf_mono W (inf_le_left.trans hcomm))
      (Subgroup.subgroupOf_mono W (le_inf hXW inf_le_right)))
      (Subgroup.subgroupOf_mono W inf_le_left)
  have hdisj : Disjoint X W := Subgroup.subgroupOf_eq_bot.1 (le_bot_iff.1 (key ▸ hsub))
  simpa [inf_eq_left.2 hXW] using disjoint_iff.1 hdisj

theorem le_betaCore_of_mem_betaPrimes
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    {G : Type u} [Group G] [Finite G] {T P : Subgroup G}
    (hG : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G) (hT : IsCoatom T)
    (hHall : IsHallPiSubgroup (sigmaPrimes T) ((sigmaCore T).subgroupOf T))
    (hST : sigmaCore T ≤ (⁅T, T⁆ : Subgroup G))
    {p : ℕ} (hp : p.Prime) (hpβ : p ∈ betaPrimes ↥T) (hPT : P ≤ T) (hPcard : Nat.card ↥P = p) :
    P ≤ betaCore T := by
  obtain ⟨hle, hpi, hidx⟩ := isHallPiIn_betaCore h₃ hG hT hHall hST
  have hHallBeta : IsHallPiSubgroup (betaPrimes ↥T) ((betaCore T).subgroupOf T) := by
    refine ⟨isPiSubgroup_iff.2 fun s hs => hpi s ?_, fun s hs => hidx s ?_⟩
    · rwa [natCard_subgroupOf hle] at hs
    · rwa [index_subgroupOf] at hs
  have hPpi : IsPiSubgroup (betaPrimes ↥T) (P.subgroupOf T) := by
    refine isPiSubgroup_iff.2 fun s hs => ?_
    rw [natCard_subgroupOf hPT, hPcard, hp.primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hpβ
  have h1 := Subgroup.map_mono (f := T.subtype) (hHallBeta.le_of_isPiSubgroup hPpi)
  rwa [Subgroup.map_subgroupOf_eq_of_le hPT, Subgroup.map_subgroupOf_eq_of_le hle] at h1

theorem betaCore_le_alphaCoreIn {G : Type*} [Group G] [Finite G] (T : Subgroup G) :
    betaCore T ≤ CFSG.FeitThompson.Prep09.alphaCoreIn T := by
  rw [betaCore_eq_map_piCore,
    CFSG.FeitThompson.Prep09.alphaCoreIn_def, alphaCore_eq_piCore]
  exact Subgroup.map_mono (piCore_mono betaPrimes_subset_alphaPrimes)

theorem FTS_tau_one_displacement_reflected_configuration
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_tau_one_displacement_reflected_configuration.{u} := by
  intro G _ _ hG M hM E hEM hsd p r hp hr hpτ P hPE hPcard R hRCE hRcard q a hq V hVCent hVcard
    hRnormV hQne T hT hNT
  have hsimple := hG.isSimpleGroup
  have hG06 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hHallMof, -, -⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ M hM
  obtain ⟨hHallTof, -, hSTcomm⟩ :=
    haveI : Fintype G := Fintype.ofFinite G
    h₁ G ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩ T hT
  obtain ⟨hnonconj, hcent, himp⟩ :=
    h₄ G hG M hM E hEM hsd p (Or.inl hpτ) P (hPE.trans hEM) hPcard T hT hNT
  have hVS : V ≤ sigmaCore M := hVCent.trans inf_le_left
  have hVcP : V ≤ centralizer (P : Set G) := hVCent.trans inf_le_right
  have hVT : V ≤ T := (hVcP.trans (centralizer_le_normalizer _)).trans hNT
  have hRE : R ≤ E := hRCE.trans inf_le_left
  have hRcP : R ≤ centralizer (P : Set G) := hRCE.trans inf_le_right
  have hRT : R ≤ T := (hRcP.trans (centralizer_le_normalizer _)).trans hNT
  have hPT : P ≤ T := le_normalizer.trans hNT
  have hQV : (⁅V, R⁆ : Subgroup G) ≤ V := commutator_le_left_of_le_normalizer hRnormV
  have hQST : (⁅V, R⁆ : Subgroup G) ≤ ⁅sigmaCore M ⊓ T, M ⊓ T⁆ :=
    Subgroup.commutator_mono (le_inf hVS hVT) (le_inf (hRE.trans hEM) hRT)
  have hcommne : (⁅sigmaCore M ⊓ T, M ⊓ T⁆ : Subgroup G) ≠ ⊥ := fun h =>
    hQne (le_bot_iff.1 (hQST.trans h.le))
  obtain ⟨hpσT, hpβT'⟩ := himp hcommne
  have hpβT : p ∈ betaPrimes ↥T := hpβT' hpτ
  have hrτT : r ∈ tau1Primes T := by
    by_contra hcon
    have hR : R ≤ centralizer ((sigmaCore M ⊓ T : Subgroup G) : Set G) := by
      refine hcent R (le_inf hRE hRT) fun s hs => ?_
      rw [hRcard, hr.primeFactors, Finset.mem_singleton] at hs
      exact hs ▸ hcon
    have hbot : (⁅sigmaCore M ⊓ T, R⁆ : Subgroup G) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hR)
    exact hQne (le_bot_iff.1
      ((Subgroup.commutator_mono (le_inf hVS hVT) le_rfl).trans hbot.le))
  have hVne : V ≠ ⊥ := fun h => hQne (le_bot_iff.1 (hQV.trans h.le))
  have hane : a ≠ 0 := by
    rintro rfl
    exact hVne (Subgroup.card_eq_one.1 (by simpa using hVcard))
  have hqdvdV : q ∣ Nat.card ↥V := by rw [hVcard]; exact dvd_pow_self q hane
  have hqσM : q ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q (Nat.mem_primeFactors.2
      ⟨hq, hqdvdV.trans (Subgroup.card_dvd_of_le hVS), Nat.card_pos.ne'⟩)
  have hnc : ∀ g : G, MulAut.conj g • M ≠ T := by
    intro g hg
    refine hnonconj g⁻¹ ?_
    rw [← hg, CFSG.FeitThompson.Prep09.conjSub_def, inv_inv]
    exact Subgroup.toSubmonoid_inj.mp rfl
  have hqαT : q ∉ alphaPrimes ↥T :=
    Set.disjoint_left.1 (disjoint_sigmaPrimes_alphaPrimes_of_not_conj hG.not_isMulCommutative
      hG.odd_natCard hG.isSolvable_of_ne_top hM hT hnc) hqσM
  have hTM : T ≠ M := fun h =>
    hnonconj 1 (by rw [h, CFSG.FeitThompson.Prep09.conjSub_one])
  have hVab : IsMulCommutative ↥V := by
    by_contra hcon
    obtain ⟨M', -, huniq⟩ := h₂ G
      ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
      q a V hq (Nat.one_le_iff_ne_zero.2 hane) hVcard hcon
    exact hTM ((huniq T ⟨hT, hVT⟩).trans (huniq M ⟨hM, hVS.trans (sigmaCore_le M)⟩).symm)
  have hrσM : r ∉ sigmaPrimes M := by
    have h := hHallMof.2.notMem_of_mem_primeFactors_index
    rw [index_subgroupOf_left_eq hsd] at h
    exact h r (Nat.mem_primeFactors.2
      ⟨hr, hRcard ▸ Subgroup.card_dvd_of_le hRE, Nat.card_pos.ne'⟩)
  have hrq : r ≠ q := fun h => hrσM (h ▸ hqσM)
  have hcop : (Nat.card ↥R).Coprime (Nat.card ↥V) := by
    rw [hRcard, hVcard]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr hq).2 hrq)
  have hPA : P ≤ CFSG.FeitThompson.Prep09.alphaCoreIn T :=
    (le_betaCore_of_mem_betaPrimes h₃ hG06 hT hHallTof.2 hSTcomm hp hpβT hPT hPcard).trans
      (betaCore_le_alphaCoreIn T)
  have hPc : P ≤ centralizer ((R ⊔ ⁅V, R⁆ : Subgroup G) : Set G) :=
    (le_centralizer_iff.1 (sup_le hVcP hRcP)).trans (centralizer_le (SetLike.coe_subset_coe.2
      (sup_le (le_sup_right : R ≤ V ⊔ R) (hQV.trans le_sup_left))))
  have hPfix : P ≤ CFSG.FeitThompson.Prep09.centIn
      (CFSG.FeitThompson.Prep09.alphaCoreIn T)
      ((R ⊔ ⁅V, R⁆ : Subgroup G) : Set G) := le_inf hPA hPc
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPcard
    exact hp.one_lt.ne hPcard
  exact ⟨hnonconj, hpσT, hpβT, hrτT, hqσM, hqαT, hVab,
    le_normalizer_commutator_of_le_normalizer hRnormV,
    inf_centralizer_commutator_eq_bot_of_coprime hRnormV hVab hcop, hPfix,
    fun h => hPne (le_bot_iff.1 (h ▸ hPfix))⟩

end

end CFSG.FeitThompson.Proofs
