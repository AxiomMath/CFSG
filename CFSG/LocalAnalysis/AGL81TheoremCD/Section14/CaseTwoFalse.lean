module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoQuotient
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFrattini
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoElements
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoFrattiniSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KNormalRank
import CFSG.GroupTheory.PGroup.RankTwoCommute
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.GH74.GLS.C3.Layer3.A8Cover
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.Quasithin.Vol2.Ch11SecOE5B
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma caseTwo_factA {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : ¬ TypeA M H) (hB : TypeB M H) (h1453 : FourteenFiveThreeAt M)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11)))
    {u₁ u₂ : G} (hu₁Q : u₁ ∈ Q) (hu₂Q : u₂ ∈ Q) (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1)
    (hu₁1 : u₁ ≠ 1) (hu12 : Commute u₁ u₂)
    (hnotsolv : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G)))
    {p : ℕ} (hp : p ∈ sigmaSet G M) {u : G}
    (huU : u ∈ Subgroup.closure ({u₁, u₂} : Set G)) (hu1 : u ≠ 1) :
    CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUQ : Subgroup.closure ({u₁, u₂} : Set G) ≤ Q :=
    (Subgroup.closure_le Q).mpr (by
      rintro x (rfl | rfl)
      · exact hu₁Q
      · exact hu₂Q)
  have huQ : u ∈ Q := hUQ huU
  have hu3 : u ^ 3 = 1 :=
    CFSG.GH74.GLS.Layer3.pow_three_eq_one_of_mem_closure_pair hu12 hu₁3 hu₂3 huU
  have hAcard : Nat.card (Subgroup.zpowers u) = 3 := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have hne : orderOf u ≠ 1 := fun h1 => hu1 (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne
    · exact h3
  have hle : kSub 3 M H ⊓
      Subgroup.centralizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) ≤
      kSub 3 M H ⊓ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr huU))
  have hns : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G)) :=
    fun hs => hnotsolv
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hs hle)
  have hcentral : Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) =
      Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  simpa [hcentral] using FourteenFiveThreeAt.pRank_le_one (A := Subgroup.zpowers u) h1453 hpre
    hK hU hL h hA hB hp (Subgroup.zpowers_le.mpr huQ) hAcard hMbar hns

private lemma caseTwo_factA_quotient {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : ¬ TypeA M H) (hB : TypeB M H) (h1453 : FourteenFiveThreeAt M)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11)))
    {u₁ u₂ : G} (hu₁Q : u₁ ∈ Q) (hu₂Q : u₂ ∈ Q) (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1)
    (hu₁1 : u₁ ≠ 1) (hu12 : Commute u₁ u₂)
    (hnotsolv : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G)))
    (hu₁M : u₁ ∈ M) (hu₂M : u₂ ∈ M) {p : ℕ} (hp : p ∈ sigmaSet G M) {u : ↥M}
    (huU : u ∈ Subgroup.closure ({⟨u₁, hu₁M⟩, ⟨u₂, hu₂M⟩} : Set ↥M)) (hu1 : u ≠ 1) :
    CFSG.Open.pRank p ((CFSG.pPrimeCore 3 ↥M) ⊓
      Subgroup.centralizer ({u} : Set ↥M)) ≤ 1 := by
  classical
  have hp' : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have huG : (u : G) ∈ Subgroup.closure ({u₁, u₂} : Set G) := by
    have hle : Subgroup.closure ({⟨u₁, hu₁M⟩, ⟨u₂, hu₂M⟩} : Set ↥M) ≤
        (Subgroup.closure ({u₁, u₂} : Set G)).comap M.subtype := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    exact hle huU
  have hu1G : (u : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hA' := caseTwo_factA h hA hB h1453 hpre hK hU hL hMbar hu₁Q hu₂Q hu₁3 hu₂3 hu₁1 hu12
    hnotsolv hp huG hu1G
  have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp' M.subtype
    M.subtype_injective ((CFSG.pPrimeCore 3 ↥M) ⊓ Subgroup.centralizer ({u} : Set ↥M))
  have hle : (((CFSG.pPrimeCore 3 ↥M) ⊓
      Subgroup.centralizer ({u} : Set ↥M)).map M.subtype) ≤
      M ⊓ Subgroup.centralizer ({(u : G)} : Set G) := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨y.2, ?_⟩
    have hy' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg M.subtype hy')
  calc CFSG.Open.pRank p ((CFSG.pPrimeCore 3 ↥M) ⊓
        Subgroup.centralizer ({u} : Set ↥M))
      = CFSG.Open.pRank p (((CFSG.pPrimeCore 3 ↥M) ⊓
          Subgroup.centralizer ({u} : Set ↥M)).map M.subtype) := hmap.symm
    _ ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({(u : G)} : Set G)) :=
        CFSG.SectionRank.pRank_mono hp'.one_lt hle
    _ ≤ 1 := hA'

private lemma caseTwo_stepFour (hGL4 : KFactA9NotInvolvedGL4)
    {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    (hA : ¬ TypeA M H) (hB : TypeB M H) (h1453 : FourteenFiveThreeAt M)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hU : NineNineOneAt M) (hL : PLayerNotLeAt M)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11)))
    {u₁ u₂ : G} (hu₁Q : u₁ ∈ Q) (hu₂Q : u₂ ∈ Q) (hu₁3 : u₁ ^ 3 = 1) (hu₂3 : u₂ ^ 3 = 1)
    (hu₁1 : u₁ ≠ 1) (hu12 : Commute u₁ u₂) (hu2z : u₂ ∉ Subgroup.zpowers u₁)
    (hnotsolv : ¬ CFSG.HallHigman.IsPSolvable 3
      ↥(kSub 3 M H ⊓ Subgroup.centralizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G)))
    (hu₁M : u₁ ∈ M) (hu₂M : u₂ ∈ M) {p : ℕ} (hp : p ∈ sigmaSet G M) (hp5 : 5 ≤ p)
    {n : ℕ} (hn : 9 ≤ n)
    (e : ↥(oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M))) ≃*
      alternatingGroup (Fin n)) :
    CFSG.Open.pRank p (CFSG.pPrimeCore 3 ↥M) ≤ 1 ∧
      (p ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥M) →
        p ∣ Nat.card ↥((CFSG.pPrimeCore 3 ↥M) ⊓
          Subgroup.centralizer ({(⟨u₁, hu₁M⟩ : ↥M)} : Set ↥M))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let Lb : Subgroup (↥M ⧸ O) := oPPrimeHull 3 (⊤ : Subgroup (↥M ⧸ O))
  haveI : O.Normal := CFSG.pPrimeCore_normal
  have hO3 : ¬ 3 ∣ Nat.card ↥O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥M))
  have h3 : ∀ x : ↥M ⧸ O, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Lb := by
    intro x hx
    exact Subgroup.subset_closure ⟨trivial, hx⟩
  have hu₁3M : (⟨u₁, hu₁M⟩ : ↥M) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hu₁3
  have hu₂3M : (⟨u₂, hu₂M⟩ : ↥M) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hu₂3
  have hu12M : Commute (⟨u₁, hu₁M⟩ : ↥M) (⟨u₂, hu₂M⟩ : ↥M) := by
    rw [commute_iff_eq]
    apply Subtype.ext
    simpa using hu12.eq
  have hu₁1M : (⟨u₁, hu₁M⟩ : ↥M) ≠ 1 := by
    intro h1
    exact hu₁1 (by simpa using congrArg Subtype.val h1)
  have hu2zM : (⟨u₂, hu₂M⟩ : ↥M) ∉ Subgroup.zpowers (⟨u₁, hu₁M⟩ : ↥M) := by
    intro hmem
    apply hu2z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hrank : ∀ u ∈ Subgroup.closure
      ({(⟨u₁, hu₁M⟩ : ↥M), (⟨u₂, hu₂M⟩ : ↥M)} : Set ↥M), u ≠ 1 →
      CFSG.Open.pRank p (O ⊓ Subgroup.centralizer ({u} : Set ↥M)) ≤ 1 := by
    intro u huU hu1
    exact caseTwo_factA_quotient h hA hB h1453 hpre hK hU hL hMbar hu₁Q hu₂Q hu₁3 hu₂3 hu₁1 hu12
      hnotsolv hu₁M hu₂M hp huU hu1
  have hres := pRank_le_one_of_alternating hGL4 hp' hp5 O hO3 Lb h3 hn e
    hu₁3M hu₂3M hu12M hu₁1M hu2zM hrank
  simpa [O, Lb] using hres

private lemma caseTwo_stepFive {M H E Q J : Subgroup G} (h : S14Choice G M H E Q J)
    {p : ℕ} (hp : p ∈ sigmaSet G M)
    (hO : CFSG.Open.pRank p (CFSG.pPrimeCore 3 ↥M) ≤ 1)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11))) :
    p = 5 ∧ 5 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥M) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp' : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h3 => h.hypCGen.not_mem_sigmaSet (h3 ▸ hp)
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp' hp2 hp3
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let Y := ↥M ⧸ O
  have hOle : CFSG.Open.pRank p O ≤ 1 := by simpa [O] using hO
  have hpM_eq : CFSG.Open.pRank p (⊤ : Subgroup ↥M) = CFSG.Open.pRank p M := by
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp' M.subtype
      M.subtype_injective (⊤ : Subgroup ↥M)
    rw [Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  have hineq : CFSG.Open.pRank p (⊤ : Subgroup ↥M) ≤
      CFSG.Open.pRank p O + CFSG.Open.pRank p (⊤ : Subgroup Y) := by
    have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_add_pRank_map (p := p) hp' O
      (⊤ : Subgroup ↥M)
    have htop : (⊤ : Subgroup ↥M).map (QuotientGroup.mk' O) = ⊤ := by
      rw [Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective O)
    rwa [top_inf_eq, htop] at h
  have h3M : 3 ≤ CFSG.Open.pRank p M :=
    h.cstar.three_le_pRank_of_mem_sigmaSet h.maxLocal hp
  have hYdvd : Nat.card Y ∣ Nat.factorial 11 :=
    card_dvd_factorial_eleven_of_nonempty (Y := Y) hMbar
  have hY2 : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 :=
    (pRank_top_le_two_of_card_dvd_factorial hp' hp5 hYdvd).1
  have hineqM : CFSG.Open.pRank p M ≤
      CFSG.Open.pRank p O + CFSG.Open.pRank p (⊤ : Subgroup Y) := by
    rw [← hpM_eq]
    exact hineq
  have hYeq : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by omega
  have hp_eq : p = 5 := (pRank_top_le_two_of_card_dvd_factorial hp' hp5 hYdvd).2 hYeq
  have hsum : 3 ≤ CFSG.Open.pRank p O + CFSG.Open.pRank p (⊤ : Subgroup Y) :=
    h3M.trans hineqM
  have hOpos : 1 ≤ CFSG.Open.pRank p O := by omega
  have hpdvd : p ∣ Nat.card ↥O := by
    obtain ⟨E, hEO, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp'.one_lt O
    have hpE : p ∣ Nat.card ↥E := by
      rw [hEcard]
      exact dvd_pow_self p (by omega)
    exact hpE.trans (Subgroup.card_dvd_of_le hEO)
  exact ⟨hp_eq, by simpa [O] using hp_eq ▸ hpdvd⟩

private lemma caseTwo_normalizer_inf {M : Subgroup G} {u₁M yM : ↥M}
    (hycomm : yM * u₁M = u₁M * yM) :
    yM ∈ Subgroup.normalizer
      ((CFSG.pPrimeCore 3 ↥M) ⊓ Subgroup.centralizer ({u₁M} : Set ↥M) : Set ↥M) := by
  classical
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let C : Subgroup ↥M := Subgroup.centralizer ({u₁M} : Set ↥M)
  have hyO : yM ∈ Subgroup.normalizer (O : Set ↥M) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top yM
  have hyC : yM ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hycomm
  have hyCN : yM ∈ Subgroup.normalizer (C : Set ↥M) := Subgroup.le_normalizer hyC
  simpa [O, C] using
    (Subgroup.inf_normalizer_le_normalizer_inf (H := O) (K := C) ⟨hyO, hyCN⟩)

private lemma caseTwo_stepSix {M : Subgroup G} {u₁M yM : ↥M}
    (hW5 : 5 ∣ Nat.card ↥((CFSG.pPrimeCore 3 ↥M) ⊓
      Subgroup.centralizer ({u₁M} : Set ↥M)))
    (hyN : yM ∈ Subgroup.normalizer
      ((CFSG.pPrimeCore 3 ↥M) ⊓ Subgroup.centralizer ({u₁M} : Set ↥M) : Set ↥M))
    (hyord : orderOf yM = 5) (hycomm : yM * u₁M = u₁M * yM)
    (hynot : (yM : G) ∉ (CFSG.pPrimeCore 3 ↥M).map M.subtype) :
    2 ≤ CFSG.Open.pRank 5 (M ⊓ Subgroup.centralizer ({(u₁M : G)} : Set G)) := by
  classical
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let C : Subgroup ↥M := Subgroup.centralizer ({u₁M} : Set ↥M)
  let W : Subgroup ↥M := O ⊓ C
  have hW5' : 5 ∣ Nat.card ↥W := by simpa [O, C, W] using hW5
  have hyN' : yM ∈ Subgroup.normalizer (W : Set ↥M) := by simpa [O, C, W] using hyN
  let P : Subgroup ↥M := Subgroup.zpowers yM
  have hPcard : Nat.card ↥P = 5 := by
    rw [show P = Subgroup.zpowers yM from rfl, Nat.card_zpowers, hyord]
  have hP5 : IsPGroup 5 P := IsPGroup.of_card (n := 1) (by simpa using hPcard)
  have hPW : P ≤ Subgroup.normalizer (W : Set ↥M) := Subgroup.zpowers_le.mpr hyN'
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨z, hzW, hzord, hzcent⟩ :=
    CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hP5 hPW hW5'
  have hzy : Commute yM z :=
    Subgroup.mem_centralizer_iff.mp hzcent yM (Subgroup.mem_zpowers yM)
  have hyH : (yM : G) ∈ M ⊓ Subgroup.centralizer ({(u₁M : G)} : Set G) := by
    refine ⟨yM.2, ?_⟩
    change (yM : G) ∈ Subgroup.centralizer ({(u₁M : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg Subtype.val hycomm
  have hzC : z ∈ C := hzW.2
  have hzH : (z : G) ∈ M ⊓ Subgroup.centralizer ({(u₁M : G)} : Set G) := by
    refine ⟨z.2, ?_⟩
    change (z : G) ∈ Subgroup.centralizer ({(u₁M : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC
    simpa using congrArg Subtype.val hzC
  have hzyG : Commute (yM : G) (z : G) :=
    (commute_iff_eq _ _).mpr (by simpa using congrArg Subtype.val hzy)
  have hzy_not : (z : G) ∉ Subgroup.zpowers (yM : G) := by
    intro hmem
    have hzO : (z : G) ∈ (O : Subgroup ↥M).map M.subtype :=
      Subgroup.mem_map_of_mem M.subtype hzW.1
    have hle : Subgroup.zpowers (z : G) ≤ (O : Subgroup ↥M).map M.subtype :=
      Subgroup.zpowers_le.mpr hzO
    have hcard : Nat.card ↥(Subgroup.zpowers (z : G)) =
        Nat.card ↥(Subgroup.zpowers (yM : G)) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_coe,
        Subgroup.orderOf_coe, hzord, hyord]
    have heq : Subgroup.zpowers (z : G) = Subgroup.zpowers (yM : G) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) (le_of_eq hcard.symm)
    have hyz : (yM : G) ∈ Subgroup.zpowers (z : G) :=
      heq ▸ Subgroup.mem_zpowers (yM : G)
    exact hynot (hle hyz)
  exact CFSG.GroupTheory.two_le_pRank_of_commute hyH hzH
    (by rw [Subgroup.orderOf_coe, hyord]) (by rw [Subgroup.orderOf_coe, hzord])
    hzyG hzy_not

theorem caseTwoFalse_of {M : Subgroup G} (hpre : PreambleTypes M) (hU : NineNineOneAt M)
    (hL : PLayerNotLeAt M)
    (hKF : KFactA11GammaTwoSet) (h514 : FiveFourteenA11Use) (h525 : FiveTwentyFiveS11Use)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) (h73 : SevenThreeInput)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (h1453 : FourteenFiveThreeAt M) (hGL4 : KFactA9NotInvolvedGL4) : CaseTwoFalse M := by
  intro H E Q J h hA hB
  obtain ⟨h2, rfl⟩ := h.caseTwo hpre hA hB
  have hK : KNormalAt M :=
    kNormalAt_of_preamble hpre hU hL
  obtain ⟨n, hn, ⟨e⟩, hMbar⟩ :=
    h.caseTwo_quotient hA h2 hpre hK hU hL hKF h514 h525 hX h73 h711
  obtain ⟨u₁, u₂, y, hu₁Q, hu₂Q, hu₁3, hu₂3, hu₁1, hu12, hu2z, hnotsolv, hyM, hyord,
    hcomm_uy, hynot⟩ := h.exists_caseTwo_elements h2 hK hU hL hKF
  have hQleM : Q ≤ M := h.Q_le_M hU
  have hu₁M : u₁ ∈ M := hQleM hu₁Q
  have hu₂M : u₂ ∈ M := hQleM hu₂Q
  obtain ⟨p, hp⟩ := h.sigma_nonempty
  have hp' : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p hp.1
  have hp3 : p ≠ 3 := fun h3 => h.hypCGen.not_mem_sigmaSet (h3 ▸ hp)
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp' hp2 hp3
  have hn9 : 9 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hstep4 := caseTwo_stepFour hGL4 h hA hB h1453 hpre hK hU hL hMbar hu₁Q hu₂Q hu₁3 hu₂3
    hu₁1 hu12 hu2z hnotsolv hu₁M hu₂M hp hp5 hn9 e
  obtain ⟨hp_eq, h5dvdO⟩ := caseTwo_stepFive h hp hstep4.1 hMbar
  let O : Subgroup ↥M := CFSG.pPrimeCore 3 ↥M
  let u₁M : ↥M := ⟨u₁, hu₁M⟩
  let yM : ↥M := ⟨y, hyM⟩
  let W : Subgroup ↥M := O ⊓ Subgroup.centralizer ({u₁M} : Set ↥M)
  have hp_dvdO : p ∣ Nat.card ↥O := by simpa [O] using hp_eq.symm ▸ h5dvdO
  have hp_dvdW : p ∣ Nat.card ↥W := by
    have h := hstep4.2 hp_dvdO
    simpa [O, W, u₁M] using h
  have h5dvdW : 5 ∣ Nat.card ↥W := by simpa [hp_eq] using hp_dvdW
  have hycommM : yM * u₁M = u₁M * yM := by
    apply Subtype.ext
    exact hcomm_uy.eq.symm
  have hyordM : orderOf yM = 5 := by
    rw [← Subgroup.orderOf_coe yM]
    simpa [yM] using hyord
  have hyN := caseTwo_normalizer_inf (M := M) (u₁M := u₁M) (yM := yM) hycommM
  have h2rank : 2 ≤ CFSG.Open.pRank 5 (M ⊓ Subgroup.centralizer ({u₁} : Set G)) :=
    caseTwo_stepSix (M := M) (u₁M := u₁M) (yM := yM) h5dvdW hyN hyordM hycommM
      (by simpa [yM] using hynot)
  have h5mem : 5 ∈ sigmaSet G M := hp_eq.symm ▸ hp
  have hle1 : CFSG.Open.pRank 5 (M ⊓ Subgroup.centralizer ({u₁} : Set G)) ≤ 1 :=
    caseTwo_factA h hA hB h1453 hpre hK hU hL hMbar hu₁Q hu₂Q hu₁3 hu₂3 hu₁1 hu12 hnotsolv h5mem
      (Subgroup.subset_closure (by simp)) hu₁1
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
