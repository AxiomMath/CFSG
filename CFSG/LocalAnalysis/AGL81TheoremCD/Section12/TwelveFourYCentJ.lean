module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveCtxOrbit
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.DResidualSimple
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.AutSymThreeSUThreeTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34NoRem
import CFSG.LocalAnalysis.AGLEmbedding.SUThreeTwoDeterminedHolds
import CFSG.CGT.PushingUpLit.EightOneWindowJS
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeKPart
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.Quasithin.H13.NQCoreWholeModuleFrattini
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly (InCatalog)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L : Subgroup G}

private theorem schreierSections_of_cZero {I : Subgroup G}
    (hS : SchreierFor InCatalog) (h : TwelveCtx G M p Q H)
    (hL : L ∈ weakBlockSet M H) (hI : IsCZeroMember (H ⊓ L) I) :
    CFSG.ComponentClassification.LBalance.SchreierSections ↥I := by
  have hI_le_M : I ≤ M := hI.le.trans (inf_le_right.trans hL.1.le)
  let : IsSimpleGroup G := h.cstar.simple
  have hKGroup : CFSG.Open.IsKGroup ↥M :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper h.cstar.kProper
      (CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top h.cstar.nonab M h.maxLocal.1)
  have hSchM : CFSG.ComponentClassification.LBalance.SchreierSections ↥M :=
    CFSG.ComponentClassification.LBalance.SchreierSections.of_isKGroup
      (fun S _ _ _ hnc hcat => hS S hnc hcat) hKGroup
  exact hSchM.of_injective (Subgroup.inclusion hI_le_M)
    (Subgroup.inclusion_injective hI_le_M)

omit [Finite G] in
private theorem outer_solvable_of_center_quotient {I : Subgroup G}
    (hSchI : CFSG.ComponentClassification.LBalance.SchreierSections ↥I)
    (hQ : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I)) :
    Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ((↥I ⧸ CFSG.pCore 2 ↥I) ⧸
          Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I))) := by
  let f : ↥(⊤ : Subgroup ↥I) →*
      ((↥I ⧸ CFSG.pCore 2 ↥I) ⧸
        Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I)) :=
    (QuotientGroup.mk' (Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I))).comp
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp Subgroup.topEquiv.toMonoidHom)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨q, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I)) x
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) q
    exact ⟨Subgroup.topEquiv.symm i, by simp [f]⟩
  let : IsSimpleGroup ((↥I ⧸ CFSG.pCore 2 ↥I) ⧸
      Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I)) := hQ.2.1
  exact hSchI.outer_solvable (⊤ : Subgroup ↥I) hQ.2.2 f hf

private theorem outer_solvable_of_perfect_cZero {I : Subgroup G}
    (hS : SchreierFor InCatalog) (h : TwelveCtx G M p Q H)
    (hL : L ∈ weakBlockSet M H) (hI : IsCZeroMember (H ⊓ L) I)
    (hcomp : IsTwoPrimeComponent I I) :
    Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥I ⧸ CFSG.pCore 2 ↥I)) := by
  have hSchI := schreierSections_of_cZero hS h hL hI
  have hbarM : CFSG.AGLEmbedding.barM I I = ⊤ := by
    unfold CFSG.AGLEmbedding.barM
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, QuotientGroup.range_mk']
  have hQ : CFSG.IsQuasisimple (↥I ⧸ CFSG.pCore 2 ↥I) := by
    have h1 : CFSG.Open.IsQuasisimple ↥(CFSG.AGLEmbedding.barM I I) := hcomp.component.2.2
    rw [hbarM] at h1
    have h2 : CFSG.IsQuasisimple ↥(⊤ : Subgroup (↥I ⧸ CFSG.pCore 2 ↥I)) :=
      CFSG.Quasithin.A3.isQuasisimple_iff_open.2 h1
    exact h2.of_mulEquiv Subgroup.topEquiv.symm
  have hOutQZ := outer_solvable_of_center_quotient hSchI hQ
  let : Group.IsPerfect (↥I ⧸ CFSG.pCore 2 ↥I) := hQ.1
  let : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        ((↥I ⧸ CFSG.pCore 2 ↥I) ⧸
          Subgroup.center (↥I ⧸ CFSG.pCore 2 ↥I))) := hOutQZ
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient
    (↥I ⧸ CFSG.pCore 2 ↥I)

private theorem oPPrimeHull_le_normalizer_cZero {I : Subgroup G}
    (hd_prime : d.Prime) (hd5 : 5 ≤ d) (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L)
    (hY_le_N_HL : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (H ⊓ L : Set G))
    (hI : IsCZeroMember (H ⊓ L) I) :
    oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (I : Set G) := by
  have hY_le_N_O2 : oPPrimeHull d (H ⊓ M) ≤
      Subgroup.normalizer (CFSG.ComponentClassification.AS76b.oUpperTwo I : Set G) :=
    oPPrimeHull_le_normalizer_oUpperTwo hL.1 hm3 hB.order_three hd_prime hd5 hI
      (hB.three_dvd_oUpperTwo I hI)
  rcases hI.shape with hcomp | ⟨hO2, hSym⟩
  · have hIeq : CFSG.ComponentClassification.AS76b.oUpperTwo I = I :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.oUpperTwo_eq_self_of_perfect
        hcomp.perfect
    simpa [hIeq] using hY_le_N_O2
  · rw [oPPrimeHull, Subgroup.closure_le]
    rintro y ⟨hyHM, k, hk⟩
    have hyY : y ∈ oPPrimeHull d (H ⊓ M) := Subgroup.subset_closure ⟨hyHM, k, hk⟩
    have hyNHL : y ∈ Subgroup.normalizer (H ⊓ L : Set G) := hY_le_N_HL hyY
    have hyNO2 : y ∈ Subgroup.normalizer
        (CFSG.ComponentClassification.AS76b.oUpperTwo I : Set G) := hY_le_N_O2 hyY
    have hO2map : CFSG.ComponentClassification.AS76b.oUpperTwo
        (I.map (MulAut.conj y).toMonoidHom) =
        CFSG.ComponentClassification.AS76b.oUpperTwo I := by
      rw [← CFSG.AGLEmbedding.SUPair.map_oUpperTwo (MulAut.conj y).toMonoidHom I]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyNO2
    have hIy : I.map (MulAut.conj y).toMonoidHom = I := by
      exact (CFSG.LocalAnalysis.RankThreeTheoremC.NoRem.eq_of_oUpperTwo_eq_cZero
        CFSG.AGLEmbedding.SUDet.subnormalSUThreeTwoDetermined_holds
        hI (IsCZeroMember.map_conj hI hyNHL) ⟨hO2, hSym⟩
        (CFSG.LocalAnalysis.RankThreeTheoremC.NoRem.shape_map_conj ⟨hO2, hSym⟩ hyNHL)
        hO2map.symm).symm
    exact mem_normalizer_iff_map_conj_eq.mpr hIy

private theorem oPPrimeHull_le_normalizer_inf_and_jZero
    (hd_prime : d.Prime) (hd5 : 5 ≤ d) (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L) :
    (oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (H ⊓ L : Set G)) ∧
      (oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (jZero H L : Set G)) := by
  have hY_le_N_L : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (L : Set G) :=
    oPPrimeHull_le_normalizer_of_isTwoPrimeComponent hL.1 hm3 hB.order_three
      hd_prime hd5 inf_le_right
  have hY_le_N_HL : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (H ⊓ L : Set G) :=
    (le_inf ((oPPrimeHull_le d _).trans inf_le_left |>.trans Subgroup.le_normalizer)
      hY_le_N_L).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact ⟨hY_le_N_HL, hY_le_N_HL.trans (le_normalizer_jZero H L)⟩

omit [Finite G] in
private theorem jZero_eq_iSup_cZero (H L : Subgroup G) :
    jZero H L = ⨆ i : {I // I ∈ cZero (H ⊓ L)}, (i : Subgroup G) := by
  rw [show jZero H L = ⨆ I ∈ cZero (H ⊓ L), I from rfl]
  exact iSup_subtype' (p := fun I : Subgroup G => I ∈ cZero (H ⊓ L))
    (f := fun I : Subgroup G => fun _ => I)

private theorem perfect_cZero_not_dvd_quotient_card {I : Subgroup G}
    (hD : TwelveThreeData M p H d) (hJX : jOne H L ≤ xSub p M H)
    (hI : IsCZeroMember (H ⊓ L) I) (hcomp : IsTwoPrimeComponent I I) :
    ¬ d ∣ Nat.card (↥I ⧸ CFSG.pCore 2 ↥I) := by
  intro hdiv
  have hIeq : CFSG.ComponentClassification.AS76b.oUpperTwo I = I :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.oUpperTwo_eq_self_of_perfect
      hcomp.perfect
  have hIleJ : I ≤ jOne H L := by
    simpa [hIeq] using IsCZeroMember.oUpperTwo_le_jOne hI
  have hIX : I ≤ xSub p M H := hIleJ.trans hJX
  exact hD.common.xSub_dPrime
    ((hdiv.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥I))).trans
      (Subgroup.card_dvd_of_le hIX))

private theorem perfect_member_commutator {I : Subgroup G}
    (hS : SchreierFor InCatalog) (h : TwelveCtx G M p Q H)
    (hd_prime : d.Prime) (hD : TwelveThreeData M p H d)
    (hL : L ∈ weakBlockSet M H) (hJX : jOne H L ≤ xSub p M H)
    (hI : IsCZeroMember (H ⊓ L) I) (hcomp : IsTwoPrimeComponent I I)
    (hY_le_N_I : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (I : Set G))
    (hY_perfect : ⁅oPPrimeHull d (H ⊓ M), oPPrimeHull d (H ⊓ M)⁆ =
      oPPrimeHull d (H ⊓ M))
    (y : G) (hyY : y ∈ oPPrimeHull d (H ⊓ M)) (k : ℕ) (hk : orderOf y = d ^ k) :
    ∀ x ∈ I, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 I := by
  let Qbar := ↥I ⧸ CFSG.pCore 2 ↥I
  let φ : ↥(oPPrimeHull d (H ⊓ M)) →* MulAut Qbar :=
    (CFSG.Quasithin.SteinbergCC.normalizerCoreQuotConj I).comp
      (Subgroup.inclusion hY_le_N_I)
  let : Group.IsPerfect ↥(oPPrimeHull d (H ⊓ M)) :=
    Subgroup.isPerfect_iff.mpr hY_perfect
  let : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Qbar) :=
    outer_solvable_of_perfect_cZero hS h hL hI hcomp
  obtain ⟨c, hc⟩ :=
    CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner φ ⟨y, hyY⟩
  have hpow : (⟨y, hyY⟩ : ↥(oPPrimeHull d (H ⊓ M))) ^ (d ^ k) = 1 := by
    ext
    simp [← hk]
  have hd1 : orderOf (φ ⟨y, hyY⟩) ∣ d ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hpow, map_one]
  have hd2 : orderOf (φ ⟨y, hyY⟩) ∣ Nat.card Qbar := by
    rw [hc]
    exact (orderOf_map_dvd (MulAut.conj : Qbar →* MulAut Qbar) c).trans
      (orderOf_dvd_natCard c)
  have hdQ : ¬ d ∣ Nat.card Qbar := perfect_cZero_not_dvd_quotient_card hD hJX hI hcomp
  have hcop : Nat.Coprime (d ^ k) (Nat.card Qbar) :=
    (hd_prime.coprime_pow_of_not_dvd hdQ).symm
  have h1 : orderOf (φ ⟨y, hyY⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hφy : φ ⟨y, hyY⟩ = 1 := orderOf_eq_one_iff.mp h1
  have hyN : y ∈ Subgroup.normalizer (I : Set G) := hY_le_N_I hyY
  exact (CFSG.Quasithin.H13.NQCore.normalizerCoreQuotConj_eq_one_iff
    (X := I) ⟨y, hyN⟩).mp hφy

omit [Finite G] in
private theorem commutator_le_of_generators_trivial {I : Subgroup G}
    (hY_le_N_I : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (I : Set G))
    (hgen : ∀ (y : G) (hyY : y ∈ oPPrimeHull d (H ⊓ M)) (k : ℕ),
      orderOf y = d ^ k →
        (CFSG.Quasithin.SteinbergCC.normalizerCoreQuotConj I)
          (Subgroup.inclusion hY_le_N_I ⟨y, hyY⟩) = 1)
    (b : G) (hb : b ∈ oPPrimeHull d (H ⊓ M)) :
    ⁅I, Subgroup.zpowers b⁆ ≤ pCoreOf 2 I := by
  let φ : ↥(oPPrimeHull d (H ⊓ M)) →* MulAut (↥I ⧸ CFSG.pCore 2 ↥I) :=
    (CFSG.Quasithin.SteinbergCC.normalizerCoreQuotConj I).comp
      (Subgroup.inclusion hY_le_N_I)
  let K : Subgroup G :=
    φ.ker.map (Subgroup.subtype (oPPrimeHull d (H ⊓ M)))
  have hK : oPPrimeHull d (H ⊓ M) ≤ K := by
    rw [oPPrimeHull, Subgroup.closure_le]
    rintro y ⟨hyHM, k, hk⟩
    have hyY : y ∈ oPPrimeHull d (H ⊓ M) := Subgroup.subset_closure ⟨hyHM, k, hk⟩
    exact ⟨⟨y, hyY⟩, MonoidHom.mem_ker.mpr (by simpa [φ] using hgen y hyY k hk), rfl⟩
  obtain ⟨x', hx'ker, hx'eq⟩ := hK hb
  have hφb : φ ⟨b, hb⟩ = 1 := by
    rw [← show x' = ⟨b, hb⟩ from Subtype.ext hx'eq]
    exact MonoidHom.mem_ker.mp hx'ker
  rw [Subgroup.commutator_le]
  intro x₀ hx₀ y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hbnY : b ^ n ∈ oPPrimeHull d (H ⊓ M) :=
    (oPPrimeHull d (H ⊓ M)).zpow_mem hb n
  have hbnN : b ^ n ∈ Subgroup.normalizer (I : Set G) := hY_le_N_I hbnY
  have hφbn : φ ⟨b ^ n, hbnY⟩ = 1 := by
    rw [show (⟨b ^ n, hbnY⟩ : ↥(oPPrimeHull d (H ⊓ M))) =
      (⟨b, hb⟩ : ↥(oPPrimeHull d (H ⊓ M))) ^ n by ext; simp, map_zpow, hφb, one_zpow]
  have hmem : b ^ n * x₀ * (b ^ n)⁻¹ * x₀⁻¹ ∈ pCoreOf 2 I :=
    (CFSG.Quasithin.H13.NQCore.normalizerCoreQuotConj_eq_one_iff
      (X := I) ((Subgroup.inclusion hY_le_N_I) ⟨b ^ n, hbnY⟩)).mp
      (by simpa [φ] using hφbn) x₀ hx₀
  have hcomm_eq : ⁅x₀, b ^ n⁆ = (b ^ n * x₀ * (b ^ n)⁻¹ * x₀⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [hcomm_eq]
  exact Subgroup.inv_mem _ hmem

private theorem member_commutator_le {I : Subgroup G}
    (hS : SchreierFor InCatalog) (h : TwelveCtx G M p Q H)
    (hd_prime : d.Prime) (hd5 : 5 ≤ d) (hD : TwelveThreeData M p H d)
    (hL : L ∈ weakBlockSet M H) (hJX : jOne H L ≤ xSub p M H)
    (hI : IsCZeroMember (H ⊓ L) I)
    (hY_le_N_I : oPPrimeHull d (H ⊓ M) ≤ Subgroup.normalizer (I : Set G))
    (hY_perfect : ⁅oPPrimeHull d (H ⊓ M), oPPrimeHull d (H ⊓ M)⁆ =
      oPPrimeHull d (H ⊓ M))
    (b : G) (hb : b ∈ oPPrimeHull d (H ⊓ M)) :
    ⁅I, Subgroup.zpowers b⁆ ≤ pCoreOf 2 I := by
  have hgen : ∀ (y : G) (hyY : y ∈ oPPrimeHull d (H ⊓ M)) (k : ℕ),
      orderOf y = d ^ k →
        (CFSG.Quasithin.SteinbergCC.normalizerCoreQuotConj I)
          (Subgroup.inclusion hY_le_N_I ⟨y, hyY⟩) = 1 := by
    intro y hyY k hk
    rcases hI.shape with hcomp | ⟨hO2, hSym⟩
    · exact (CFSG.Quasithin.H13.NQCore.normalizerCoreQuotConj_eq_one_iff
        (X := I) ⟨y, hY_le_N_I hyY⟩).mpr
        (perfect_member_commutator hS h hd_prime hD hL hJX hI hcomp hY_le_N_I
          hY_perfect y hyY k hk)
    · have hyN : y ∈ Subgroup.normalizer (I : Set G) := hY_le_N_I hyY
      have hpow : y ^ (d ^ k) = 1 := by
        rw [← hk]
        exact pow_orderOf_eq_one y
      have hmem : ∀ x ∈ I, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 I :=
        commutator_mem_pCoreOf_of_isSymThreeOrSUThreeTwo hSym hd_prime hd5 hyN hpow
      exact (CFSG.Quasithin.H13.NQCore.normalizerCoreQuotConj_eq_one_iff
        (X := I) ⟨y, hyN⟩).mpr hmem
  exact commutator_le_of_generators_trivial hY_le_N_I hgen b hb

theorem twelveFourYCentJ_of_twelveCtx (hS : SchreierFor InCatalog) (h : TwelveCtx G M p Q H)
    (hd : d ∈ sigmaSet G M) (hD : TwelveThreeData M p H d) (hA : TwelveFourStepA M d)
    (hL : L ∈ weakBlockSet M H) (hB : TwelveFourBlockFacts M H L) (hJX : jOne H L ≤ xSub p M H) :
    TwelveFourYCentJ M H L d := by
  classical
  have hd_prime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hd5 : 5 ≤ d := hA.2.2
  have hm3 : CFSG.Open.pRank 3 M ≤ 3 := hA.2.1
  have hY_perfect : ⁅oPPrimeHull d (H ⊓ M), oPPrimeHull d (H ⊓ M)⁆ =
      oPPrimeHull d (H ⊓ M) := by
    have : IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M))) := hD.common.y_simple
    exact commutator_eq_self_of_simple_modPrimeComplement_of_not_solvable hd_prime
      (CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631.oPPrimeHull_oPPrimeHull d (H ⊓ M))
      hD.common.y_nonsolvable
  obtain ⟨hY_le_N_HL, -⟩ := oPPrimeHull_le_normalizer_inf_and_jZero hd_prime hd5 hm3 hL hB
  intro b hb x hx
  set N : Subgroup G := pCoreOf 2 (jZero H L)
  have hJ0 := jZero_eq_iSup_cZero H L
  have hcomm : ⁅jZero H L, Subgroup.zpowers b⁆ ≤ N := by
    rw [hJ0]
    refine CFSG.CGT.PushingUpLit.EightOneWindow.commutator_iSup_le
      (K := jZero H L) (E := N) (X := Subgroup.zpowers b)
      (A := fun i : {I // I ∈ cZero (H ⊓ L)} => (i : Subgroup G)) ?_ ?_ ?_
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (jZero H L)
    · intro i
      exact IsCZeroMember.le_jZero i.2
    · rintro ⟨I, hI⟩
      have hsub : CFSG.Open.IsSubnormal I (jZero H L) := by
        have h := hI.subnormal.inf_of_le (jZero_le H L)
        rwa [inf_of_le_left (IsCZeroMember.le_jZero hI)] at h
      have hO2_le_N : pCoreOf 2 I ≤ N :=
        CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hsub
      have hY_le_N_I := oPPrimeHull_le_normalizer_cZero hd_prime hd5 hm3 hL hB hY_le_N_HL hI
      exact (member_commutator_le hS h hd_prime hd5 hD hL hJX hI hY_le_N_I hY_perfect
        b hb).trans hO2_le_N
  have hmem : ⁅b, x⁆ ∈ ⁅jZero H L, Subgroup.zpowers b⁆ := by
    have h1 : ⁅x, b⁆ ∈ ⁅jZero H L, Subgroup.zpowers b⁆ :=
      Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers b)
    rw [(commutatorElement_inv x b).symm]
    exact Subgroup.inv_mem _ h1
  exact hcomm hmem

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
