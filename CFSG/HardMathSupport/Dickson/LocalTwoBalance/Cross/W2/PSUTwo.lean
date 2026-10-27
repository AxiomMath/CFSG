module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Count
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Inner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Outer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Planes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary2DMain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalNonsplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryGoodAct
public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneLift
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.D4Dichotomy
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.T1
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwLangConsumers
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalFinal
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinHeisCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSuzFaithful
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NormalFormStabilizer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

namespace PSUTwo

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem isLocallyBalancedAbs_two_three (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2)
    (hn : 4 ≤ n) : IsLocallyBalancedAbs 3 2 (primeFormP h (idGram K n)) := by
  classical
  have hfin := h.finite
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  intro D hD hcard H hH hDH
  have hH' : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H := hH
  have hDl : D ≤ primeFormD h (idGram K n) := le_primeFormD_three_two h hq hn3 hne hD
  obtain ⟨S, hS3, hSD, hS1⟩ := exists_split_lift hn hq hD hcard hDl
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨⟨M, τ⟩, rfl⟩ := surjective_primeFormPsi_of_ne (h := h) hn3 hne g
  by_cases hτ : τ = RingEquiv.refl K
  · subst hτ
    rw [psi_refl_eq] at hg ⊢
    exact eq_one_of_mem_localDeltaIn_inner hn hq hH' hS3 hSD hS1 hg
  · exfalso
    have h5 : n ≤ 5 := (outer_pattern hn hq hH' hS3 hSD hS1 hτ hg).1
    have hn3' : ¬ 3 ∣ n := by omega
    have hpg : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1) := fun hdvd => hn3' (hdvd.trans (Nat.gcd_dvd_left _ _))
    have hDin : D ≤ (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range := fun d hd =>
      mem_inner_of_pow_eq_one_unitary h (1 : GL (Fin n) K) Nat.prime_three hpg (hDl hd)
        (hD.2 d hd)
    have hEel : CFSG.IsElementaryAbelian 3 D :=
      { toIsMulCommutative := hD.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hD.2 x x.2) }
    have hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ 3 = 1 → c = 1 := by
      intro c _ hcn hc3
      have h1 := pow_gcd_eq_one.mpr ⟨hcn, hc3⟩
      have hg1 : Nat.gcd n 3 = 1 :=
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn3')
      rwa [hg1, pow_one] at h1
    obtain ⟨Ahat, ⟨hAel, hAcard, hAmap, hAinj⟩, -⟩ :=
      exists_unique_planeLift hn3 hne Nat.prime_three hZp D hDin hEel hcard
    refine not_all_fixed_dim hq hn3 Ahat hAel hAcard ?_
    intro x hx hx1
    have hx3 : x ^ 3 = 1 := by
      haveI := hAel
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Ahat) x hx
    have hy3 : (liftUnitary x) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact congrArg Subtype.val hx3
    have hyρ : primeFormConjHom h (idGram K n) (liftUnitary x) = innerLift h n x := by
      rw [primeFormConjHom_liftUnitary, innerLift_apply]
    have hyD : primeFormConjHom h (idGram K n) (liftUnitary x) ∈ D := by
      rw [hyρ, ← hAmap]
      exact Subgroup.mem_map_of_mem _ hx
    have hy1 : primeFormConjHom h (idGram K n) (liftUnitary x) ≠ 1 := by
      rw [hyρ]
      intro h1
      apply hx1
      exact hAinj hx (one_mem Ahat) (by rw [h1, map_one])
    have hdet : (((liftUnitary x : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).det = 1 := x.2.2
    exact (outer_pattern hn hq hH' hy3 hyD hy1 hτ hg).2 hdet

end PSUTwo

theorem psuTwoThreeBalance_holds : PSUTwoThreeBalance := by
  rintro ⟨d, hv⟩ hk hR hc hnexc
  obtain ⟨r, q, hd⟩ := hk
  change d = _ at hd
  subst hd
  obtain ⟨r', q', hd', hq2c⟩ := hR
  obtain ⟨rfl, rfl⟩ := TauCeti.LieTypeIndex.twistedA.inj hd'
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (CatT ⟨.twistedA r q, hv⟩))
  obtain ⟨⟨hℓ, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
  have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  have hq2 : q.p ^ q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq2c
  have h4 : 4 ≤ r + 1 := by
    by_contra hlt
    exact hq' ⟨by omega, hq2⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
  let e : CatT ⟨.twistedA r q, hv⟩ ≃* primeFormP h (idGram K (r + 1)) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  exact IsLocallyBalancedAbs.of_mulEquiv e (PSUTwo.isLocallyBalancedAbs_two_three h hq2 h4)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
