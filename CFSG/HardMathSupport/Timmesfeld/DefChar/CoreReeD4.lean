module

public import CFSG.HardMathSupport.Timmesfeld.DefChar.Families
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreExcGeneric
public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ReeMain
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Par
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Inner
public import CFSG.GH74.GLS.Stage2.OddAut.RPData
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.HardMathSupport.Timmesfeld.DefChar

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.LieType.Ree (ReeTag)

theorem innerCoreFree_transport {S Y : Type} [Group S] [Group Y] (e : S ≃* Y) {p : ℕ}
    (key : ∀ H' : Subgroup (MulAut Y), innerAut Y ≤ H' → ∀ x' ∈ innerAut Y, orderOf x' = p →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({x'} : Set (MulAut Y))) = ⊥) :
    ∀ x ∈ innerAut S, orderOf x = p → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥ := by
  intro x hx hxo H hH
  set φ := MulAut.congr e with hφ
  have hinn : innerAut Y ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), hH ⟨e.symm y, rfl⟩, ?_⟩
    ext s
    simp [hφ, MulAut.congr_apply]
  have hx' : φ x ∈ innerAut Y := by
    obtain ⟨g, rfl⟩ := hx
    refine ⟨e g, ?_⟩
    ext s
    simp [hφ, MulAut.congr_apply]
  have h := key _ hinn (φ x) hx' (by rw [MulEquiv.orderOf_eq φ x]; exact hxo)
  rw [CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_map_inf_centralizer] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h

theorem innerCoreFree_of_parCharP_top {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (hBT : CFSG.LieType.BorelTits.Holds Y p) (hcen : Subgroup.center Y = ⊥)
    (hd : PCharData Y p ⊤) :
    ∀ H' : Subgroup (MulAut Y), innerAut Y ≤ H' → ∀ x' ∈ innerAut Y, orderOf x' = p →
      GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({x'} : Set (MulAut Y))) = ⊥ :=
  fun H' hH' x' hx' hxo =>
    gLAPPrimeCoreOf_centralizer_eq_bot_of_parCharP hBT hcen (parCharP_of_data hcen hd)
      le_top hH' hx' hxo

theorem defCharInnerCoreFreeFamReeG2 : DefCharInnerCoreFreeFam .reeG2 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl⟩ := hidx
  obtain ⟨e0⟩ := hS
  have hp3 : p = 3 := by simpa using hch.symm
  subst hp3
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 (2 * m + 1)) = 3 ^ (2 * m + 1) :=
    GaloisField.card 3 (2 * m + 1) (by omega)
  have : CharP (GaloisField 3 (2 * m + 1)) ReeTag.G2.prime :=
    (inferInstance : CharP (GaloisField 3 (2 * m + 1)) 3)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv (GaloisField 3 (2 * m + 1)) hK
  have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * m + 1)) reeG2Perm
      fun i => if i ∈ reeG2Long then 3 ^ m else 3 ^ (m + 1)) ≃*
        DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
    (K := GaloisField 3 (2 * m + 1)) hm1 hK
  let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m :=
    ((e0.trans b.symm).trans e1).trans E
  have : Finite (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.finite_reeGamma
  have hcen : Subgroup.center (ReeTag.G2.reeGamma (GaloisField 3 (2 * m + 1)) m) = ⊥ :=
    ReeTag.center_reeGamma_G2_eq_bot hK
  exact innerCoreFree_transport e
    (innerCoreFree_of_parCharP_top CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_holds hcen
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.ree_pCharData hm1 hK)) x hx hxo H hH

theorem defCharInnerCoreFreeFamTrialityD4 : DefCharInnerCoreFreeFam .trialityD4 := by
  intro S _ _ _ _ idx hidx hS p hp hp2 hch x hx hxo H hH
  obtain ⟨q, hr⟩ := hidx
  obtain ⟨d, hv⟩ := idx
  simp only at hr
  subst hr
  obtain ⟨e0⟩ := hS
  have hpq : p = q.p := by simpa using hch.symm
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let K := GaloisField q.p (3 * q.exponent)
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hKc : Nat.card K = (q.p ^ q.exponent) ^ TwistTag.D4.order := by
    change Nat.card (GaloisField q.p (3 * q.exponent)) = _
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega)]
    change _ = (q.p ^ q.exponent) ^ 3
    rw [← pow_mul, mul_comm]
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p hf K hKc
  subst hpq
  have hK3 : Nat.card K = (q.p ^ q.exponent) ^ 3 := hKc
  obtain ⟨-, -, -, -, -, -, hcen, ⟨eC⟩⟩ :=
    odd_triality_exact_automorphism_normal_form q.prime_p hp2 hf K hK3 σ hσ
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨eB⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv K
    (by rw [hqc]; exact hK3) σ.toRingHom (fun x => by rw [hqc]; exact hσ x)
  have e : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    e0.trans (eB.symm.trans eC)
  have hσ3 : σ ^ TwistTag.D4.order = 1 :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_sigma_pow_order K hK3 σ hσ
  have hBT : CFSG.LieType.BorelTits.Holds (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) q.p :=
    CFSG.LieType.BorelTits.holds_of_twistedChevalleyModel (t := TwistTag.D4) hf
      ⟨K, inferInstance, inferInstance, hK3, σ.toRingHom, hσ, ⟨eC.symm⟩⟩
  have hAtop := CFSG.GH74.GLS.Stage2.Bender.Thm1.par_fixedDiagonalFieldActors_D4_eq_top_odd
    q.prime_p hp2 hf K hK3 σ hσ
  have hd := CFSG.GH74.GLS.Stage2.Bender.Thm1.pCharData_fixed TwistTag.D4 K σ hσ3 q.p
  rw [hAtop] at hd
  exact innerCoreFree_transport e (innerCoreFree_of_parCharP_top hBT hcen hd) x hx hxo H hH

end CFSG.HardMathSupport.Timmesfeld.DefChar
