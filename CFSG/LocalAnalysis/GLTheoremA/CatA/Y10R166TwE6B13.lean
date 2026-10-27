module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B12
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldAlign
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompTorusComm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A6
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.ClassicalInvolution.Upgrade
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open scoped commutatorElement

section Certs

local instance e6TwE6B13NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩


variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω] [CharP Ω 2]
  {Fr : Ω →+* Ω}

theorem twE6JStar_le_twE6C {q : ℕ} {ζ : Ωˣ}
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))) :
    twE6JStar (Fr := Fr) (q := q) (ζ := ζ) i ≤ twE6C Fr := by
  intro x hx
  rw [mem_twE6C]
  unfold twE6JStar rationalComponent rationalSpan at hx
  exact Subgroup.commutator_le_self _
    ((Subgroup.commutator_mono inf_le_right inf_le_right) hx)

theorem torusElt_mem_twE6JStar (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) (hod : Odd f)
    {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ω))) {j : Fin Tag.E6.rank}
    (hj : j ≠ 0) {t : Ωˣ} (ht : t ^ 3 = 1) :
    torusElt Tag.E6 Ω j t ∈ twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i := by
  have hker : kernelRoots (rootCharHom (twE6omega1Tuple ω)) = twE6D5 :=
    kernelRoots_omega1 Nat.prime_three hω3 hω1
  have hΨ : componentRoots (rootCharHom (twE6omega1Tuple ω)) i = twE6D5 :=
    componentRoots_eq_twE6D5 hker i
  have hsingle : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
      rationalRoots (Equiv.neg (Fin Tag.E6.rank → ℤ)) (rootCharHom (twE6omega1Tuple ω)) i := by
    refine ⟨0, Pi.single j 1, ?_, by simp⟩
    rw [hΨ]
    exact ⟨isRoot_single Tag.E6 j, by rw [Pi.single_eq_of_ne (Ne.symm hj)]⟩
  have hnegsingle : (-Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈
      rationalRoots (Equiv.neg (Fin Tag.E6.rank → ℤ)) (rootCharHom (twE6omega1Tuple ω)) i := by
    refine ⟨0, -Pi.single j 1, ?_, by simp⟩
    rw [hΨ]
    exact ⟨isRoot_neg_single Tag.E6 j, by simp [Pi.single_eq_of_ne (Ne.symm hj)]⟩
  have hnS : weylElt Tag.E6 Ω j 1 ∈
      rationalSpan (Equiv.neg (Fin Tag.E6.rank → ℤ))
        ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆
        (rootCharHom (twE6omega1Tuple ω)) i :=
    ⟨CFSG.SeitzReduction.E6Pilot.weylElt_mem_rootSpan_E6 hsingle hnegsingle,
      mem_twE6C.1 (TwE6B.weylElt_mem_twE6C (K := K) (σ := σ.toRingHom) (n := f)
        (by omega) hK hσ hFr j)⟩
  have htS : torusElt Tag.E6 Ω j t ∈
      rationalSpan (Equiv.neg (Fin Tag.E6.rank → ℤ))
        ⁅TwistedDiag.thetaFixed Fr, TwistedDiag.thetaFixed Fr⁆
        (rootCharHom (twE6omega1Tuple ω)) i :=
    ⟨CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.torusElt_mem_rootSpan_e6
        hsingle hnegsingle t,
      mem_twE6C.1 (TwE6B.torusElt_mem_twE6C hFr hod ht j)⟩
  rw [TwE6B.torusElt_eq_commutator_weylElt j ht]
  unfold twE6JStar rationalComponent
  exact Subgroup.commutator_mem_commutator hnS htS

theorem twE6BZero_le_twE6JStar (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (hFr : ∀ c, Fr c = c ^ (2 ^ f)) (hod : Odd f)
    {ω : Ωˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (i : KernelComponent (rootCharHom (twE6omega1Tuple ω))) :
    twE6BZero ω hω3 ≤ twE6JStar (Fr := Fr) (q := 3) (ζ := ω) i := by
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  refine TwE6B.twE6BZero_le_of_gens hω3 ?_ ?_ ?_ ?_
  · exact torusElt_mem_twE6JStar hf hK hσ hFr hod hω3 hω1 i (by decide) hω3
  · exact torusElt_mem_twE6JStar hf hK hσ hFr hod hω3 hω1 i (by decide) hω3
  · exact torusElt_mem_twE6JStar hf hK hσ hFr hod hω3 hω1 i (by decide) hω3
  · exact mul_mem (torusElt_mem_twE6JStar hf hK hσ hFr hod hω3 hω1 i (j := 4)
      (by decide) hω23) (torusElt_mem_twE6JStar hf hK hσ hFr hod hω3 hω1 i (j := 5)
      (by decide) hω3)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
