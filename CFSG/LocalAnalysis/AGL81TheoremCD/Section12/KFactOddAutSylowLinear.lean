module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.HardMathSupport.Foote.ModuleExclusions.ProjectiveLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Milestones.ASVolI.A3Aut.C5L3
import CFSG.Dihedral.GorensteinWalter.PSL2EvenOuterOddSylow
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
import CFSG.RankThree.PartOne.CTP.SpEven
import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Item426A6
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Sec8.Steps
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

private theorem psl_ge_three_fieldAut_pow_orderOf_eq_one {K : Type} [Field K] [Finite K] {n r k : ℕ}
    (hn : 3 ≤ n) (hr : r.Prime)
    (hdiag : ¬ r ∣ Nat.gcd n (Nat.card K - 1)) {A : GL (Fin n) K} {σ : K ≃+* K}
    (hα : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) ^ (r ^ k) = 1)
    (hinn : Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) = ⊥) :
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) ^
      orderOf (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) = 1 := by
  have htrans :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.standard_automorphism_transport
      (K := K) (n := n)
  exact pow_orderOf_eq_one_of_mul
    (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K))
    (D := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup n K)
    (fun δ hδ j hδj =>
      CFSG.RankThree.PartOne.OutStructure.linear_D2 hr hn hdiag δ hδ j hδj)
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_linearAutGroup A)
    (fun g hg => by
      obtain ⟨B, rfl⟩ :=
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_linearAutGroup_iff).mp hg
      rw [htrans.2.2.1]
      exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_mem_linearAutGroup _)
    hα hinn

private theorem psl_ge_three_exists_conj_fieldAut_of_odd_order {K : Type} [Field K] [Finite K]
    {n r : ℕ} (hn : 3 ≤ n) (hr : r.Prime)
    (hdiag : ¬ r ∣ Nat.gcd n (Nat.card K - 1))
    {α : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)}
    {k : ℕ} (hα : orderOf α = r ^ k) (hodd : Odd (r ^ k))
    (hinn : Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) = ⊥) :
    ∃ (B : GL (Fin n) K) (σ : K ≃+* K),
      α = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K B *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K B)⁻¹ := by
  have hαpow : α ^ (r ^ k) = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hαE : α ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.semilinearAutGroup n K :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd
      hn hodd hαpow
  obtain ⟨A, σ, hαeq⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_iff).mp hαE
  have hαr : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) ^ (r ^ k) = 1 := by
    rw [← hαeq]; exact hαpow
  have hinn' : Subgroup.zpowers (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ) ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) = ⊥ := by
    rw [← hαeq]; exact hinn
  have hfieldpow := psl_ge_three_fieldAut_pow_orderOf_eq_one hn hr hdiag hαr hinn'
  have : NeZero n := ⟨by omega⟩
  obtain ⟨B, hB⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.exists_conj_fieldAut_of_pow_eq_one
    (n := n) (K := K) σ A (by
      rw [← CFSG.RankThree.PartOne.KCLinearSubfield.orderOf_fieldAut hn σ]
      exact hfieldpow)
  exact ⟨B, σ, hαeq.trans hB⟩

theorem oddAutSylowFixAt_psl {Y : Type} [Group Y] [Finite Y] {n f r : ℕ} (hn : 3 ≤ n)
    (hC : CFSG.Open.StatedClassicalModel Y .PSL n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hgcd : ¬ r ∣ Nat.gcd n (2 ^ f - 1)) : OddAutSylowFixAt r Y := by
  classical
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e0⟩⟩ := hC
  let _ := hKfield
  let _ := hKfinite
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hKcard])
  have : NeZero n := ⟨by omega⟩
  have hdiag : ¬ r ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hKcard]
  let P := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K
  let c : GL (Fin n) K →* MulAut P :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K
  let F : (K ≃+* K) →* MulAut P :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K
  let e : Y ≃* P :=
    (e0.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        n K)
  have : Finite P := Finite.of_equiv Y e.toEquiv
  refine OddAutSylowFixAt.of_mulEquiv e.symm ?_
  obtain ⟨S₀, hS₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
      (K := K) 2 (n := n) (by omega)
  refine OddAutSylowFixAt.of_conj S₀ ?_
  intro α k hα hinn
  have hodd : Odd (r ^ k) := (hr.odd_of_ne_two (by omega)).pow
  obtain ⟨B, σ, hB⟩ := psl_ge_three_exists_conj_fieldAut_of_odd_order hn hr hdiag hα hodd hinn
  refine ⟨c B, F σ, hB, ?_⟩
  rw [hS₀]
  exact CFSG.ASVolI.burnsideAut_c5L3_map_fieldAut_U σ

theorem oddAutSylowFixAt_psl_two {Y : Type} [Group Y] [Finite Y] {f r : ℕ}
    (hC : CFSG.Open.StatedClassicalModel Y .PSL 2 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r Y := by
  obtain ⟨-, K, hField, hFinite, hK, ⟨e0⟩⟩ := hC
  let _ : Field K := hField
  let _ : Finite K := hFinite
  let e : Y ≃* CFSG.GorensteinWalter.PSL2 K :=
    e0.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine OddAutSylowFixAt.of_mulEquiv e.symm ?_
  intro α k hα hinn
  have hodd : Odd (orderOf α) := by
    rw [hα]
    exact (hr.odd_of_ne_two (by omega)).pow
  have hmem : Subgroup.zpowers α ⊓
      (MulAut.conj : CFSG.GorensteinWalter.PSL2 K →*
        MulAut (CFSG.GorensteinWalter.PSL2 K)).range = ⊥ := by
    simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hinn
  obtain ⟨S, hS⟩ :=
    CFSG.GorensteinWalter.psl2_even_exists_sylow_fixed_of_inf_inner_eq_bot
      hK (Subgroup.zpowers α) (by rw [Nat.card_zpowers]; exact hodd) hmem
  refine ⟨S, ?_⟩
  have hS' : α • S = S := hS α (Subgroup.mem_zpowers α)
  exact congrArg (fun T : Sylow 2 (CFSG.GorensteinWalter.PSL2 K) =>
    (T : Subgroup (CFSG.GorensteinWalter.PSL2 K))) hS'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
