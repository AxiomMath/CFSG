module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBReduce
public import CFSG.Monster.B.CTIB.FourClasses
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Bar
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic

open Subgroup

section Generic

variable {W : Type*} [Group W]

@[expose] def ClassFact (r : W → ℕ) (x : W) : Prop :=
  ∃ P : Subgroup W, ⁅P, P⁆ = P ∧ P ≤ centralizer {x} ∧
    ∀ y ∈ centralizer (P : Set W), y * x = x * y → y ^ 2 = 1 → y ≠ 1 → y ≠ x → r y < r x

theorem classFact_conj {r : W → ℕ} (hr : ∀ g y : W, r (g * y * g⁻¹) = r y) {x : W}
    (h : ClassFact r x) (g : W) : ClassFact r (g * x * g⁻¹) := by
  obtain ⟨P, hP, hPx, hb⟩ := h
  refine ⟨P.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hpx := mem_centralizer_singleton_iff.mp (hPx hp)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * p * g⁻¹ * (g * x * g⁻¹) = g * (p * x) * g⁻¹ := by group
      _ = g * (x * p) * g⁻¹ := by rw [hpx]
      _ = g * x * g⁻¹ * (g * p * g⁻¹) := by group
  · intro y hy hyx hy2 hy1 hyx'
    set y' := g⁻¹ * y * g
    have hy'C : y' ∈ centralizer (P : Set W) := by
      rw [mem_centralizer_iff]
      intro p hp
      have := (mem_centralizer_iff.mp hy) (g * p * g⁻¹) ⟨p, hp, rfl⟩
      calc p * y' = g⁻¹ * ((g * p * g⁻¹) * y) * g := by simp only [y']; group
        _ = g⁻¹ * (y * (g * p * g⁻¹)) * g := by rw [this]
        _ = y' * p := by simp only [y']; group
    have hy'x : y' * x = x * y' := by
      calc y' * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by simp only [y']; group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hyx]
        _ = x * y' := by simp only [y']; group
    have hy'2 : y' ^ 2 = 1 := by
      calc y' ^ 2 = g⁻¹ * y ^ 2 * g := by simp only [y', sq]; group
        _ = 1 := by rw [hy2]; group
    have hy'1 : y' ≠ 1 := fun h => hy1 (by
      calc y = g * y' * g⁻¹ := by simp only [y']; group
        _ = 1 := by rw [h]; group)
    have hy'x' : y' ≠ x := fun h => hyx' (by
      calc y = g * y' * g⁻¹ := by simp only [y']; group
        _ = g * x * g⁻¹ := by rw [h])
    have hlt := hb y' hy'C hy'x hy'2 hy'1 hy'x'
    have hry : r y = r y' := by
      have := hr g y'
      rw [show g * y' * g⁻¹ = y by simp only [y']; group] at this
      exact this
    rw [hry, hr]
    exact hlt

theorem perfectCentralizerBound_of_reps {r : W → ℕ} (hr : ∀ g y : W, r (g * y * g⁻¹) = r y)
    (reps : Set W) (hreps : ∀ x : W, x ^ 2 = 1 → x ≠ 1 → ∃ x₀ ∈ reps, IsConj x x₀)
    (hfacts : ∀ x₀ ∈ reps, ClassFact r x₀) : PerfectCentralizerBound r := by
  intro x hx2 hx1
  obtain ⟨x₀, hx₀, hc⟩ := hreps x hx2 hx1
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have h := classFact_conj hr (hfacts x₀ hx₀) c⁻¹
  rw [← hc, show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h
  exact h

end Generic

namespace B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB

@[expose] noncomputable def rankB (X : NativeSporadic.B) : ℕ := (X.val.val - 1).rank

theorem rankB_conj (g y : NativeSporadic.B) : rankB (g * y * g⁻¹) = rankB y := by
  unfold rankB
  have hmul : ∀ a b : NativeSporadic.B, (a * b).val.val = a.val.val * b.val.val :=
    fun a b => by rw [Units.val_mul, Submonoid.coe_mul]
  have hg : g.val.val * (g⁻¹).val.val = 1 := by
    rw [← hmul, mul_inv_cancel, Units.val_one, Submonoid.coe_one]
  rw [hmul, hmul]
  exact rank_conj_sub_one hg

@[expose] noncomputable def classRep
    (i : ℕ) : NativeSporadic.B :=
  iotaEquiv.symm (rs i)

theorem classes_B
    : (∀ X : NativeSporadic.B, X ^ 2 = 1 → X ≠ 1 →
      ∃ i ∈ [1, 0, 5, 3], IsConj X (classRep i)) ∧
    rankB (classRep 1) = 1860 ∧ rankB (classRep 0) = 2048 ∧ rankB (classRep 5) = 2158 ∧
    rankB (classRep 3) = 2168 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hcl, -, h1, h0, h5, h3⟩ := native_four_involution_classes
  refine ⟨fun X hX2 hX1 => ?_, h1, h0, h5, h3⟩
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hcl X (orderOf_eq_prime hX2 hX1)
  exact ⟨i, hi, hc⟩

theorem rankB_of_involution
    {X : NativeSporadic.B} (hX2 : X ^ 2 = 1) (hX1 : X ≠ 1) :
    rankB X = 1860 ∨ rankB X = 2048 ∨ rankB X = 2158 ∨ rankB X = 2168 := by
  obtain ⟨hcl, h1, h0, h5, h3⟩ := classes_B
  obtain ⟨i, hi, hc⟩ := hcl X hX2 hX1
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have hr : rankB X = rankB (classRep i) := by rw [← hc, rankB_conj]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · left; rw [hr, h1]
  · right; left; rw [hr, h0]
  · right; right; left; rw [hr, h5]
  · right; right; right; rw [hr, h3]

theorem isConj_classRep
    {X : NativeSporadic.B} (hX2 : X ^ 2 = 1) (hX1 : X ≠ 1) :
    ∃ i ∈ [1, 0, 5, 3], IsConj X (classRep i) ∧ rankB X = rankB (classRep i) := by
  obtain ⟨hcl, -⟩ := classes_B
  obtain ⟨i, hi, hc⟩ := hcl X hX2 hX1
  refine ⟨i, hi, hc, ?_⟩
  obtain ⟨c, hc'⟩ := isConj_iff.mp hc
  rw [← hc', rankB_conj]

theorem perfectCentralizerBound_B
    (h : ∀ i ∈ [1, 0, 5, 3], ∃ x : NativeSporadic.B, x ^ 2 = 1 ∧ x ≠ 1 ∧
      rankB x = rankB (classRep i) ∧ ClassFact rankB x) :
    PerfectCentralizerBound rankB := by
  obtain ⟨hcl, h1, h0, h5, h3⟩ := classes_B
  refine perfectCentralizerBound_of_reps (fun g y => rankB_conj g y)
    {x | ∃ i ∈ [1, 0, 5, 3], x ^ 2 = 1 ∧ x ≠ 1 ∧ rankB x = rankB (classRep i) ∧
      ClassFact rankB x} (fun X hX2 hX1 => ?_) (fun _ ⟨_, _, _, _, _, hx⟩ => hx)
  obtain ⟨i, hi, hcX⟩ := hcl X hX2 hX1
  obtain ⟨x, hx2, hx1, hxr, hxf⟩ := h i hi
  obtain ⟨j, hj, hcx, hxr'⟩ := isConj_classRep hx2 hx1
  have hij : j = i := by
    rw [hxr] at hxr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; omega)
  subst hij
  exact ⟨x, ⟨j, hi, hx2, hx1, hxr, hxf⟩, hcX.trans (isConj_comm.mp hcx)⟩

end B

end CFSG.ComponentClassification.RankTwoSporadic
