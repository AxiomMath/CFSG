module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIFunct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.GroupActions CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.Assembly
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.MI
open scoped Classical

theorem blockComponent_fixed_apply {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {p : ℕ}
    (hx : OddOrderIsometry Q p x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
    (hv : v ∈ primaryComponent x.toLinearMap a) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V) v =
      if a = X - 1 then y v else v := by
  classical
  have hrec : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := reciprocalPolynomial_X_sub_one
  have h := blockComponent_apply_of_mem hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩ (X - 1) ha hv
  simpa [hrec] using h

theorem blockComponent_fixed_pow {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {p n : ℕ}
    (hx : OddOrderIsometry Q p x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    (hyn : y ^ n = 1) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V) ^ n = 1 := by
  classical
  set yW : V ≃ₗ[K] V :=
    (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hyc : y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hy).2
  have hpow : ∀ k : ℕ, ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a),
      (yW ^ k) v = if a = X - 1 then (y ^ k) v else v := by
    intro k
    induction k with
    | zero => intro a ha v hv; simp
    | succ k ih =>
      intro a ha v hv
      have hyk : (y ^ k) v ∈ primaryComponent x.toLinearMap a :=
        apply_mem_primaryComponent_of_mem_centralizer (Subgroup.pow_mem _ hyc k) hv
      rw [pow_succ', LinearEquiv.mul_apply]
      by_cases haX : a = X - 1
      · rw [pow_succ', LinearEquiv.mul_apply, ih a ha v hv, if_pos haX,
          hyW_apply a ha ((y ^ k) v) hyk]
        simp [haX]
      · rw [pow_succ', LinearEquiv.mul_apply, ih a ha v hv, if_neg haX,
          hyW_apply a ha v hv]
        simp [haX]
  have hmap : ((yW ^ n : V ≃ₗ[K] V) : V →ₗ[K] V) = 1 := by
    apply ext_primaryComponent hx.squarefree_minpoly
    intro a ha v hv
    have hynv : (y ^ n) v = v := by
      have h1 := congrArg (fun e : V ≃ₗ[K] V => e v) hyn
      simpa using h1
    change (yW ^ n) v = v
    rw [hpow n a ha v hv]
    by_cases haX : a = X - 1
    · rw [if_pos haX, hynv]
    · rw [if_neg haX]
  exact LinearEquiv.ext fun v => by
    have := congrArg (fun f : V →ₗ[K] V => f v) hmap
    simpa using this

private theorem blockComponent_fixed_inv_apply {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {x : V ≃ₗ[K] V} {p : ℕ} (hx : OddOrderIsometry Q p x) {y : V ≃ₗ[K] V}
    (hy : y ∈ isometryCentralizer Q x) (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap)
    (v : V) (hv : v ∈ primaryComponent x.toLinearMap a) :
    ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 : V ≃ₗ[K] V)⁻¹ v =
      if a = X - 1 then y⁻¹ v else v := by
  classical
  set yW : V ≃ₗ[K] V :=
    (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hyinv : y⁻¹ v ∈ primaryComponent x.toLinearMap a :=
    apply_mem_primaryComponent_of_mem_centralizer
      (Subgroup.mem_inf.mp (inv_mem hy)).2 hv
  by_cases haX : a = X - 1
  · apply yW.injective
    rw [if_pos haX]
    change yW (yW.symm v) = yW (y.symm v)
    rw [yW.apply_symm_apply, hyW_apply a ha (y.symm v) hyinv, if_pos haX]
    exact (y.apply_symm_apply v).symm
  · apply yW.injective
    rw [if_neg haX]
    change yW (yW.symm v) = yW v
    rw [yW.apply_symm_apply, hyW_apply a ha v hv, if_neg haX]

theorem blockComponent_fixed_conj_eq {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {p : ℕ}
    (hx : OddOrderIsometry Q p x) {y : V ≃ₗ[K] V} (hy : y ∈ isometryCentralizer Q x)
    {f : V ≃ₗ[K] V} (hf : f ∈ supportedBlock Q x (X - 1 : K[X])) :
    y * f * y⁻¹ =
      (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 * f *
        ((CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1)⁻¹ := by
  classical
  set yW : V ≃ₗ[K] V :=
    (CFSG.RankThree.PartOne.KCOrthogonal.blockComponent hx ⟨y, (Subgroup.mem_inf.mp hy).2⟩
      (X - 1)).1 with hyW
  have hyW_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW v = if a = X - 1 then y v else v :=
    fun a ha v hv => blockComponent_fixed_apply hx hy a ha v hv
  have hyWinv_apply : ∀ (a : K[X]) (ha : a ∈ primaryFactors x.toLinearMap) (v : V)
      (hv : v ∈ primaryComponent x.toLinearMap a), yW⁻¹ v = if a = X - 1 then y⁻¹ v else v :=
    fun a ha v hv => blockComponent_fixed_inv_apply hx hy a ha v hv
  have hmap : (((y * f * y⁻¹ : V ≃ₗ[K] V)) : V →ₗ[K] V) =
      (((yW * f * yW⁻¹ : V ≃ₗ[K] V)) : V →ₗ[K] V) := by
    apply ext_primaryComponent hx.squarefree_minpoly
    intro a ha v hv
    have hc := supportedBlock_le_centralizer (X - 1) hf
    have hyinv : y⁻¹ v ∈ primaryComponent x.toLinearMap a :=
      apply_mem_primaryComponent_of_mem_centralizer (Subgroup.mem_inf.mp (inv_mem hy)).2 hv
    by_cases haX : a = X - 1
    · have hfmem : f (y⁻¹ v) ∈ primaryComponent x.toLinearMap a :=
        apply_mem_primaryComponent_of_mem_centralizer hc hyinv
      change y (f (y⁻¹ v)) = yW (f (yW⁻¹ v))
      rw [hyWinv_apply a ha v hv, if_pos haX, hyW_apply a ha (f (y⁻¹ v)) hfmem, if_pos haX]
    · have hfv : f (y⁻¹ v) = y⁻¹ v := by
        refine apply_eq_of_mem_supportedBlock hf ha haX ?_ hyinv
        rwa [reciprocalPolynomial_X_sub_one]
      have hyWinv : yW⁻¹ v ∈ primaryComponent x.toLinearMap a := by
        rw [hyWinv_apply a ha v hv, if_neg haX]; exact hv
      have hfW : f (yW⁻¹ v) = yW⁻¹ v := by
        refine apply_eq_of_mem_supportedBlock hf ha haX ?_ hyWinv
        rwa [reciprocalPolynomial_X_sub_one]
      change y (f (y⁻¹ v)) = yW (f (yW⁻¹ v))
      rw [hfv, hfW]
      change y (y.symm v) = yW (yW.symm v)
      exact (y.apply_symm_apply v).trans (yW.apply_symm_apply v).symm
  exact LinearEquiv.ext fun v => by
    have := congrArg (fun f : V →ₗ[K] V => f v) hmap
    simpa using this

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
