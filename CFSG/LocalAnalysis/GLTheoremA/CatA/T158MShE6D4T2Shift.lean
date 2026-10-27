module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Shift

variable {L : Type} [Field L]

theorem e6d4t2_stab_conj
    {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) : t * w * t⁻¹ ∈ rootCharStabilizerSubgroup a := by
  intro v
  have h1 : rootChar a v = (rootChar a (t⁻¹ • v))⁻¹ := by
    have := ht (t⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this
  rw [mul_smul, mul_smul, ht, hw, ← h1]

theorem e6d4t2_shift_conj_one
    {a : Fin Tag.E6.rank → Lˣ} {t : WeylGroup Tag.E6}
    (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) :
    rootChar a (e6Shift (t * w * t⁻¹ * w)) = 1 := by
  have hc : t * w * t⁻¹ ∈ rootCharStabilizerSubgroup a := e6d4t2_stab_conj ht hw
  have h0 : (0 : Fin Tag.E6.rank → ℤ) = t • e6Shift t⁻¹ + e6Shift t := by
    rw [← e6Shift_mul t t⁻¹, mul_inv_cancel, e6Shift_one]
  have hinv : rootChar a (e6Shift t⁻¹) = rootChar a (e6Shift t) := by
    have e := congrArg (rootChar a) h0
    rw [rootChar_zero, rootChar_add, ht] at e
    exact (inv_mul_eq_one.1 e.symm)
  have h1 : e6Shift (t * w * t⁻¹ * w) =
      (t * w * t⁻¹) • e6Shift w + ((t * w) • e6Shift t⁻¹ + t • e6Shift w + e6Shift t) := by
    rw [e6Shift_mul (t * w * t⁻¹) w, e6Shift_mul (t * w) t⁻¹, e6Shift_mul t w]
    abel
  have f1 : rootChar a ((t * w * t⁻¹) • e6Shift w) = rootChar a (e6Shift w) := hc _
  have f2 : rootChar a ((t * w) • e6Shift t⁻¹) = (rootChar a (e6Shift t))⁻¹ := by
    rw [mul_smul, ht, hw, hinv]
  have f3 : rootChar a (t • e6Shift w) = (rootChar a (e6Shift w))⁻¹ := ht _
  rw [h1, rootChar_add, rootChar_add, rootChar_add, f1, f2, f3]
  generalize rootChar a (e6Shift w) = A
  generalize rootChar a (e6Shift t) = B
  calc A * (B⁻¹ * A⁻¹ * B) = (A * A⁻¹) * (B⁻¹ * B) := by ac_rfl
    _ = 1 := by rw [mul_inv_cancel, inv_mul_cancel, one_mul]

theorem e6d4t2_shift_conj
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1) {t : WeylGroup Tag.E6}
    (ht : ∀ x, rootChar a (t • x) = (rootChar a x)⁻¹) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) : t * w * t⁻¹ * w ∈ kernelReflectionGroup a :=
  mem_kernelReflectionGroup_of_e6Shift a hap
    (mul_mem (e6d4t2_stab_conj ht hw) hw) (e6d4t2_shift_conj_one ht hw)

theorem e6d4t2_cube_mem
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) : w ^ 3 ∈ kernelReflectionGroup a := by
  refine mem_kernelReflectionGroup_of_e6Shift a hap (pow_mem hw 3) ?_
  have h := map_pow (e6ShiftChar a) (⟨w, hw⟩ : rootCharStabilizerSubgroup a) 3
  have h3 := e6ShiftChar_pow_three a ⟨w, hw⟩
  have : e6ShiftChar a (⟨w, hw⟩ ^ 3) = 1 := by rw [h, h3]
  exact this

end Shift

end CFSG.LocalAnalysis.GLTheoremA.T158

end
