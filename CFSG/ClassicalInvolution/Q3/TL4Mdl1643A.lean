module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5GL2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscFusionR8
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open scoped MatrixGroups

namespace E1643

section Alpha

variable {Y : Type} [Group Y]

theorem closure_pair_facts {z z' : Y} (hz : z * z = 1) (hz' : z' * z' = 1)
    (hzz' : z * z' = z' * z) :
    (∀ x ∈ Subgroup.closure ({z, z'} : Set Y), ∀ y ∈ Subgroup.closure ({z, z'} : Set Y),
      x * y = y * x) ∧ ∀ x ∈ Subgroup.closure ({z, z'} : Set Y), x * x = 1 := by
  have hcz : Subgroup.closure ({z, z'} : Set Y) ≤ Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx <;> rw [hx, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hzz'.symm
  have hcz' : Subgroup.closure ({z, z'} : Set Y) ≤ Subgroup.centralizer ({z'} : Set Y) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx <;> rw [hx, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hzz'
  have hle : Subgroup.closure ({z, z'} : Set Y) ≤
      Subgroup.centralizer ((Subgroup.closure ({z, z'} : Set Y) : Set Y)) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hcz hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hcz' hy)
  have hc : ∀ x ∈ Subgroup.closure ({z, z'} : Set Y), ∀ y ∈ Subgroup.closure ({z, z'} : Set Y),
      x * y = y * x := fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hle hy) x hx
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz
    · exact hz'
  | one => exact mul_one 1
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc y hy x hx]
      _ = x * x * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]

end Alpha

end E1643

end CFSG.ClassicalInvolution.Q3.TL4
