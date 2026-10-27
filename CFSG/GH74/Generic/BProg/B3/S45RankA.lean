module

public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45Glue

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic.BProg.B3.FalseCtxS45
open CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

@[expose] def LocBal32All (Jt : Type) [Group Jt] : Prop :=
  ∀ B : Subgroup (MulAut Jt), (∀ b ∈ B, b * b = 1) → IsLocBal32 Jt B

section Branch

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem center_ne_bot_of_xbar_mem (hc : Ctx21 G x K A a D J)
    (hxb : L5U5.xbar a ∈ PumpCalc.bar a J) : Subgroup.center ↥(PumpCalc.bar a J) ≠ ⊥ := by
  intro hbot
  have hmem : (⟨L5U5.xbar a, hxb⟩ : ↥(PumpCalc.bar a J)) ∈ Subgroup.center ↥(PumpCalc.bar a J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (L5U5.xbar_mem_center a) (g : CentralizerBar a))
  rw [hbot, Subgroup.mem_bot] at hmem
  exact L5U5.xbar_ne_one hc.obs.y_ord (congrArg Subtype.val hmem)

end Branch

end CFSG.GH74.Generic.BProg.B3
