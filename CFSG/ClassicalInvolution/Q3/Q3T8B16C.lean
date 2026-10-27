module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26UAction
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.AschTight.S19GTrace
public import CFSG.ClassicalInvolution.Uniform.U5Comp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open scoped commutatorElement MatrixGroups

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.DeltaClosure

section Basic

variable {G : Type} [Group G] [Finite G]

theorem isUniqueInvolution_modOddIn {Y K : Subgroup G} {z : G} (hKY : K ≤ Y)
    (hz : IsUniqueInvolution K z) :
    IsUniqueInvolution (modOddIn Y K)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) (⟨z, hKY hz.mem⟩ : ↥Y)) := by
  have hz' : IsUniqueInvolution (K.subgroupOf Y) (⟨z, hKY hz.mem⟩ : ↥Y) := by
    refine ⟨Subgroup.mem_subgroupOf.mpr hz.mem, ?_, ?_, ?_⟩
    · intro h
      exact hz.ne_one (congrArg Subtype.val h)
    · exact Subtype.ext hz.sq
    · intro y hy hy2
      rcases hz.unique (y : G) (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hy2) with
        h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  exact isUniqueInvolution_map_mk_of_odd (X := classicalInvolutionOddCore ↥Y)
    (odd_natCard_inf (OddCore.odd_card Y) _) hz'

end Basic

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem s26Act_apply_eq_of_comm_mem (X : Subgroup G) (b : ↥(Subgroup.normalizer (X : Set G)))
    (x : ↥X) (h : ⁅(b : G), (x : G)⁆ ∈ oddCoreOf X) :
    s26Act X b (x : ↥X ⧸ classicalInvolutionOddCore ↥X) =
      (x : ↥X ⧸ classicalInvolutionOddCore ↥X) := by
  have hxX : ((b : G) * x * (b : G)⁻¹) ∈ X := (Subgroup.mem_normalizer_iff.mp b.2 x).mp x.2
  rw [s26Act_mk X b x ⟨(b : G) * x * (b : G)⁻¹, hxX⟩ rfl, QuotientGroup.eq_iff_div_mem]
  obtain ⟨h1, h2⟩ := mem_oddCoreOf_iff.mp h
  convert h2 using 1
  apply Subtype.ext
  simp [commutatorElement_def, div_eq_mul_inv]

end Section

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
