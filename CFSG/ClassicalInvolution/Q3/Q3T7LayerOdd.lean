module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Normal

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_normal {E C : Subgroup G} (hEC : E ≤ C) (hn : (E.subgroupOf C).Normal)
    (hC : classicalInvolutionOddCore ↥C = ⊥) : classicalInvolutionOddCore ↥E = ⊥ := by
  have hsub : IsSubnormal (E.subgroupOf C) ⊤ :=
    IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  have h1 : classicalInvolutionOddCore ↥(E.subgroupOf C) = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hC (E.subgroupOf C) hsub
  let e : ↥(E.subgroupOf C) ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEC
  have h2 : (classicalInvolutionOddCore ↥(E.subgroupOf C)).map e.toMonoidHom =
      classicalInvolutionOddCore ↥E :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [← h2, h1, Subgroup.map_bot]

end Normal

namespace ExactLayer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem oddCore_exactLayer_eq_bot_of_centralizer (hΩ : ConjInvariant Ω)
    (hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(exactLayer Ω c) = ⊥ := by
  have hn : ((exactLayer Ω c).subgroupOf (Subgroup.centralizer ({c} : Set G))).Normal := by
    refine ⟨fun h hh n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    have hmem : (n : G) * (h : G) * (n : G)⁻¹ ∈ conjSub (n : G) (exactLayer Ω c) :=
      Subgroup.mem_map_of_mem (MulAut.conj (n : G)).toMonoidHom hh
    rw [conjSub_exactLayer hΩ n.2] at hmem
    simpa using hmem
  exact oddCore_eq_bot_of_normal (exactLayer_le_centralizer Ω c) hn hC

end ExactLayer

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
