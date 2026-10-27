module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.U62CoversB
public import Certificates.Certificate450060
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.Fi23 CFSG.Sporadic.Th.Native
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Sylow

theorem involutionFixesElem_lvl_two :
    InvolutionFixesElem ↥(lvl 2) 64 :=
  Certificates.certificate450060.1

theorem d_mem_commutator_lvl_two :
    (⟨CFSG.Sporadic.Fi23.d, d_mem_lvl_two⟩ : ↥(lvl 2)) ∈ commutator ↥(lvl 2) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := Certificates.certificate450060.2
  have h : ⁅(⟨x, hx⟩ : ↥(lvl 2)), (⟨y, hy⟩ : ↥(lvl 2))⁆ ∈ commutator ↥(lvl 2) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have e : ⁅(⟨x, hx⟩ : ↥(lvl 2)), (⟨y, hy⟩ : ↥(lvl 2))⁆ =
      ⟨CFSG.Sporadic.Fi23.d, d_mem_lvl_two⟩ :=
    Subtype.ext hxy
  rwa [e] at h

end Sylow

end CFSG.EvenSporadicStandard.Induction.Fi
