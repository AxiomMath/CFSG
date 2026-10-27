module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Normalizer
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

section Certified

theorem centralizer_z_le_M : ∀ g : J, g * z = z * g → g ∈ M := by
  intro g hg
  obtain ⟨hcent, -, -, -⟩ := ctuc_Th_full_central_involution_centralizer
  rw [← hcent, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rw [← z_eq_a]
  exact hg.symm

theorem thLocalWitness_J : ThLocalWitness LocalDataTh.S LocalDataTh.A LocalDataTh.B z :=
  LocalDataTh.thLocalWitness_of_facts natCard_J (LocalDataTh.card_B centralizer_z_le_M)
    LocalDataTh.trans_A LocalDataTh.surj_A

end Certified

end CFSG.EvenSporadicStandard.ThStd
