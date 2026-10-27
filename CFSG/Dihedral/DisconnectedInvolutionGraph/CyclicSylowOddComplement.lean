module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem cyclic_two_sylow_oddCore_complement (sylow : Sylow 2 G)
    (hcyclic : IsCyclic (sylow : Subgroup G)) (heven : Even (Nat.card G)) :
    (oddCore G).IsComplement' (sylow : Subgroup G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
  let transfer := MonoidHom.transferSylow sylow (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (sylow : Subgroup G) := hcyclic.isComplement' hmin
  have hkerOdd : Odd (Nat.card transfer.ker) := by
    rw [← hcomplement.index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun hevenIndex => sylow.not_dvd_index
      (even_iff_two_dvd.mp hevenIndex))
  have hkerLe : transfer.ker ≤ oddCore G := normal_odd_le_oddCore _ inferInstance hkerOdd
  have hcoreLe : oddCore G ≤ transfer.ker := by
    intro element hmem
    change transfer element = 1
    by_contra hnonidentity
    have htwo : 2 ∣ orderOf (transfer element) := sylow.isPGroup'.dvd_orderOf hnonidentity
    have hdiv := htwo.trans ((orderOf_map_dvd transfer element).trans
      ((oddCore G).orderOf_dvd_natCard hmem))
    exact (oddCore_odd (G := G)).not_two_dvd_nat hdiv
  rw [le_antisymm hcoreLe hkerLe]
  exact hcomplement

theorem cyclic_two_sylow_oddCore_quotient (sylow : Sylow 2 G)
    (hcyclic : IsCyclic (sylow : Subgroup G)) (heven : Even (Nat.card G)) :
    let _ := oddCore_normal (G := G)
    IsPGroup 2 (G ⧸ oddCore G) := by
  let _ := oddCore_normal (G := G)
  let equivalence := (cyclic_two_sylow_oddCore_complement sylow hcyclic heven).symm.QuotientMulEquiv
  exact sylow.isPGroup'.of_equiv equivalence.symm

end CFSG.DisconnectedInvolutionGraph.Helpers
