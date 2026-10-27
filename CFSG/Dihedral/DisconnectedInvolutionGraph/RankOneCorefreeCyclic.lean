module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem corefree_cyclic_two_sylow_cyclic (hcore : oddCore G = ⊥)
    (sylow : Sylow 2 G) (hcyclic : IsCyclic (sylow : Subgroup G))
    (heven : Even (Nat.card G)) : IsCyclic G := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
  let transfer := MonoidHom.transferSylow sylow (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (sylow : Subgroup G) := hcyclic.isComplement' hmin
  have hodd : Odd (Nat.card transfer.ker) := by
    rw [← hcomplement.index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun hevenIndex => sylow.not_dvd_index
      (even_iff_two_dvd.mp hevenIndex))
  have hkerLe := normal_odd_le_oddCore transfer.ker inferInstance hodd
  rw [hcore] at hkerLe
  have hkerBot : transfer.ker = ⊥ := bot_unique hkerLe
  have hsylowTop : (sylow : Subgroup G) = ⊤ := by
    have hsup := hcomplement.sup_eq_top
    simpa only [hkerBot, bot_sup_eq] using hsup
  obtain ⟨generator, hgenerates⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top (sylow : Subgroup G)).mp hcyclic
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  exact ⟨generator, hgenerates.trans hsylowTop⟩

theorem corefree_cyclic_two_sylow_involution_central (hcore : oddCore G = ⊥)
    (sylow : Sylow 2 G) (hcyclic : IsCyclic (sylow : Subgroup G))
    (involution : Involution G) : (involution : G) ∈ Subgroup.center G := by
  have heven : Even (Nat.card G) := by
    apply even_iff_two_dvd.mpr
    have hdiv := orderOf_dvd_natCard (involution : G)
    rwa [involution.property] at hdiv
  let _ := corefree_cyclic_two_sylow_cyclic hcore sylow hcyclic heven
  exact Subgroup.mem_center_iff.mpr (fun element => mul_comm' element involution)

end CFSG.DisconnectedInvolutionGraph.Helpers
