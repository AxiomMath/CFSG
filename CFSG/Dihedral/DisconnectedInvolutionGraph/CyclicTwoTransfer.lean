module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem cyclic_involutions_unique [IsCyclic G] (first second : Involution G) :
    first = second := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (Involution G)
  have hdiv : 2 ∣ Fintype.card G := by
    have hdiv := orderOf_dvd_card (x := (first : G))
    rwa [first.property] at hdiv
  have hcard : Fintype.card (Involution G) = 1 := by
    rw [Fintype.card_subtype]
    exact (IsCyclic.card_orderOf_eq_totient hdiv).trans Nat.totient_two
  have hsubsingleton : Subsingleton (Involution G) :=
    (Fintype.card_le_one_iff_subsingleton.mp (by omega))
  exact hsubsingleton.elim first second

theorem cyclic_two_sylow_transfer_involutions_same (sylow : Sylow 2 G)
    (hcyclic : IsCyclic (sylow : Subgroup G)) (heven : Even (Nat.card G))
    (first second : Involution G) :
    MonoidHom.transferSylow sylow
      (hcyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr
        (even_iff_two_dvd.mp heven))) (first : G) =
    MonoidHom.transferSylow sylow
      (hcyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr
        (even_iff_two_dvd.mp heven))) (second : G) ∧
    orderOf (MonoidHom.transferSylow sylow
      (hcyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr
        (even_iff_two_dvd.mp heven))) (first : G)) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclic (sylow : Subgroup G) := hcyclic
  have hmin : (Nat.card G).minFac = 2 :=
    (Nat.minFac_eq_two_iff _).mpr (even_iff_two_dvd.mp heven)
  let transfer := MonoidHom.transferSylow sylow (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (sylow : Subgroup G) := hcyclic.isComplement' hmin
  have hkerOdd : Odd (Nat.card transfer.ker) := by
    rw [← hcomplement.index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun hevenIndex => sylow.not_dvd_index
      (even_iff_two_dvd.mp hevenIndex))
  have horder : ∀ involution : Involution G, orderOf (transfer (involution : G)) = 2 := by
    intro involution
    have hsquare : transfer (involution : G) ^ 2 = 1 := by
      rw [← map_pow]
      have htwo : (involution : G) ^ 2 = 1 := by
        simpa only [involution.property] using pow_orderOf_eq_one (involution : G)
      rw [htwo, map_one]
    have hnonidentity : transfer (involution : G) ≠ 1 := by
      intro heq
      have hmem : (involution : G) ∈ transfer.ker := heq
      have hoddOrder := hkerOdd.of_dvd_nat (transfer.ker.orderOf_dvd_natCard hmem)
      rw [involution.property] at hoddOrder
      exact (Nat.not_even_iff_odd.mpr hoddOrder) (by decide)
    exact orderOf_eq_prime hsquare hnonidentity
  refine ⟨?_, horder first⟩
  exact congrArg Subtype.val (cyclic_involutions_unique
    (⟨transfer first, horder first⟩ : Involution (sylow : Subgroup G))
    ⟨transfer second, horder second⟩)

end CFSG.DisconnectedInvolutionGraph.Helpers
