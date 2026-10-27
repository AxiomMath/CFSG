module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.TwoInvolutions

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

@[expose] def conjugateSubgroup (subgroup : Subgroup G) (g : G) : Subgroup G :=
  subgroup.comap (MulAut.conj g⁻¹).toMonoidHom

@[expose] def IsStronglyEmbedded (subgroup : Subgroup G) : Prop :=
  subgroup ≠ ⊤ ∧ Even (Nat.card subgroup) ∧
    ∀ g : G, g ∉ subgroup → Odd (Nat.card ↥(subgroup ⊓ conjugateSubgroup subgroup g))

theorem componentStabilizer_involution_iff [Finite G] (t u : Involution G) :
    (u : G) ∈ componentStabilizer t ↔
      (disconnectedInvolutionCommutingGraph G).Reachable t u := by
  constructor
  · intro hu
    rcases Nat.even_or_odd (orderOf ((t : G) * u)) with heven | hodd
    · exact reachable_of_even_product t u heven
    · obtain ⟨exponent, hconj⟩ := odd_product_conjugates t u hodd
      have hproduct : (t : G) * u ∈ componentStabilizer t :=
        (componentStabilizer t).mul_mem (componentStabilizer_base_mem t) hu
      have hpower := (componentStabilizer t).pow_mem hproduct exponent
      rw [mem_componentStabilizer_iff, hconj] at hpower
      exact hpower
  · exact involution_mem_componentStabilizer

theorem componentStabilizer_proper [Finite G] (t : Involution G)
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    componentStabilizer t ≠ ⊤ := by
  intro htop
  apply hdisc
  intro u v
  have htu : (disconnectedInvolutionCommutingGraph G).Reachable t u :=
    (componentStabilizer_involution_iff t u).mp (by rw [htop]; trivial)
  have htv : (disconnectedInvolutionCommutingGraph G).Reachable t v :=
    (componentStabilizer_involution_iff t v).mp (by rw [htop]; trivial)
  exact htu.symm.trans htv

theorem componentStabilizer_even (t : Involution G) :
    Even (Nat.card (componentStabilizer t)) := by
  apply even_iff_two_dvd.mpr
  have hdiv := (componentStabilizer t).orderOf_dvd_natCard (componentStabilizer_base_mem t)
  simpa only [t.property] using hdiv

theorem intersection_involution_forces_mem [Finite G] (t : Involution G) (g : G)
    (u : Involution G)
    (hu : (u : G) ∈ componentStabilizer t ⊓ conjugateSubgroup (componentStabilizer t) g) :
    g ∈ componentStabilizer t := by
  obtain ⟨humem, hconjmem⟩ := Subgroup.mem_inf.mp hu
  have hpath := (componentStabilizer_involution_iff t u).mp humem
  have hconjpath := (componentStabilizer_involution_iff t (conjugateInvolution g⁻¹ u)).mp
    hconjmem
  have hmapped := reachable_conjugate hconjpath g
  simp only [← conjugateInvolution_mul, mul_inv_cancel, conjugateInvolution_one] at hmapped
  exact hpath.trans hmapped.symm

theorem odd_card_of_no_involutions [Finite G] (hno : ∀ element : G, orderOf element ≠ 2) :
    Odd (Nat.card G) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := G) 2
    (even_iff_two_dvd.mp heven)
  exact hno element horder

theorem componentStabilizer_intersection_odd [Finite G] (t : Involution G) (g : G)
    (houtside : g ∉ componentStabilizer t) :
    Odd (Nat.card ↥(componentStabilizer t ⊓ conjugateSubgroup (componentStabilizer t) g)) := by
  apply odd_card_of_no_involutions
  intro element horder
  let u : Involution G := ⟨element, (Subgroup.orderOf_coe element).trans horder⟩
  exact houtside (intersection_involution_forces_mem t g u element.property)

theorem componentStabilizer_stronglyEmbedded [Finite G] (t : Involution G)
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    IsStronglyEmbedded (componentStabilizer t) :=
  ⟨componentStabilizer_proper t hdisc, componentStabilizer_even t,
    componentStabilizer_intersection_odd t⟩

theorem disconnected_exists_stronglyEmbedded [Finite G]
    (hdisc : ¬ (disconnectedInvolutionCommutingGraph G).Preconnected) :
    ∃ subgroup : Subgroup G, IsStronglyEmbedded subgroup := by
  classical
  change ¬ ∀ t u : Involution G,
    (disconnectedInvolutionCommutingGraph G).Reachable t u at hdisc
  push Not at hdisc
  obtain ⟨t, u, hnopath⟩ := hdisc
  refine ⟨componentStabilizer t, ?_⟩
  apply componentStabilizer_stronglyEmbedded
  exact fun hconnected => hnopath (hconnected t u)

end CFSG.DisconnectedInvolutionGraph.Helpers
