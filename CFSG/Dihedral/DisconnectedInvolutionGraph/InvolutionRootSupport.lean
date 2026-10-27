module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneInvolutions
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InducedSupportedFunction

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem involution_zpowers_members (involution : Involution G) (element : G)
    (hmem : element ∈ Subgroup.zpowers (involution : G)) :
    element = 1 ∨ element = (involution : G) := by
  classical
  obtain ⟨exponent, hexponent, hequal⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hmem)
  have hbound : exponent < 2 := by simpa only [Finset.mem_range, involution.property] using hexponent
  have hcases : exponent = 0 ∨ exponent = 1 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl (by simpa only [pow_zero] using hequal.symm)
  · exact Or.inr (by simpa only [pow_one] using hequal.symm)

theorem involution_zpowers_normalizer_eq_centralizer (involution : Involution G) :
    Subgroup.normalizer (Subgroup.zpowers (involution : G) : Set G) =
      Subgroup.centralizer ({(involution : G)} : Set G) := by
  apply le_antisymm
  · intro actor hactor
    have hmem := (Subgroup.mem_normalizer_iff.mp hactor (involution : G)).mp
      (Subgroup.mem_zpowers (involution : G))
    rcases involution_zpowers_members involution _ hmem with hone | hequal
    · have hinvolution : (involution : G) = 1 := by
        have heq := congrArg (fun element => actor⁻¹ * element * actor) hone
        calc
          (involution : G) = actor⁻¹ * (actor * (involution : G) * actor⁻¹) * actor := by group
          _ = 1 := by simpa only [mul_one, inv_mul_cancel] using heq
      have horder := involution.property
      rw [hinvolution, orderOf_one] at horder
      omega
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      have heq := congrArg (fun element => element * actor) hequal
      simpa only [inv_mul_cancel_right] using heq
  · intro actor hactor
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro element hmem
    obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcommute : Commute actor (involution : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hactor
    exact (hcommute.zpow_right exponent).symm.eq

theorem involution_root_ti (involution : Involution G) :
    IsTISupport (cyclicRootSet (involution : G))
      (Subgroup.centralizer ({(involution : G)} : Set G)) := by
  rw [← involution_zpowers_normalizer_eq_centralizer involution]
  apply cyclic_root_set_ti
  intro hone
  have horder := involution.property
  rw [hone, orderOf_one] at horder
  omega

omit [Finite G] in
theorem rank_one_involution_centralizer_unique
    (hrank : NoCommutingDistinctInvolutions G) (involution other : Involution G)
    (hmem : (other : G) ∈ Subgroup.centralizer ({(involution : G)} : Set G)) :
    other = involution :=
  hrank other involution (Subgroup.mem_centralizer_singleton_iff.mp hmem)

theorem rank_one_involution_root_iff_even
    (hrank : NoCommutingDistinctInvolutions G) (involution : Involution G) (root : G) :
    root ∈ cyclicRootSet (involution : G) ↔
      root ∈ Subgroup.centralizer ({(involution : G)} : Set G) ∧ Even (orderOf root) := by
  constructor
  · intro hroot
    refine ⟨cyclic_root_set_centralizes (involution : G) root hroot, ?_⟩
    have hdiv := orderOf_dvd_of_mem_zpowers hroot
    rw [involution.property] at hdiv
    exact even_iff_two_dvd.mpr hdiv
  · rintro ⟨hcentralizer, heven⟩
    have hdiv : 2 ∣ orderOf root := even_iff_two_dvd.mp heven
    have horder : orderOf (root ^ (orderOf root / 2)) = 2 :=
      orderOf_pow_orderOf_div (orderOf_pos root).ne' hdiv
    let other : Involution G := ⟨root ^ (orderOf root / 2), horder⟩
    have hequal := rank_one_involution_centralizer_unique hrank involution other
      ((Subgroup.centralizer ({(involution : G)} : Set G)).pow_mem hcentralizer _)
    have hvalue : (involution : G) = root ^ (orderOf root / 2) :=
      (congrArg Subtype.val hequal).symm
    change (involution : G) ∈ Subgroup.zpowers root
    rw [hvalue]
    exact Subgroup.npow_mem_zpowers root _

variable {Scalar : Type*} [Field Scalar] [Fintype G]

theorem involution_root_induced_pair_zero
    (involution : Involution G)
    (hunique : ∀ other : Involution G,
      (other : G) ∈ Subgroup.centralizer ({(involution : G)} : Set G) → other = involution)
    (function : G → Scalar)
    (hzero : ∀ element ∉ cyclicRootSet (involution : G), function element = 0)
    (first second : Involution G) :
    inducedSupportedFunction (Subgroup.centralizer ({(involution : G)} : Set G)) function
      ((first : G) * second) = 0 := by
  apply inducedSupportedFunction_pair_zero _ _ (involution_root_ti involution)
    (fun member hmem => (cyclic_root_set_inverse (involution : G) member).mpr hmem)
    function hzero
  intro firstInside secondInside hfirst hsecond
  rw [hunique firstInside hfirst, hunique secondInside hsecond]
  have hsquare : (involution : G) * involution = 1 := by
    have hpower := pow_orderOf_eq_one (involution : G)
    simpa only [involution.property, pow_two] using hpower
  rw [hsquare]
  exact hzero 1 (involution_root_ti involution).identity_not_mem

end CFSG.DisconnectedInvolutionGraph.Helpers
