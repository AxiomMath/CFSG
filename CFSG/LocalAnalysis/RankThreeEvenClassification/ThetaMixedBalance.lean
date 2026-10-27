module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlane
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CentralQuotient

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem thetaCoreOf_map_eq_of_injective {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (prime : ℕ) (hprime : prime.Prime) (homomorphism : G →* H)
    (hinjective : Function.Injective homomorphism) (subgroup : Subgroup G) :
    (thetaCoreOf prime subgroup).map homomorphism =
      thetaCoreOf prime (subgroup.map homomorphism) := by
  apply thetaCoreOf_map_eq_of_central_kernel prime hprime homomorphism
  rw [MonoidHom.ker_eq_bot homomorphism hinjective]
  exact bot_le

theorem element_centralizer_subtype_map {G : Type u} [Group G]
    (larger : Subgroup G) (element : G) (hmem : element ∈ larger) :
    (Subgroup.centralizer ({⟨element, hmem⟩} : Set larger)).map larger.subtype =
      larger ⊓ Subgroup.centralizer ({element} : Set G) := by
  ext other
  constructor
  · intro hother
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hother
    exact ⟨preimage.property, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hpreimage))⟩
  · intro hother
    exact Subgroup.mem_map.mpr ⟨⟨other, hother.1⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hother.2)), rfl⟩

theorem thetaCoreOf_element_centralizer_subtype_map {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (larger : Subgroup G)
    (element : G) (hmem : element ∈ larger) :
    (thetaCoreOf prime (Subgroup.centralizer ({⟨element, hmem⟩} : Set larger))).map larger.subtype =
      thetaCoreOf prime (larger ⊓ Subgroup.centralizer ({element} : Set G)) := by
  rw [thetaCoreOf_map_eq_of_injective prime hprime larger.subtype larger.subtype_injective,
    element_centralizer_subtype_map]

theorem theta_element_centralizer_intersection_le {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (larger : Subgroup G) (element : G) :
    larger ⊓ thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) ≤
      thetaCoreOf prime (larger ⊓ Subgroup.centralizer ({element} : Set G)) := by
  intro other hother
  exact intersection_thetaCoreOf_le prime hprime _ _ inf_le_right
    ⟨⟨hother.1, thetaCoreOf_le prime _ hother.2⟩, hother.2⟩

theorem theta_mixed_commutator_le_local_alpha {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane larger : Subgroup G)
    (hle : plane ≤ larger) (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    ⁅larger ⊓ thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), plane⁆ ≤
      (thetaPlaneAlpha prime (plane.subgroupOf larger)).map larger.subtype := by
  have helement : element ∈ larger := hle hmem
  have hthetaMap := thetaCoreOf_element_centralizer_subtype_map prime hprime larger element helement
  have hcommutatorMap :
      (⁅thetaCoreOf prime (Subgroup.centralizer ({⟨element, helement⟩} : Set larger)),
        plane.subgroupOf larger⁆).map larger.subtype =
        ⁅thetaCoreOf prime (larger ⊓ Subgroup.centralizer ({element} : Set G)), plane⁆ := by
    rw [Subgroup.map_commutator, hthetaMap, Subgroup.map_subgroupOf_eq_of_le hle]
  apply le_trans (Subgroup.commutator_mono
    (theta_element_centralizer_intersection_le prime hprime larger element) le_rfl)
  rw [← hcommutatorMap]
  apply Subgroup.map_mono
  apply le_sup_of_le_left
  exact le_iSup_of_le (⟨element, helement⟩ : larger) (le_iSup_of_le hmem
    (le_iSup_of_le (fun heq => hne (congrArg Subtype.val heq)) le_rfl))

theorem theta_mixed_balance_of_local_alpha {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (hcomm : IsMulCommutative plane)
    (first second : G) (hfirst : first ∈ plane) (hsecond : second ∈ plane) (hsecondNe : second ≠ 1)
    (hlocal : thetaPlaneAlpha prime
      (plane.subgroupOf (Subgroup.centralizer ({first} : Set G))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({first} : Set G)) prime) :
    ⁅Subgroup.centralizer ({first} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)), plane⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)) := by
  have hle := commutative_plane_le_element_centralizer plane hcomm first hfirst
  exact (theta_mixed_commutator_le_local_alpha prime hprime plane _ hle second hsecond hsecondNe).trans
    (Subgroup.map_mono (f := (Subgroup.centralizer ({first} : Set G)).subtype) hlocal)

theorem thetaPlaneIntersection_fixed_le_local_intersection
    {G : Type u} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (plane larger : Subgroup G) :
    larger ⊓ thetaPlaneIntersection prime plane ≤
      (thetaPlaneIntersection prime (plane.subgroupOf larger)).map larger.subtype := by
  intro other hother
  apply Subgroup.mem_map.mpr
  refine ⟨⟨other, hother.1⟩, ?_, rfl⟩
  simp only [thetaPlaneIntersection, Subgroup.mem_iInf]
  intro element helement hne
  have helementNe : (element : G) ≠ 1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hcore := thetaPlaneIntersection_le prime plane element helement helementNe hother.2
  have hlocal := theta_element_centralizer_intersection_le prime hprime larger element
    (show other ∈ larger ⊓ thetaCoreOf prime (Subgroup.centralizer ({(element : G)} : Set G)) from
      ⟨hother.1, hcore⟩)
  rw [← thetaCoreOf_element_centralizer_subtype_map prime hprime larger element element.property]
    at hlocal
  obtain ⟨preimage, hpreimage, heq⟩ := Subgroup.mem_map.mp hlocal
  have hpreimageEq : preimage = (⟨other, hother.1⟩ : larger) := Subtype.ext heq
  exact hpreimageEq ▸ hpreimage

theorem thetaPlaneIntersection_fixed_le_theta_of_local_alpha
    {G : Type u} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (plane larger : Subgroup G)
    (hlocal : thetaPlaneAlpha prime (plane.subgroupOf larger) ≤
      solvablePrimeComplementCore larger prime) :
    larger ⊓ thetaPlaneIntersection prime plane ≤ thetaCoreOf prime larger := by
  exact (thetaPlaneIntersection_fixed_le_local_intersection prime hprime plane larger).trans
    (Subgroup.map_mono (f := larger.subtype) (le_sup_right.trans hlocal))

end CFSG.RankThreeEvenClassification.Helpers
