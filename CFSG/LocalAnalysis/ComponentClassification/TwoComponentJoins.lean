module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentSubnormal

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoComponentJoins

theorem exists_le_of_le_sSup {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (hcomponent : TwoComponents.IsTwoComponent component)
    (subgroups : Set (Subgroup G))
    (hsubnormal : ∀ subgroup ∈ subgroups, IsSubnormal subgroup ⊤)
    (hle : component ≤ sSup subgroups) : ∃ subgroup ∈ subgroups, component ≤ subgroup := by
  classical
  by_contra hnone
  let quotient := QuotientGroup.mk' (componentClassificationOddCore G)
  let image := component.map quotient
  have hkernel : quotient.ker = componentClassificationOddCore G := QuotientGroup.ker_mk' _
  have hoddKernel : Odd (Nat.card quotient.ker) := by
    rw [hkernel]
    exact OddCore.odd_card G
  have hcentralizes : sSup subgroups ≤ (Subgroup.centralizer (image : Set _)).comap quotient := by
    apply sSup_le
    intro subgroup hmem
    have hnotLe : ¬ component ≤ subgroup := fun hcontained => hnone ⟨subgroup, hmem, hcontained⟩
    have hnotImageLe : ¬ image ≤ subgroup.map quotient := by
      intro himages
      exact hnotLe (TwoComponentSubnormal.le_of_odd_kernel_map_le quotient
        (QuotientGroup.mk'_surjective _) hoddKernel component subgroup hcomponent
          (hsubnormal subgroup hmem) himages)
    have himageSubnormal : IsSubnormal (subgroup.map quotient) ⊤ := by
      have hchain := Components.chain_map quotient (hsubnormal subgroup hmem)
      rwa [Subgroup.map_top_of_surjective quotient (QuotientGroup.mk'_surjective _)] at hchain
    have hcommutes := (LocalComponents.subnormal_contains_or_commutes image (subgroup.map quotient)
      hcomponent.2.1 himageSubnormal).resolve_left hnotImageLe
    rw [Subgroup.commutator_comm] at hcommutes
    exact Subgroup.map_le_iff_le_comap.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)
  have himageCentralizes : image ≤ Subgroup.centralizer (image : Set _) :=
    Subgroup.map_le_iff_le_comap.mpr (hle.trans hcentralizes)
  have himageCommutator : ⁅image, image⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr himageCentralizes
  let : Group.IsPerfect image := ⟨hcomponent.2.1.2.2.1⟩
  have himageBot : image = ⊥ := by
    rwa [Subgroup.commutator_eq_self] at himageCommutator
  let : Nontrivial image := Quasisimple.nontrivial hcomponent.2.1.2.2
  exact (image.nontrivial_iff_ne_bot.mp inferInstance) himageBot

theorem component_sets_eq_of_sSup_eq {G : Type*} [Group G] [Finite G]
    (first second : Set (Subgroup G))
    (hfirst : ∀ component ∈ first, TwoComponents.IsTwoComponent component)
    (hsecond : ∀ component ∈ second, TwoComponents.IsTwoComponent component)
    (hjoins : sSup first = sSup second) : first = second := by
  apply Set.Subset.antisymm
  · intro component hmem
    have hle : component ≤ sSup second := by rw [← hjoins]; exact le_sSup hmem
    obtain ⟨containing, hcontaining, hcontained⟩ := exists_le_of_le_sSup component
      (hfirst component hmem) second (fun subgroup hmember => (hsecond subgroup hmember).1) hle
    have heq := TwoComponentSubnormal.eq_of_le component containing
      (hfirst component hmem) (hsecond containing hcontaining) hcontained
    exact heq ▸ hcontaining
  · intro component hmem
    have hle : component ≤ sSup first := by rw [hjoins]; exact le_sSup hmem
    obtain ⟨containing, hcontaining, hcontained⟩ := exists_le_of_le_sSup component
      (hsecond component hmem) first (fun subgroup hmember => (hfirst subgroup hmember).1) hle
    have heq := TwoComponentSubnormal.eq_of_le component containing
      (hsecond component hmem) (hfirst containing hcontaining) hcontained
    exact heq ▸ hcontaining

end CFSG.ComponentClassification.TwoComponentJoins
