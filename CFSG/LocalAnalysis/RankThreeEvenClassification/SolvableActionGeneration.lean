module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionTransport

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem action_preserves_commutator {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (member : actor) (element : acted) (helement : element ∈ commutator acted) :
    member • element ∈ commutator acted := by
  have hmap : (commutator acted).map (MulDistribMulAction.toMonoidHom acted member) ≤
      commutator acted := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  exact hmap ⟨element, helement, rfl⟩

theorem solvable_action_fixed_generated_eq_top {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [Group acted] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted] (prime : ℕ) (hprime : prime.Prime)
    (hpower : ∀ member : actor, member ^ prime = 1)
    (hcard : Nat.card actor = prime ^ 2) (hcomplement : ¬prime ∣ Nat.card acted) :
    actionFixedGenerated (actor := actor) (acted := acted) = ⊤ := by
  classical
  induction hsize : Nat.card acted using Nat.strong_induction_on generalizing acted with
  | h size ih =>
    by_cases htrivial : Subsingleton acted
    · have : Subsingleton acted := htrivial
      exact Subsingleton.elim _ _
    have : Nontrivial acted := not_subsingleton_iff_nontrivial.mp htrivial
    have hinvariant : ∀ member : actor, ∀ element ∈ commutator acted,
        member • element ∈ commutator acted := action_preserves_commutator
    let : MulDistribMulAction actor (commutator acted) :=
      invariantSubgroupAction (commutator acted) hinvariant
    have hsmaller : Nat.card (commutator acted) < size := by
      let : Fintype acted := Fintype.ofFinite _
      let : Fintype (commutator acted) := Fintype.ofFinite _
      rw [← hsize, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      apply Fintype.card_lt_of_injective_not_surjective (commutator acted).subtype
        Subtype.val_injective
      intro hsurjective
      have htop : commutator acted = ⊤ := by
        rw [← Subgroup.range_subtype (commutator acted), MonoidHom.range_eq_top.mpr hsurjective]
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial acted).ne htop
    have hderivedComplement : ¬prime ∣ Nat.card (commutator acted) :=
      fun hdiv => hcomplement (hdiv.trans (Subgroup.card_subgroup_dvd_card (commutator acted)))
    have hderivedTop := ih (Nat.card (commutator acted)) hsmaller
      (acted := commutator acted) hderivedComplement rfl
    have hderivedLe : commutator acted ≤ actionFixedGenerated (actor := actor) (acted := acted) := by
      have hmap := actionFixedGenerated_map_le (actor := actor) (commutator acted).subtype
        (fun _ _ => rfl)
      rw [hderivedTop] at hmap
      intro element helement
      exact hmap ⟨⟨element, helement⟩, Subgroup.mem_top _, rfl⟩
    let : MulDistribMulAction actor (Abelianization acted) :=
      invariantQuotientAction (commutator acted) hinvariant
    let quotient : acted →* Abelianization acted := Abelianization.of
    have hsurjective : Function.Surjective quotient := QuotientGroup.mk'_surjective _
    have hequivariant : ∀ member : actor, ∀ element : acted,
        quotient (member • element) = member • quotient element := fun _ _ => rfl
    have hquotientComplement : ¬prime ∣ Nat.card (Abelianization acted) :=
      fun hdiv => hcomplement (hdiv.trans (Subgroup.card_quotient_dvd_card (commutator acted)))
    have hquotientTop := abelian_action_fixed_generated_eq_top prime hprime hpower
      hcard hquotientComplement (acted := Abelianization acted)
    have hkernel : quotient.ker = commutator acted := Abelianization.ker_of acted
    have hmapTop := actionFixedGenerated_map_eq_of_pGroup_prime_complement_kernel
      prime hprime (IsPGroup.of_card hcard) quotient hsurjective hequivariant
      (hkernel.symm ▸ hderivedComplement)
    rw [hquotientTop] at hmapTop
    have hcomap := Subgroup.comap_map_eq_self (hkernel ▸ hderivedLe)
    rw [hmapTop, Subgroup.comap_top] at hcomap
    exact hcomap.symm

end CFSG.RankThreeEvenClassification.Helpers
