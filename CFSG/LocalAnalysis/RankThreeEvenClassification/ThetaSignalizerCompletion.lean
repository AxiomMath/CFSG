module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneComparison
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneCondition

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] noncomputable def thetaActorGenerated {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) : Subgroup G :=
  ⨆ (element : G) (_ : element ∈ actor) (_ : element ≠ 1), thetaActorSignalizer prime actor element

theorem thetaActorSignalizer_le_generated {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) :
    thetaActorSignalizer prime actor element ≤ thetaActorGenerated prime actor := by
  exact le_iSup_of_le element (le_iSup_of_le hmem (le_iSup_of_le hne le_rfl))

theorem thetaActorGenerated_normalized {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) :
    actor ≤ Subgroup.normalizer (thetaActorGenerated prime actor : Set G) := by
  apply normalizes_iSup
  intro element
  apply normalizes_iSup
  intro _
  apply normalizes_iSup
  intro _
  exact thetaActorSignalizer_normalized prime actor element

theorem thetaPlaneIntersection_actor_fixed_le_core
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hplaneLe : plane ≤ actor) (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    thetaPlaneIntersection prime plane ⊓ Subgroup.centralizer (actor : Set G) ≤
      thetaActorFixedCore prime actor := by
  let fixed := thetaPlaneIntersection prime plane ⊓ Subgroup.centralizer (actor : Set G)
  have hnormalized : Subgroup.centralizer (actor : Set G) ≤
      Subgroup.normalizer (fixed : Set G) :=
    normalizes_inf_of_normalizes_both _ _ _
      ((Subgroup.centralizer_le hplaneLe).trans
        (centralizer_plane_normalizes_intersection prime hprime plane)) Subgroup.le_normalizer
  have hsolvable : Group.IsSolvable fixed := by
    have : Group.IsSolvable (thetaPlaneIntersection prime plane) :=
      thetaPlaneIntersection_solvable prime hprime plane element hmem hne
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  exact normal_solvable_primeComplement_le_thetaCoreOf prime fixed _ inf_le_right
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnormalized) hsolvable
    (fun hdiv => thetaPlaneIntersection_prime_complement prime hprime plane element hmem hne
      (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left)))

theorem thetaPlaneAlpha_le_actor_generated
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hpgroup : IsPGroup prime actor) (hplaneLe : plane ≤ actor)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1) :
    thetaPlaneAlpha prime plane ≤ thetaActorGenerated prime actor := by
  have hsignalizerLe := thetaActorSignalizer_le_generated prime actor element (hplaneLe hmem) hne
  apply sup_le
  · apply iSup_le
    intro member
    apply iSup_le
    intro hmember
    apply iSup_le
    intro hmemberNe
    exact (Subgroup.commutator_mono le_rfl hplaneLe).trans
      (le_sup_left.trans (thetaActorSignalizer_le_generated prime actor member
        (hplaneLe hmember) hmemberNe))
  · let intersection := thetaPlaneIntersection prime plane
    have hnormalized : actor ≤ Subgroup.normalizer (intersection : Set G) :=
      actor_normalizes_thetaPlaneIntersection prime hprime actor plane hcomm hplaneLe
    have hcomplement := thetaPlaneIntersection_prime_complement prime hprime plane element hmem hne
    change intersection ≤ _
    rw [coprime_commutator_centralizer_factorization prime hprime actor intersection
      hpgroup hcomplement hnormalized]
    apply sup_le
    · exact (Subgroup.commutator_mono (thetaPlaneIntersection_le prime plane element hmem hne)
        le_rfl).trans (le_sup_left.trans hsignalizerLe)
    · exact (thetaPlaneIntersection_actor_fixed_le_core prime hprime actor plane hplaneLe
        element hmem hne).trans (le_sup_right.trans hsignalizerLe)

theorem thetaPlaneAlpha_solvable_of_generated_solvable
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hab : IsElemAbelian prime actor) (hplaneLe : plane ≤ actor)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1)
    (hcompletion : Group.IsSolvable (thetaActorGenerated prime actor)) :
    Group.IsSolvable (thetaPlaneAlpha prime plane) := by
  have : Group.IsSolvable (thetaActorGenerated prime actor) := hcompletion
  have hle := thetaPlaneAlpha_le_actor_generated prime hprime actor plane hab.1
    (isElemAbelian_isPGroup prime actor hab) hplaneLe element hmem hne
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem thetaPlaneAlpha_prime_complement_of_generated_prime_complement
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hab : IsElemAbelian prime actor) (hplaneLe : plane ≤ actor)
    (element : G) (hmem : element ∈ plane) (hne : element ≠ 1)
    (hcompletion : ¬prime ∣ Nat.card (thetaActorGenerated prime actor)) :
    ¬prime ∣ Nat.card (thetaPlaneAlpha prime plane) := by
  have hle := thetaPlaneAlpha_le_actor_generated prime hprime actor plane hab.1
    (isElemAbelian_isPGroup prime actor hab) hplaneLe element hmem hne
  exact fun hdiv => hcompletion (hdiv.trans (Subgroup.card_dvd_of_le hle))

theorem ThetaPlaneCondition.comparison_or_obstruction
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (hcondition : ThetaPlaneCondition prime actor)
    (firstPlane secondPlane : Subgroup G) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor) (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondCard : Nat.card secondPlane = prime ^ 2) :
    thetaPlaneAlpha prime firstPlane ≤ thetaPlaneAlpha prime secondPlane ∨
      ∃ element ∈ secondPlane, element ∉ firstPlane ∧ ¬CentralLineThetaAt prime actor element := by
  exact thetaPlaneAlpha_comparison_or_central_line_obstruction prime hprime actor hab hactorCard
    firstPlane secondPlane hfirstLe hsecondLe hfirstCard hsecondCard
    (fun first hfirst hfirstNe second hsecond hsecondNe =>
      ThetaPlaneCondition.mixed_balance prime hprime actor hab hcondition first second
        hfirst hsecond hfirstNe hsecondNe)

end CFSG.RankThreeEvenClassification.Helpers
