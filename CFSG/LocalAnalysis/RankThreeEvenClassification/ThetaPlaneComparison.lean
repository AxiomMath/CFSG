module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaQuotientCriterion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneIndependence

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def CentralLineThetaAt {G : Type u} [Group G] (prime : ℕ) (actor : Subgroup G)
    (element : G) : Prop :=
  ∀ (lineNormal : (Subgroup.zpowers (elementInCentralizer element)).Normal),
    let quotient := @QuotientGroup.mk' (Subgroup.centralizer ({element} : Set G))
      _ (Subgroup.zpowers (elementInCentralizer element)) lineNormal
    thetaPlaneAlpha prime ((actor.subgroupOf
      (Subgroup.centralizer ({element} : Set G))).map quotient) ≤
      solvablePrimeComplementCore
        ((Subgroup.centralizer ({element} : Set G)) ⧸
          Subgroup.zpowers (elementInCentralizer element)) prime

theorem centralLineThetaCriterion_iff {G : Type u} [Group G]
    (prime : ℕ) (actor : Subgroup G) : CentralLineThetaCriterion prime actor ↔
      ∀ element ∈ actor, element ≠ 1 → CentralLineThetaAt prime actor element := Iff.rfl

theorem thetaPlaneIntersection_le_alpha_of_fixed_theta
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor firstPlane secondPlane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor)
    (hsecondPower : ∀ member : secondPlane, member ^ prime = 1)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (element : G) (helement : element ∈ firstPlane) (hne : element ≠ 1)
    (hfixed : ∀ member ∈ secondPlane, member ≠ 1 →
      thetaPlaneIntersection prime firstPlane ⊓ Subgroup.centralizer ({member} : Set G) ≤
        thetaCoreOf prime (Subgroup.centralizer ({member} : Set G))) :
    thetaPlaneIntersection prime firstPlane ≤ thetaPlaneAlpha prime secondPlane := by
  let intersection := thetaPlaneIntersection prime firstPlane
  have hnormalized : secondPlane ≤ Subgroup.normalizer (intersection : Set G) :=
    hsecondLe.trans (actor_normalizes_thetaPlaneIntersection prime hprime actor firstPlane hcomm hfirstLe)
  have hsolvable := thetaPlaneIntersection_solvable prime hprime firstPlane element helement hne
  have hcomplement := thetaPlaneIntersection_prime_complement prime hprime firstPlane element helement hne
  have hcommutatorLe : ⁅intersection, secondPlane⁆ ≤ thetaPlaneAlpha prime secondPlane := by
    rw [repeated_action_commutator_generation prime hprime secondPlane intersection
      (fun first second => Subtype.ext (congrArg (fun value : actor => (value : G))
        (isMulCommutative_iff.mp hcomm ⟨first, hsecondLe first.property⟩
          ⟨second, hsecondLe second.property⟩))) hsecondPower hsecondCard hsolvable hcomplement hnormalized]
    apply iSup_le
    intro member
    apply iSup_le
    intro hmemberNe
    have hmemberAmbientNe : (member : G) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
    apply (Subgroup.commutator_mono (hfixed member member.property hmemberAmbientNe) le_rfl).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (member : G) (le_iSup_of_le member.property
      (le_iSup_of_le hmemberAmbientNe le_rfl))
  have hfixedLe : intersection ⊓ Subgroup.centralizer (secondPlane : Set G) ≤
      thetaPlaneIntersection prime secondPlane := by
    apply le_iInf
    intro member
    apply le_iInf
    intro hmember
    apply le_iInf
    intro hmemberNe
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmember))).trans
      (hfixed member hmember hmemberNe)
  change intersection ≤ thetaPlaneAlpha prime secondPlane
  rw [coprime_commutator_centralizer_factorization prime hprime secondPlane intersection
    (IsPGroup.of_card hsecondCard) hcomplement hnormalized]
  exact sup_le hcommutatorLe (hfixedLe.trans le_sup_right)

theorem thetaPlaneAlpha_le_other_of_outside_quotient_containment
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (firstPlane secondPlane : Subgroup G) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor) (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)))
    (hquotient : ∀ element ∈ secondPlane, element ∉ firstPlane →
      CentralLineThetaAt prime actor element) :
    thetaPlaneAlpha prime firstPlane ≤ thetaPlaneAlpha prime secondPlane := by
  have hsecondPower : ∀ member : secondPlane, member ^ prime = 1 :=
    fun member => Subtype.ext (hab.2 member (hsecondLe member.property))
  have hnontrivial : firstPlane ≠ ⊥ := by
    intro heq
    have hone := Subgroup.card_eq_one.mpr heq
    rw [hfirstCard] at hone
    nlinarith [hprime.two_le]
  obtain ⟨element, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnontrivial
  have hneAmbient : (element : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
  apply sup_le
  · apply iSup_le
    intro member
    apply iSup_le
    intro hmember
    apply iSup_le
    intro hmemberNe
    exact thetaPlaneCommutator_le_other_alpha_of_mixed prime hprime actor firstPlane secondPlane
      hab.1 hfirstLe hsecondLe hfirstCard hsecondPower hsecondCard hmixed member hmember hmemberNe
  · apply thetaPlaneIntersection_le_alpha_of_fixed_theta prime hprime actor firstPlane secondPlane
      hab.1 hfirstLe hsecondLe hsecondPower hsecondCard element element.property hneAmbient
    intro member hmember hmemberNe
    by_cases hmemberFirst : member ∈ firstPlane
    · exact inf_le_left.trans (thetaPlaneIntersection_le prime firstPlane member hmemberFirst hmemberNe)
    · have hlocal := rank_three_central_line_raw_plane_containment prime hprime actor hab hactorCard
        member (hsecondLe hmember) hmemberNe firstPlane hfirstLe hfirstCard
        (hquotient member hmember hmemberFirst)
      exact thetaPlaneIntersection_fixed_le_element_theta_of_local prime hprime firstPlane member hlocal

theorem thetaPlaneAlpha_comparison_or_central_line_obstruction
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (firstPlane secondPlane : Subgroup G) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor) (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G))) :
    thetaPlaneAlpha prime firstPlane ≤ thetaPlaneAlpha prime secondPlane ∨
      ∃ element ∈ secondPlane, element ∉ firstPlane ∧ ¬CentralLineThetaAt prime actor element := by
  classical
  by_cases hquotient : ∀ element ∈ secondPlane, element ∉ firstPlane →
      CentralLineThetaAt prime actor element
  · exact Or.inl (thetaPlaneAlpha_le_other_of_outside_quotient_containment prime hprime actor hab
      hactorCard firstPlane secondPlane hfirstLe hsecondLe hfirstCard hsecondCard hmixed hquotient)
  · push Not at hquotient
    exact Or.inr hquotient

end CFSG.RankThreeEvenClassification.Helpers
