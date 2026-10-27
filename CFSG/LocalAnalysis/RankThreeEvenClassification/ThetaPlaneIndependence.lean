module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryPlanes
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RepeatedActionGeneration

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem commutator_normalized_sup_le {G : Type u} [Group G]
    (normalFactor fixedFactor acting : Subgroup G)
    (hfixedNormalizes : fixedFactor ≤ Subgroup.normalizer (normalFactor : Set G))
    (hactingNormalizes : acting ≤ Subgroup.normalizer (normalFactor : Set G)) :
    ⁅normalFactor ⊔ fixedFactor, acting⁆ ≤ normalFactor ⊔ ⁅fixedFactor, acting⁆ := by
  apply Subgroup.commutator_le.mpr
  intro element helement member hmember
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := normalized_sup_factorization
    normalFactor fixedFactor hfixedNormalizes element helement
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hfirstJoin : first ∈ normalFactor ⊔ ⁅fixedFactor, acting⁆ := Subgroup.mem_sup_left hfirst
  have hsecondCommutator : ⁅second, member⁆ ∈ normalFactor ⊔ ⁅fixedFactor, acting⁆ :=
    Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hsecond hmember)
  have hfirstCommutator : ⁅first, member⁆ ∈ normalFactor :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hactingNormalizes
      (Subgroup.commutator_mem_commutator hfirst hmember)
  exact (normalFactor ⊔ ⁅fixedFactor, acting⁆).mul_mem
    ((normalFactor ⊔ ⁅fixedFactor, acting⁆).mul_mem
      ((normalFactor ⊔ ⁅fixedFactor, acting⁆).mul_mem hfirstJoin hsecondCommutator)
      ((normalFactor ⊔ ⁅fixedFactor, acting⁆).inv_mem hfirstJoin))
    (Subgroup.mem_sup_left hfirstCommutator)

theorem commutative_actor_normalizes_plane {G : Type u} [Group G]
    (actor plane : Subgroup G) (hcomm : IsMulCommutative actor) (hle : plane ≤ actor) :
    actor ≤ Subgroup.normalizer (plane : Set G) := by
  exact ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm).trans
    (Subgroup.centralizer_le hle)).trans (Subgroup.centralizer_le_normalizer _)

theorem actor_normalizes_thetaPlaneIntersection {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor plane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hle : plane ≤ actor) :
    actor ≤ Subgroup.normalizer (thetaPlaneIntersection prime plane : Set G) := by
  apply normalizes_iInf
  intro element
  apply normalizes_iInf
  intro hmem
  apply normalizes_iInf
  intro _
  exact commutative_plane_normalizes_element_theta prime hprime actor hcomm element (hle hmem)

theorem thetaPlaneIntersection_fixed_le_element_theta_of_local
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (plane : Subgroup G) (element : G)
    (hlocal : thetaPlaneAlpha prime
      (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime) :
    thetaPlaneIntersection prime plane ⊓ Subgroup.centralizer ({element} : Set G) ≤
      thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)) := by
  rw [inf_comm]
  exact thetaPlaneIntersection_fixed_le_theta_of_local_alpha prime hprime plane _ hlocal

theorem thetaPlaneIntersection_le_other_alpha_of_local
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor firstPlane secondPlane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor)
    (hsecondPower : ∀ member : secondPlane, member ^ prime = 1)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (firstElement : G) (hfirstElement : firstElement ∈ firstPlane) (hfirstNe : firstElement ≠ 1)
    (hlocal : ∀ element ∈ secondPlane, element ≠ 1 →
      thetaPlaneAlpha prime (firstPlane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime) :
    thetaPlaneIntersection prime firstPlane ≤ thetaPlaneAlpha prime secondPlane := by
  let intersection := thetaPlaneIntersection prime firstPlane
  have hnormalized : secondPlane ≤ Subgroup.normalizer (intersection : Set G) :=
    hsecondLe.trans (actor_normalizes_thetaPlaneIntersection prime hprime actor firstPlane hcomm hfirstLe)
  have hsolvable := thetaPlaneIntersection_solvable prime hprime firstPlane firstElement hfirstElement hfirstNe
  have hcomplement := thetaPlaneIntersection_prime_complement prime hprime firstPlane firstElement
    hfirstElement hfirstNe
  have hcommutatorLe : ⁅intersection, secondPlane⁆ ≤ thetaPlaneAlpha prime secondPlane := by
    rw [repeated_action_commutator_generation prime hprime secondPlane intersection
      (fun first second => Subtype.ext (congrArg (fun value : actor => (value : G))
        (isMulCommutative_iff.mp hcomm ⟨first, hsecondLe first.property⟩
          ⟨second, hsecondLe second.property⟩))) hsecondPower hsecondCard hsolvable hcomplement hnormalized]
    apply iSup_le
    intro member
    apply iSup_le
    intro hne
    have hmemberNe : (member : G) ≠ 1 := fun heq => hne (Subtype.ext heq)
    have hfixed := thetaPlaneIntersection_fixed_le_element_theta_of_local prime hprime firstPlane member
      (hlocal member member.property hmemberNe)
    apply (Subgroup.commutator_mono hfixed le_rfl).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (member : G) (le_iSup_of_le member.property
      (le_iSup_of_le hmemberNe le_rfl))
  have hfixedLe : intersection ⊓ Subgroup.centralizer (secondPlane : Set G) ≤
      thetaPlaneIntersection prime secondPlane := by
    apply le_iInf
    intro element
    apply le_iInf
    intro hmem
    apply le_iInf
    intro hne
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmem))).trans
      (thetaPlaneIntersection_fixed_le_element_theta_of_local prime hprime firstPlane element
        (hlocal element hmem hne))
  change intersection ≤ thetaPlaneAlpha prime secondPlane
  rw [coprime_commutator_centralizer_factorization prime hprime secondPlane intersection
    (IsPGroup.of_card hsecondCard) hcomplement hnormalized]
  exact sup_le hcommutatorLe (hfixedLe.trans le_sup_right)

theorem thetaPlaneCommutator_le_other_alpha_of_mixed
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor firstPlane secondPlane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor)
    (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondPower : ∀ member : secondPlane, member ^ prime = 1)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)))
    (element : G) (hmem : element ∈ firstPlane) (hne : element ≠ 1) :
    ⁅thetaCoreOf prime (Subgroup.centralizer ({element} : Set G)), firstPlane⁆ ≤
      thetaPlaneAlpha prime secondPlane := by
  let core := thetaCoreOf prime (Subgroup.centralizer ({element} : Set G))
  let derived := ⁅core, firstPlane⁆
  let normalFactor := ⁅derived, secondPlane⁆
  let fixedFactor := derived ⊓ Subgroup.centralizer (secondPlane : Set G)
  have hcoreNormalized : actor ≤ Subgroup.normalizer (core : Set G) :=
    commutative_plane_normalizes_element_theta prime hprime actor hcomm element (hfirstLe hmem)
  have hderivedLe : derived ≤ core :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hfirstLe.trans hcoreNormalized)
  have hderivedNormalized : actor ≤ Subgroup.normalizer (derived : Set G) :=
    normalizes_commutator_of_normalizes_both actor core firstPlane hcoreNormalized
      (commutative_actor_normalizes_plane actor firstPlane hcomm hfirstLe)
  have hsolvable : Group.IsSolvable derived := by
    have : Group.IsSolvable core := thetaCoreOf_solvable prime hprime _
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hderivedLe)
      (Subgroup.inclusion_injective hderivedLe)
  have hcomplement : ¬prime ∣ Nat.card derived :=
    fun hdiv => thetaCoreOf_prime_complement prime hprime _
      (hdiv.trans (Subgroup.card_dvd_of_le hderivedLe))
  have hfactor := coprime_commutator_centralizer_factorization prime hprime secondPlane derived
    (IsPGroup.of_card hsecondCard) hcomplement (hsecondLe.trans hderivedNormalized)
  have hnormalNormalized : firstPlane ≤ Subgroup.normalizer (normalFactor : Set G) :=
    hfirstLe.trans (normalizes_commutator_of_normalizes_both actor derived secondPlane
      hderivedNormalized (commutative_actor_normalizes_plane actor secondPlane hcomm hsecondLe))
  have hfixedNormalizes : fixedFactor ≤ Subgroup.normalizer (normalFactor : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left derived secondPlane)
  have hidempotent : ⁅derived, firstPlane⁆ = derived :=
    coprime_commutator_idempotent prime hprime firstPlane core (IsPGroup.of_card hfirstCard)
      (thetaCoreOf_prime_complement prime hprime _) (hfirstLe.trans hcoreNormalized)
  have hfixedCommutatorLe : ⁅fixedFactor, firstPlane⁆ ≤ thetaPlaneIntersection prime secondPlane := by
    apply le_iInf
    intro member
    apply le_iInf
    intro hmember
    apply le_iInf
    intro hmemberNe
    have hfixedLe : fixedFactor ≤ Subgroup.centralizer ({member} : Set G) ⊓ core :=
      le_inf (inf_le_right.trans (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr hmember))) (inf_le_left.trans hderivedLe)
    exact (Subgroup.commutator_mono hfixedLe hfirstLe).trans
      (hmixed element (hfirstLe hmem) hne member (hsecondLe hmember) hmemberNe)
  have hnormalLe : normalFactor ≤ thetaPlaneAlpha prime secondPlane := by
    change ⁅derived, secondPlane⁆ ≤ _
    rw [repeated_action_commutator_generation prime hprime secondPlane derived
      (fun first second => Subtype.ext (congrArg (fun value : actor => (value : G))
        (isMulCommutative_iff.mp hcomm ⟨first, hsecondLe first.property⟩
          ⟨second, hsecondLe second.property⟩))) hsecondPower hsecondCard hsolvable hcomplement
      (hsecondLe.trans hderivedNormalized)]
    apply iSup_le
    intro member
    apply iSup_le
    intro hmemberNe
    let fixed := derived ⊓ Subgroup.centralizer {(member : G)}
    let commutator := ⁅fixed, secondPlane⁆
    have hmemberActorNe : (member : G) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
    have hfixedNormalized : secondPlane ≤ Subgroup.normalizer (fixed : Set G) :=
      normalizes_inf_of_normalizes_both secondPlane derived _
        (hsecondLe.trans hderivedNormalized)
        ((hsecondLe.trans (commutative_plane_le_element_centralizer actor hcomm member
          (hsecondLe member.property))).trans Subgroup.le_normalizer)
    have hfixedLe : fixed ≤ Subgroup.centralizer ({(member : G)} : Set G) ⊓ core :=
      le_inf inf_le_right (inf_le_left.trans hderivedLe)
    have hcommutatorLe : commutator ≤
        thetaCoreOf prime (Subgroup.centralizer ({(member : G)} : Set G)) :=
      (Subgroup.commutator_mono hfixedLe hsecondLe).trans
        (hmixed element (hfirstLe hmem) hne member (hsecondLe member.property) hmemberActorNe)
    have hfixedComplement : ¬prime ∣ Nat.card fixed :=
      fun hdiv => hcomplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hidempotent := coprime_commutator_idempotent prime hprime secondPlane fixed
      (IsPGroup.of_card hsecondCard) hfixedComplement hfixedNormalized
    change ⁅fixed, secondPlane⁆ ≤ _
    rw [← hidempotent]
    apply (Subgroup.commutator_mono hcommutatorLe le_rfl).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (member : G) (le_iSup_of_le member.property
      (le_iSup_of_le hmemberActorNe le_rfl))
  have hderivedBound : derived ≤ normalFactor ⊔ ⁅fixedFactor, firstPlane⁆ := by
    rw [← hidempotent]
    rw [hfactor]
    exact commutator_normalized_sup_le normalFactor fixedFactor firstPlane hfixedNormalizes
      hnormalNormalized
  exact hderivedBound.trans (sup_le hnormalLe (hfixedCommutatorLe.trans le_sup_right))

theorem thetaPlaneAlpha_le_other_alpha_of_local_and_mixed
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor firstPlane secondPlane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor)
    (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondPower : ∀ member : secondPlane, member ^ prime = 1)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (hlocal : ∀ element ∈ secondPlane, element ≠ 1 →
      thetaPlaneAlpha prime (firstPlane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
        solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime)
    (hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G))) :
    thetaPlaneAlpha prime firstPlane ≤ thetaPlaneAlpha prime secondPlane := by
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
      hcomm hfirstLe hsecondLe hfirstCard hsecondPower hsecondCard hmixed member hmember hmemberNe
  · exact thetaPlaneIntersection_le_other_alpha_of_local prime hprime actor firstPlane secondPlane
      hcomm hfirstLe hsecondLe hsecondPower hsecondCard element element.property hneAmbient hlocal

theorem thetaPlaneAlpha_eq_of_rank_three_local_planes
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3)
    (hlocal : ∀ element ∈ actor, element ≠ 1 → ∀ plane : Subgroup G,
      plane ≤ actor → Nat.card plane = prime ^ 2 →
        thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
          solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime)
    (firstPlane secondPlane : Subgroup G) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor) (hfirstCard : Nat.card firstPlane = prime ^ 2)
    (hsecondCard : Nat.card secondPlane = prime ^ 2) :
    thetaPlaneAlpha prime firstPlane = thetaPlaneAlpha prime secondPlane := by
  have hmixed : ∀ first ∈ actor, first ≠ 1 → ∀ second ∈ actor, second ≠ 1 →
      ⁅Subgroup.centralizer ({second} : Set G) ⊓
        thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
          thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)) := by
    intro first hfirst hfirstNe second hsecond hsecondNe
    exact theta_mixed_balance_of_rank_three_local_planes prime hprime actor hab hactorCard hlocal
      first second hfirst hsecond hfirstNe hsecondNe
  have hpower : ∀ plane : Subgroup G, plane ≤ actor → ∀ member : plane, member ^ prime = 1 := by
    intro plane hle member
    apply Subtype.ext
    exact hab.2 member (hle member.property)
  apply le_antisymm
  · exact thetaPlaneAlpha_le_other_alpha_of_local_and_mixed prime hprime actor firstPlane secondPlane
      hab.1 hfirstLe hsecondLe hfirstCard (hpower secondPlane hsecondLe) hsecondCard
      (fun element hmem hne => hlocal element (hsecondLe hmem) hne firstPlane hfirstLe hfirstCard) hmixed
  · exact thetaPlaneAlpha_le_other_alpha_of_local_and_mixed prime hprime actor secondPlane firstPlane
      hab.1 hsecondLe hfirstLe hsecondCard (hpower firstPlane hfirstLe) hfirstCard
      (fun element hmem hne => hlocal element (hfirstLe hmem) hne secondPlane hsecondLe hsecondCard) hmixed

end CFSG.RankThreeEvenClassification.Helpers
