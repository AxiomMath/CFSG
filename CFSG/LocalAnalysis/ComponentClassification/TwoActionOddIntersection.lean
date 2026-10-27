module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorInvolutions

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.TwoActionOddIntersection

theorem two_in_odd_eq_bot {G : Type*} [Group G] [Finite G]
    (twoSubgroup oddSubgroup : Subgroup G) (htwo : IsPGroup 2 twoSubgroup)
    (hodd : Odd (Nat.card oddSubgroup)) (hle : twoSubgroup ≤ oddSubgroup) :
    twoSubgroup = ⊥ := by
  apply twoSubgroup.eq_bot_iff_card.mpr
  have htwoOdd := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rcases htwo.card_eq_or_dvd with hone | hdivides
  · exact hone
  · exact (htwoOdd.not_two_dvd_nat hdivides).elim

theorem commutator_le_core {G : Type*} [Group G] [Finite G]
    (first second overgroup twoSubgroup : Subgroup G)
    (hsecondOvergroup : second ≤ overgroup) (htwo : IsPGroup 2 twoSubgroup)
    (htwoSecond : twoSubgroup ≤ second)
    (htwoNormalizes : twoSubgroup ≤ Subgroup.normalizer (first : Set G))
    (hodd : Odd (Nat.card ↥(first ⊓ second)))
    (hoddConjugate : ∀ actor ∈ first ⊓ overgroup,
      Odd (Nat.card ↥(first ⊓ (second ⊔ second.map (MulAut.conj actor).toMonoidHom))))
    (hcommutesConjugate : ∀ actor ∈ first ⊓ overgroup,
      actor ∉ Subgroup.normalizer (second : Set G) →
        ⁅second, second.map (MulAut.conj actor).toMonoidHom⁆ = ⊥) :
    ⁅twoSubgroup, first ⊓ overgroup⁆ ≤
      (componentClassificationOddCore ↥(first ⊓ overgroup)).map (first ⊓ overgroup).subtype := by
  classical
  let intersection := first ⊓ overgroup
  let overlap := first ⊓ second
  by_cases hnormalizes : intersection ≤ Subgroup.normalizer (second : Set G)
  · have hmutualIntersection : overlap ≤ intersection := inf_le_inf_left first hsecondOvergroup
    let localMutual := overlap.subgroupOf intersection
    have hlocalNormal : localMutual.Normal := by
      apply (Subgroup.normal_subgroupOf_iff hmutualIntersection).mpr
      intro member actor hmember hactor
      exact ⟨first.mul_mem (first.mul_mem hactor.1 hmember.1) (first.inv_mem hactor.1),
        (Subgroup.mem_normalizer_iff.mp (hnormalizes hactor) member).mp hmember.2⟩
    let : localMutual.Normal := hlocalNormal
    have hlocalOdd : Odd (Nat.card localMutual) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmutualIntersection).toEquiv]
      exact hodd
    have hcore := OddCore.maximal intersection localMutual hlocalNormal hlocalOdd
    have hambientCore := Subgroup.map_mono (f := intersection.subtype) hcore
    rw [Subgroup.map_subgroupOf_eq_of_le hmutualIntersection] at hambientCore
    apply le_trans _ hambientCore
    apply Subgroup.commutator_le.mpr
    intro member hmember actor hactor
    have hfirstConjugate : member * actor * member⁻¹ ∈ first :=
      (Subgroup.mem_normalizer_iff.mp (htwoNormalizes hmember) actor).mp hactor.1
    have hsecondConjugate : actor * member⁻¹ * actor⁻¹ ∈ second :=
      (Subgroup.mem_normalizer_iff.mp (hnormalizes hactor) member⁻¹).mp
        (second.inv_mem (htwoSecond hmember))
    refine ⟨first.mul_mem hfirstConjugate (first.inv_mem hactor.1), ?_⟩
    change member * actor * member⁻¹ * actor⁻¹ ∈ second
    simpa only [mul_assoc] using second.mul_mem (htwoSecond hmember) hsecondConjugate
  · let proper := (Subgroup.normalizer (second : Set G)).subgroupOf intersection
    have hproper : proper ≠ ⊤ := by
      intro heq
      apply hnormalizes
      intro actor hactor
      have hmem : (⟨actor, hactor⟩ : intersection) ∈ proper := by rw [heq]; exact Subgroup.mem_top _
      exact hmem
    have houtsideCentralizes : ∀ actor : intersection, actor ∉ proper →
        actor ∈ (Subgroup.centralizer (twoSubgroup : Set G)).subgroupOf intersection := by
      intro actor houtside
      apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have hcommutes := hcommutesConjugate actor.val actor.property houtside
      let cyclic := Subgroup.zpowers member
      let conjugateCyclic := cyclic.map (MulAut.conj actor.val).toMonoidHom
      have hcyclicTwo : IsPGroup 2 cyclic := htwo.to_le (Subgroup.zpowers_le.mpr hmember)
      have hconjugateTwo : IsPGroup 2 conjugateCyclic := hcyclicTwo.map (MulAut.conj actor.val).toMonoidHom
      have hcyclicSecond : cyclic ≤ second := (Subgroup.zpowers_le.mpr (htwoSecond hmember))
      have hconjugateSecond : conjugateCyclic ≤ second.map (MulAut.conj actor.val).toMonoidHom :=
        Subgroup.map_mono hcyclicSecond
      have hcyclicCommutes : ⁅cyclic, conjugateCyclic⁆ = ⊥ := by
        apply le_bot_iff.mp
        have hle := Subgroup.commutator_mono hcyclicSecond hconjugateSecond
        rwa [hcommutes] at hle
      have hproductTwo : IsPGroup 2 ↥(cyclic ⊔ conjugateCyclic) :=
        hcyclicTwo.to_sup_of_normal_left' hconjugateTwo
          ((Subgroup.le_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcyclicCommutes)).trans
              (Subgroup.centralizer_le_normalizer _))
      let displacement := ⁅member, actor.val⁆
      have hdisplacementProduct : displacement ∈ cyclic ⊔ conjugateCyclic := by
        have hconjugate : actor.val * member⁻¹ * actor.val⁻¹ ∈ conjugateCyclic :=
          Subgroup.mem_map_of_mem (MulAut.conj actor.val).toMonoidHom (cyclic.inv_mem (Subgroup.mem_zpowers member))
        change member * actor.val * member⁻¹ * actor.val⁻¹ ∈ cyclic ⊔ conjugateCyclic
        simpa only [mul_assoc] using Subgroup.mul_mem_sup (Subgroup.mem_zpowers member) hconjugate
      have hdisplacementFirst : displacement ∈ first := by
        have hconjugate := (Subgroup.mem_normalizer_iff.mp (htwoNormalizes hmember) actor.val).mp actor.property.1
        exact first.mul_mem hconjugate (first.inv_mem actor.property.1)
      let displacementSubgroup := Subgroup.zpowers displacement
      have hdisplacementTwo : IsPGroup 2 displacementSubgroup :=
        hproductTwo.to_le (Subgroup.zpowers_le.mpr hdisplacementProduct)
      have hdisplacementLe : displacementSubgroup ≤ first ⊓
          (second ⊔ second.map (MulAut.conj actor.val).toMonoidHom) := by
        apply Subgroup.zpowers_le.mpr
        exact ⟨hdisplacementFirst, (sup_le (hcyclicSecond.trans le_sup_left)
          (hconjugateSecond.trans le_sup_right)) hdisplacementProduct⟩
      have hbot := two_in_odd_eq_bot displacementSubgroup _ hdisplacementTwo
        (hoddConjugate actor.val actor.property) hdisplacementLe
      have hone : displacement = 1 := Subgroup.zpowers_eq_bot.mp hbot
      exact commutatorElement_eq_one_iff_mul_comm.mp hone
    have hcentralizerTop := BlockFactorInvolutions.complement_le proper
      ((Subgroup.centralizer (twoSubgroup : Set G)).subgroupOf intersection) hproper houtsideCentralizes
    have hcentralizes : intersection ≤ Subgroup.centralizer (twoSubgroup : Set G) := by
      intro actor hactor
      have hmem : (⟨actor, hactor⟩ : intersection) ∈
          (Subgroup.centralizer (twoSubgroup : Set G)).subgroupOf intersection := by
        rw [hcentralizerTop]
        exact Subgroup.mem_top _
      exact hmem
    have hbot : ⁅twoSubgroup, intersection⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hcentralizes)
    rw [hbot]
    exact bot_le

end CFSG.ComponentClassification.TwoActionOddIntersection
