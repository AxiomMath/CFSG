module

public import CFSG.GroupTheory.ThreeTranspositions.QuotientReduce
import CFSG.GroupTheory.ThreeTranspositions.SingleClass
import CFSG.GroupTheory.ThreeTranspositions.DerivedSimple
import CFSG.GroupTheory.ThreeTranspositions.ClassifyEnd
import CFSG.GroupTheory.ThreeTranspositions.IndexEnd

public section

namespace CFSG.GroupTheory.ThreeTranspositions

private theorem mem_normalClosure_of_isConj {Q : Type} [Group Q] {t a : Q} (ha : IsConj t a) :
    a ∈ Subgroup.normalClosure ({t} : Set Q) :=
  Subgroup.conjugatesOfSet_subset_normalClosure
    (Group.mem_conjugatesOfSet_iff.mpr ⟨t, rfl, ha⟩)

theorem noThreeTranspositionClass : NoThreeTranspositionClass := by
  intro Q _ _ Y t hO hX hY hS ht2 ht1
  by_contra hcon
  have h : ∀ a : Q, (t * (a * t * a⁻¹)) ^ 2 = 1 ∨ (t * (a * t * a⁻¹)) ^ 3 = 1 := by
    intro a
    by_contra hh
    exact hcon ⟨a, fun h2 => hh (Or.inl h2), fun h3 => hh (Or.inr h3)⟩
  have hnc : ∃ a b : Q, IsConj t a ∧ IsConj t b ∧ a * b ≠ b * a :=
    exists_noncommuting_conj_of_pPrimeCore_eq_bot hO ht2 ht1
  have hP := pair_normalClosure_of_sq_or_cube hX ht2 ht1 h hnc
  set A : Subgroup Q := Subgroup.normalClosure ({t} : Set Q) with hA
  haveI : A.Normal := Subgroup.normalClosure_normal
  have hXA : ¬ HasE9 ↥A := fun h9 => hX (HasE9.map_injective A.subtype A.subtype_injective h9)
  have hOA : CFSG.pPrimeCore 3 ↥A = ⊥ := pPrimeCore_eq_bot_of_normal Nat.prime_three hO A
  have hpC : CFSG.pCore 3 Q = ⊥ := pCore_eq_bot_of_isStronglyPEmbedded Nat.prime_three hY
  have hZ : Subgroup.center ↥A = ⊥ := center_eq_bot_of_normal Nat.prime_three hO hpC A
  have hncA : ∃ d ∈ {x : ↥A | IsConj t (x : Q)}, ∃ e ∈ {x : ↥A | IsConj t (x : Q)},
      d * e ≠ e * d := by
    obtain ⟨a, b, ha, hb, hab⟩ := hnc
    refine ⟨⟨a, mem_normalClosure_of_isConj ha⟩, ha, ⟨b, mem_normalClosure_of_isConj hb⟩, hb, ?_⟩
    intro hcomm
    exact hab (congrArg Subtype.val hcomm)
  have hS' : IsSimpleGroup ↥(commutator ↥A) :=
    isSimpleGroup_commutator_of_pair hP hXA hOA hncA
  have hcard : Nat.card ↥A = 6 ∨ Nat.card ↥A = 120 :=
    card_eq_six_or_one_twenty_of_pair hP hXA hZ hS'
  exact false_of_normal_card_six_or_one_twenty hY hS A hcard

end CFSG.GroupTheory.ThreeTranspositions
