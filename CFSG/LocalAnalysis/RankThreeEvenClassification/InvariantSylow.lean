module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem actionMonoidHom_surjective {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted] (member : actor) :
    Function.Surjective (MulDistribMulAction.toMonoidHom acted member) := by
  intro element
  exact ⟨member⁻¹ • element, smul_inv_smul member element⟩

@[instance_reducible]
def automorphismSylowAction {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (sylowPrime : ℕ) [Fact sylowPrime.Prime] : MulAction actor (Sylow sylowPrime acted) where
  smul member sylow := Sylow.mapSurjective
    (f := MulDistribMulAction.toMonoidHom acted member)
      (actionMonoidHom_surjective member) sylow
  one_smul sylow := by
    apply Sylow.ext
    change ((Sylow.mapSurjective
      (f := MulDistribMulAction.toMonoidHom acted (1 : actor))
        (actionMonoidHom_surjective (1 : actor)) sylow) : Subgroup acted) = sylow
    rw [Sylow.coe_mapSurjective]
    have hone : MulDistribMulAction.toMonoidHom acted (1 : actor) = MonoidHom.id acted := by
      ext element
      exact one_smul actor element
    rw [hone, Subgroup.map_id]
  mul_smul first second sylow := by
    apply Sylow.ext
    change ((Sylow.mapSurjective
      (f := MulDistribMulAction.toMonoidHom acted (first * second))
        (actionMonoidHom_surjective (first * second)) sylow) : Subgroup acted) =
      ((Sylow.mapSurjective (f := MulDistribMulAction.toMonoidHom acted first)
        (actionMonoidHom_surjective first)
          (Sylow.mapSurjective (f := MulDistribMulAction.toMonoidHom acted second)
            (actionMonoidHom_surjective second) sylow)) : Subgroup acted)
    rw [Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, Sylow.coe_mapSurjective, Subgroup.map_map]
    have hmul : MulDistribMulAction.toMonoidHom acted (first * second) =
        (MulDistribMulAction.toMonoidHom acted first).comp
          (MulDistribMulAction.toMonoidHom acted second) := by
      ext element
      exact mul_smul first second element
    rw [hmul]

theorem exists_invariant_sylow_of_pGroup_action_prime_complement
    {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite acted] [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime) :
    ∃ sylow : Sylow sylowPrime acted, ∀ member : actor,
      (sylow : Subgroup acted).map (MulDistribMulAction.toMonoidHom acted member) = sylow := by
  have : Fact prime.Prime := ⟨hprime⟩
  have : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  let : MulAction actor (Sylow sylowPrime acted) := automorphismSylowAction sylowPrime
  let sylow : Sylow sylowPrime acted := Classical.choice inferInstance
  have hcardDiv : Nat.card (Sylow sylowPrime acted) ∣ Nat.card acted :=
    (Sylow.card_dvd_index sylow).trans (Subgroup.index_dvd_card _)
  obtain ⟨fixedSylow, hfixed⟩ := hpgroup.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow sylowPrime acted) (fun hdiv => hcomplement (hdiv.trans hcardDiv))
  refine ⟨fixedSylow, ?_⟩
  intro member
  have heq := congrArg (fun value : Sylow sylowPrime acted => (value : Subgroup acted))
    (MulAction.mem_fixedPoints.mp hfixed member)
  change ((Sylow.mapSurjective (f := MulDistribMulAction.toMonoidHom acted member)
    (actionMonoidHom_surjective member) fixedSylow) :
    Subgroup acted) = fixedSylow at heq
  rw [Sylow.coe_mapSurjective] at heq
  exact heq

theorem exists_normalized_sylow_in_prime_complement_subgroup
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpgroup : IsPGroup prime actor) (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalizes : actor ≤ Subgroup.normalizer (subgroup : Set G))
    (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime) :
    ∃ sylow : Sylow sylowPrime subgroup,
      actor ≤ Subgroup.normalizer (((sylow : Subgroup subgroup).map subgroup.subtype) : Set G) := by
  let action : MulDistribMulAction actor subgroup :=
    { smul := fun member element => ⟨member * element * (member : G)⁻¹,
        Subgroup.le_normalizer_iff.mp hnormalizes member member.property element element.property⟩
      one_smul := fun element => Subtype.ext (by
        change (1 : G) * (element : G) * (1 : G)⁻¹ = element
        simp)
      mul_smul := fun first second element => Subtype.ext (by
        change ((first : G) * second) * (element : G) * ((first : G) * second)⁻¹ =
          first * ((second : G) * element * (second : G)⁻¹) * (first : G)⁻¹
        simp [mul_assoc])
      smul_one := fun member => Subtype.ext (by
        change (member : G) * 1 * (member : G)⁻¹ = 1
        simp)
      smul_mul := fun member first second => Subtype.ext (by
        change (member : G) * ((first : G) * second) * (member : G)⁻¹ =
          (member * first * (member : G)⁻¹) * (member * second * (member : G)⁻¹)
        simp [mul_assoc]) }
  let : MulDistribMulAction actor subgroup := action
  obtain ⟨sylow, hsylow⟩ := exists_invariant_sylow_of_pGroup_action_prime_complement prime hprime
    hpgroup hcomplement sylowPrime hsylowPrime (acted := subgroup)
  refine ⟨sylow, Subgroup.le_normalizer_iff.mpr ?_⟩
  intro member hmember element helement
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp helement
  have hfixed := Subgroup.mem_map_of_mem (MulDistribMulAction.toMonoidHom subgroup
    (⟨member, hmember⟩ : actor)) hpreimage
  rw [hsylow] at hfixed
  exact ⟨(⟨member, hmember⟩ : actor) • preimage, hfixed, rfl⟩

end CFSG.RankThreeEvenClassification.Helpers
