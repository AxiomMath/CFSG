module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantHall

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

noncomputable def invariantHallIntersection {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted] (primes : Set ℕ) : Subgroup acted :=
  ⨅ hall : {subgroup : Subgroup acted // HallFor primes subgroup ∧
    ∀ member : actor, subgroup.map (MulDistribMulAction.toMonoidHom acted member) = subgroup}, hall.val

theorem invariantHallIntersection_le {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (primes : Set ℕ) (hall : Subgroup acted) (hhall : HallFor primes hall)
    (hinvariant : ∀ member : actor, hall.map (MulDistribMulAction.toMonoidHom acted member) = hall) :
    invariantHallIntersection (actor := actor) primes ≤ hall := by
  unfold invariantHallIntersection
  exact iInf_le _ (⟨hall, hhall, hinvariant⟩ : {subgroup : Subgroup acted // HallFor primes subgroup ∧
    ∀ member : actor, subgroup.map (MulDistribMulAction.toMonoidHom acted member) = subgroup})

theorem invariant_hall_conjugate_by_fixed {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (primes : Set ℕ) (hall : Subgroup acted) (hhall : HallFor primes hall)
    (hinvariant : ∀ member : actor, hall.map (MulDistribMulAction.toMonoidHom acted member) = hall)
    (conjugator : acted) (hfixed : ∀ member : actor, member • conjugator = conjugator) :
    HallFor primes (hall.map (MulAut.conj conjugator).toMonoidHom) ∧
      ∀ member : actor, (hall.map (MulAut.conj conjugator).toMonoidHom).map
        (MulDistribMulAction.toMonoidHom acted member) = hall.map (MulAut.conj conjugator).toMonoidHom := by
  refine ⟨HallFor.map primes hall (MulAut.conj conjugator).toMonoidHom
    (MulAut.conj conjugator).surjective hhall, ?_⟩
  intro member
  rw [action_subgroup_conjugate_map, hinvariant, hfixed]

theorem invariantHallIntersection_invariant {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (primes : Set ℕ) (member : actor) :
    (invariantHallIntersection (actor := actor) primes).map
      (MulDistribMulAction.toMonoidHom acted member) =
        invariantHallIntersection (actor := actor) (acted := acted) primes := by
  have hle : ∀ member : actor, (invariantHallIntersection (actor := actor) primes).map
      (MulDistribMulAction.toMonoidHom acted member) ≤
        invariantHallIntersection (actor := actor) (acted := acted) primes := by
    intro member
    apply le_iInf
    intro hall
    have hmap := Subgroup.map_mono (f := MulDistribMulAction.toMonoidHom acted member)
      (invariantHallIntersection_le primes hall.val hall.property.1 hall.property.2)
    rw [hall.property.2 member] at hmap
    exact hmap
  apply le_antisymm (hle member)
  have hmap := Subgroup.map_mono (f := MulDistribMulAction.toMonoidHom acted member) (hle member⁻¹)
  have hcompose : (MulDistribMulAction.toMonoidHom acted member).comp
      (MulDistribMulAction.toMonoidHom acted member⁻¹) = MonoidHom.id acted := by
    ext element
    exact smul_inv_smul member element
  rw [Subgroup.map_map, hcompose, Subgroup.map_id] at hmap
  exact hmap

theorem invariantHallIntersection_fixed_normalizes {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [MulDistribMulAction actor acted]
    (primes : Set ℕ) (conjugator : acted) (hfixed : ∀ member : actor, member • conjugator = conjugator) :
    conjugator ∈ Subgroup.normalizer
      ((invariantHallIntersection (actor := actor) primes : Subgroup acted) : Set acted) := by
  have hle : ∀ conjugator : acted, (∀ member : actor, member • conjugator = conjugator) →
      (invariantHallIntersection (actor := actor) primes).map (MulAut.conj conjugator).toMonoidHom ≤
        invariantHallIntersection (actor := actor) (acted := acted) primes := by
    intro conjugator hfixed
    apply le_iInf
    intro hall
    have hfixedInv : ∀ member : actor, member • conjugator⁻¹ = conjugator⁻¹ := by
      intro member
      rw [smul_inv', hfixed]
    have hconjugate := invariant_hall_conjugate_by_fixed primes hall.val hall.property.1
      hall.property.2 conjugator⁻¹ hfixedInv
    have hmap := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom)
      (invariantHallIntersection_le primes _ hconjugate.1 hconjugate.2)
    rw [← subgroup_map_conj_mul, mul_inv_cancel, subgroup_map_conj_one] at hmap
    exact hmap
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm (hle conjugator hfixed)
  have hfixedInv : ∀ member : actor, member • conjugator⁻¹ = conjugator⁻¹ := by
    intro member
    rw [smul_inv', hfixed]
  have hmap := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom)
    (hle conjugator⁻¹ hfixedInv)
  rw [← subgroup_map_conj_mul, mul_inv_cancel, subgroup_map_conj_one] at hmap
  exact hmap

theorem invariantHallIntersection_primeSetOrder {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (primes : Set ℕ) :
    PrimeSetOrder primes (Nat.card (invariantHallIntersection (actor := actor) (acted := acted) primes)) := by
  obtain ⟨hall, hhall, hinvariant⟩ := exists_invariant_hall prime hprime hpgroup hcomplement primes
  exact PrimeSetOrder.of_dvd primes _ _ hhall.1
    (Subgroup.card_dvd_of_le (invariantHallIntersection_le primes hall hhall hinvariant))

theorem le_invariantHallIntersection_of_fixed_normalized {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] [Finite actor] [Finite acted] [Group.IsSolvable acted]
    [MulDistribMulAction actor acted]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card acted) (primes : Set ℕ)
    (subgroup : Subgroup acted) (horder : PrimeSetOrder primes (Nat.card subgroup))
    (hinvariant : ∀ member : actor, subgroup.map (MulDistribMulAction.toMonoidHom acted member) = subgroup)
    (hnormalized : ∀ conjugator : acted, (∀ member : actor, member • conjugator = conjugator) →
      conjugator ∈ Subgroup.normalizer (subgroup : Set acted)) :
    subgroup ≤ invariantHallIntersection (actor := actor) primes := by
  obtain ⟨hall, hhall, hsubgroupLe, hhallInvariant⟩ := exists_invariant_hall_containing
    prime hprime hpgroup hcomplement primes subgroup horder hinvariant
  apply le_iInf
  intro other
  obtain ⟨conjugator, hfixed, hconjugacy⟩ := exists_fixed_conjugator_of_invariant_halls
    prime hprime hpgroup hcomplement primes hall other.val hhall other.property.1
      hhallInvariant other.property.2
  have hmap := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) hsubgroupLe
  have hnorm : subgroup.map (MulAut.conj conjugator).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormalized conjugator hfixed)
  rw [hnorm, hconjugacy] at hmap
  exact hmap

end CFSG.RankThreeEvenClassification.Helpers
