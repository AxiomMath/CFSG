module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

def conjugatorFiberEquiv (J : Subgroup G) (t : G) (b : J) :
    (J ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ≃
      {i : J // (i : G)⁻¹ * t * i = (b : G)⁻¹ * t * b} where
  toFun c := ⟨⟨(c : G) * b, J.mul_mem c.property.1 b.property⟩, by
    have hct : Commute (c : G) t :=
      Subgroup.mem_centralizer_singleton_iff.mp c.property.2
    change ((c : G) * b)⁻¹ * t * ((c : G) * b) = (b : G)⁻¹ * t * b
    calc
      _ = (b : G)⁻¹ * ((c : G)⁻¹ * t * c) * b := by group
      _ = _ := by rw [hct.inv_mul_cancel]⟩
  invFun i := ⟨(i.val : G) * (b : G)⁻¹,
    J.mul_mem i.val.property (J.inv_mem b.property),
    (right_conjugates_eq_iff.mp i.property)⟩
  left_inv c := by
    apply Subtype.ext
    change (c : G) * (b : G) * (b : G)⁻¹ = c
    group
  right_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    change (i.val : G) * (b : G)⁻¹ * (b : G) = i.val
    group

@[expose, instance_reducible] def fixedConjugatorFiberAction
    (J A : Subgroup G) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (t s : G) (ht : t ∈ Subgroup.centralizer (A : Set G))
    (hs : s ∈ Subgroup.centralizer (A : Set G)) :
    MulAction A {i : J // (i : G)⁻¹ * t * i = s} where
  smul a i := ⟨⟨(a : G) * i.val * (a : G)⁻¹,
    (hAJ a.property i.val).mp i.val.property⟩, by
    have hat : Commute (a : G) t := Subgroup.mem_centralizer_iff.mp ht a a.property
    have has : Commute (a : G) s := Subgroup.mem_centralizer_iff.mp hs a a.property
    change ((a : G) * i.val * (a : G)⁻¹)⁻¹ * t *
      ((a : G) * i.val * (a : G)⁻¹) = s
    calc
      _ = (a : G) * ((i.val : G)⁻¹ * ((a : G)⁻¹ * t * a) * i.val) * (a : G)⁻¹ := by
        group
      _ = (a : G) * ((i.val : G)⁻¹ * t * i.val) * (a : G)⁻¹ := by
        rw [hat.inv_mul_cancel]
      _ = (a : G) * s * (a : G)⁻¹ := by rw [i.property]
      _ = s := has.mul_inv_cancel⟩
  one_smul i := by
    apply Subtype.ext
    apply Subtype.ext
    change (1 : G) * i.val * (1 : G)⁻¹ = i.val
    simp only [inv_one, one_mul, mul_one]
  mul_smul a b i := by
    apply Subtype.ext
    apply Subtype.ext
    change ((a : G) * b) * i.val * ((a : G) * b)⁻¹ =
      (a : G) * ((b : G) * i.val * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem odd_fixed_conjugate_has_fixed_conjugator [Finite G]
    (J A : Subgroup G) (hJ : Odd (Nat.card J)) (hA : IsPGroup 2 A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (t : G) (ht : t ∈ Subgroup.centralizer (A : Set G))
    {s : G} (hsJ : s ∈ conjugacyWithin J t)
    (hsA : s ∈ Subgroup.centralizer (A : Set G)) :
    ∃ i : (J ⊓ Subgroup.centralizer (A : Set G) : Subgroup G), (i : G)⁻¹ * t * i = s := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb⟩ := hsJ
  let : MulAction A {i : J // (i : G)⁻¹ * t * i = s} :=
    fixedConjugatorFiberAction J A hAJ t s ht hsA
  have hcard : Nat.card {i : J // (i : G)⁻¹ * t * i = s} =
      Nat.card (J ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    rw [← hb]
    exact (Nat.card_congr (conjugatorFiberEquiv J t b)).symm
  have hodd : Odd (Nat.card {i : J // (i : G)⁻¹ * t * i = s}) := by
    rw [hcard]
    exact hJ.of_dvd_nat
      (Subgroup.card_dvd_of_le (show J ⊓ Subgroup.centralizer ({t} : Set G) ≤ J from inf_le_left))
  obtain ⟨i, hi⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card
    {i : J // (i : G)⁻¹ * t * i = s} hodd.not_two_dvd_nat
  refine ⟨⟨i.val, i.val.property, Subgroup.mem_centralizer_iff.mpr ?_⟩, i.property⟩
  intro a ha
  have hf := congrArg (fun j : {i : J // (i : G)⁻¹ * t * i = s} => (j.val : G))
    (MulAction.mem_fixedPoints.mp hi (⟨a, ha⟩ : A))
  change a * (i.val : G) * a⁻¹ = i.val at hf
  exact mul_inv_eq_iff_eq_mul.mp hf

theorem odd_conjugacyWithin_fixed_eq [Finite G]
    (J A : Subgroup G) (hJ : Odd (Nat.card J)) (hA : IsPGroup 2 A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (t : G) (ht : t ∈ Subgroup.centralizer (A : Set G)) :
    conjugacyWithin J t ∩ (Subgroup.centralizer (A : Set G) : Set G) =
      conjugacyWithin (J ⊓ Subgroup.centralizer (A : Set G)) t := by
  ext s
  constructor
  · rintro ⟨hsJ, hsA⟩
    exact odd_fixed_conjugate_has_fixed_conjugator J A hJ hA hAJ t ht hsJ hsA
  · rintro ⟨i, rfl⟩
    refine ⟨⟨⟨i, i.property.1⟩, rfl⟩, ?_⟩
    exact (Subgroup.centralizer (A : Set G)).mul_mem
      ((Subgroup.centralizer (A : Set G)).mul_mem
        ((Subgroup.centralizer (A : Set G)).inv_mem i.property.2) ht) i.property.2

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
