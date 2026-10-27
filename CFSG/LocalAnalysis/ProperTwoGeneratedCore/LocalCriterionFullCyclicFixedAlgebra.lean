module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeneratedPairGrowthPair
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def cyclicSylowImage (X : Subgroup G) {p : ℕ} (A : Sylow p X) : Subgroup G :=
  (A : Subgroup X).map X.subtype

theorem cyclic_sylow_unique [Finite G] (X : Subgroup G) [IsCyclic X]
    {p : ℕ} (hp : p.Prime) (A A' : Sylow p X) : A = A' := by
  let : Fact p.Prime := ⟨hp⟩
  let : Unique (Sylow p X) := Sylow.unique_of_normal A (Subgroup.normal_of_isMulCommutative _)
  exact Subsingleton.elim A A'

theorem cyclic_sylow_characteristic [Finite G] (X : Subgroup G) [IsCyclic X]
    {p : ℕ} (hp : p.Prime) (A : Sylow p X) : (A : Subgroup X).Characteristic := by
  let : Fact p.Prime := ⟨hp⟩
  exact Sylow.characteristic_of_normal A (Subgroup.normal_of_isMulCommutative _)

theorem cyclic_sylow_image_card [Finite G] (X : Subgroup G)
    {p : ℕ} (hp : p.Prime) (A : Sylow p X) :
    Nat.card (cyclicSylowImage X A) = p ^ (Nat.card X).factorization p := by
  let : Fact p.Prime := ⟨hp⟩
  rw [cyclicSylowImage, Subgroup.card_subtype]
  exact A.card_eq_multiplicity

theorem cyclic_sylow_image_normal [Finite G] (B X : Subgroup G) [IsCyclic X]
    (hXB : X ≤ B) (hXnormal : (X.subgroupOf B).Normal)
    {p : ℕ} (hp : p.Prime) (A : Sylow p X) :
    ((cyclicSylowImage X A).subgroupOf B).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hXB).mp hXnormal).trans
    (generatedPairGrowth_normalizer_le_characteristic_image X (A : Subgroup X)
      (cyclic_sylow_characteristic X hp A))

theorem inversion_mem_normalizer (A : Subgroup G) (t : G)
    (hinverts : ∀ x ∈ A, rightConjugateElem x t = x⁻¹) :
    t ∈ Subgroup.normalizer (A : Set G) := by
  apply Subgroup.mem_normalizer_iff''.mpr
  intro x
  constructor
  · intro hx
    rw [show t⁻¹ * x * t = x⁻¹ from hinverts x hx]
    exact A.inv_mem hx
  · intro hx
    have hh := hinverts (t⁻¹ * x * t) hx
    have heq : t⁻¹ * (t⁻¹ * x * t) * t = t⁻¹ * x⁻¹ * t := by
      simpa only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc] using hh
    have hxinv : t⁻¹ * x * t = x⁻¹ := by
      have hc := congrArg (fun y => t * y * t⁻¹) heq
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, inv_mul_cancel,
        inv_mul_cancel_left, mul_one] using hc
    have hxA : x⁻¹ ∈ A := by rwa [hxinv] at hx
    simpa only [inv_inv] using A.inv_mem hxA

theorem odd_inversion_centralizer_eq_bot [Finite G] (A : Subgroup G) (t : G)
    (hodd : Odd (Nat.card A))
    (hinverts : ∀ x ∈ A, rightConjugateElem x t = x⁻¹) :
    A ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hcomm : Commute x t := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hconj : rightConjugateElem x t = x := by
    change t⁻¹ * x * t = x
    calc
      t⁻¹ * x * t = t⁻¹ * (x * t) := mul_assoc _ _ _
      _ = t⁻¹ * (t * x) := congrArg (fun a => t⁻¹ * a) hcomm.eq
      _ = x := inv_mul_cancel_left t x
  have heq : x = x⁻¹ := hconj.symm.trans (hinverts x hx.1)
  have htwo : x ^ 2 = 1 := by
    rw [pow_two]
    calc
      x * x = x * x⁻¹ := congrArg (fun y => x * y) heq
      _ = 1 := mul_inv_cancel x
  have horder : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right
    (A.orderOf_dvd_natCard hx.1) (orderOf_dvd_of_pow_eq_one htwo)
  exact orderOf_eq_one_iff.mp horder

theorem odd_inversion_conjugacy_card [Finite G] (A : Subgroup G) (t : G)
    (hodd : Odd (Nat.card A))
    (hinverts : ∀ x ∈ A, rightConjugateElem x t = x⁻¹) :
    Nat.card (conjugacyWithin A t) = Nat.card A := by
  have hbot := odd_inversion_centralizer_eq_bot A t hodd hinverts
  have hC : (Subgroup.centralizer ({t} : Set G)).subgroupOf A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hbot ▸ (show (x : G) ∈ A ⊓
      Subgroup.centralizer ({t} : Set G) from ⟨x.property, hx⟩))
  rw [conjugacyWithin_card_eq_centralizer_index, hC, Subgroup.index_bot]

theorem cyclic_coset_inverts (X : Subgroup G) [IsCyclic X] (t : G)
    (hinverts : ∀ x ∈ X, rightConjugateElem x t = x⁻¹)
    {r : G} (hr : r ∈ ({t} : Set G) * (X : Set G)) :
    ∀ y ∈ X, rightConjugateElem y r = y⁻¹ := by
  rw [Set.singleton_mul] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  intro y hy
  rw [← rightConjugateElem_comp, hinverts y hy]
  have hcomm : Commute y⁻¹ x := by
    exact congrArg Subtype.val (show (⟨y⁻¹, X.inv_mem hy⟩ : X) * ⟨x, hx⟩ =
      (⟨x, hx⟩ : X) * ⟨y⁻¹, X.inv_mem hy⟩ from mul_comm' _ _)
  change x⁻¹ * y⁻¹ * x = y⁻¹
  calc
    x⁻¹ * y⁻¹ * x = x⁻¹ * (y⁻¹ * x) := mul_assoc _ _ _
    _ = x⁻¹ * (x * y⁻¹) := congrArg (fun a => x⁻¹ * a) hcomm.eq
    _ = y⁻¹ := inv_mul_cancel_left x y⁻¹

end CFSG.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed
