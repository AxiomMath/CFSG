module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Model
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.HSFLit.L2Act

open Equiv DihedralGroup

@[expose] def typeP (g : Perm (ZMod 8)) : Multiplicative (ZMod 2 × ZMod 2) :=
  Multiplicative.ofAdd (dbit8 (g 0), fbit8 (linF g))

theorem type8_eq_typeP (g : H8) : type8 g = typeP g := rfl

theorem typeP_aff8 (u : (ZMod 8)ˣ) (b : ZMod 8) :
    typeP (aff8 u b) = Multiplicative.ofAdd (dbit8 b, fbit8 u) :=
  type8_aff8 u b

theorem fbit8_mul : ∀ u u' : (ZMod 8)ˣ,
    fbit8 ((u * u' : (ZMod 8)ˣ) : ZMod 8) = fbit8 u + fbit8 u' := by decide

@[expose] def fbitU8 : (ZMod 8)ˣ →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (fbit8 u)
  map_one' := by decide
  map_mul' u u' := by rw [fbit8_mul, ofAdd_add]

theorem fbit8_neg_mul : ∀ u : (ZMod 8)ˣ, fbit8 ((-u : (ZMod 8)ˣ) : ZMod 8) = fbit8 u := by
  decide

theorem aff8_pair_injective :
    Function.Injective fun p : (ZMod 8)ˣ × ZMod 8 => aff8 p.1 p.2 := by
  rintro ⟨u, b⟩ ⟨u', b'⟩ h
  obtain ⟨h1, h2⟩ := aff8_injective h
  exact Prod.ext h1 h2

private abbrev r8Par : Finset ((ZMod 8)ˣ × ZMod 8) :=
  Finset.univ.filter fun p => (p.1 = 1 ∨ p.1 = -1) ∧ ∃ c : ZMod 8, p.2 = 2 * c

private theorem card_r8Par : r8Par.card = 8 := by decide

theorem card_R8 : Nat.card R8 = 8 := by
  classical
  have hset : (R8 : Set (Perm (ZMod 8))) =
      (fun p : (ZMod 8)ˣ × ZMod 8 => aff8 p.1 p.2) '' (r8Par : Set _) := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨u, c, hu, rfl⟩
      exact ⟨u, 2 * c, ⟨hu, c, rfl⟩, rfl⟩
    · rintro ⟨u, b, ⟨hu, c, rfl⟩, rfl⟩
      exact ⟨u, c, hu, rfl⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset,
    Set.ncard_image_of_injective _ aff8_pair_injective, Set.ncard_coe_finset, card_r8Par]

@[expose] def dih8Fun : DihedralGroup 8 → Perm (ZMod 8)
  | r i => aff8 1 i
  | sr i => aff8 (-1) (-i)

theorem dih8Fun_mul (g h : DihedralGroup 8) :
    dih8Fun (g * h) = dih8Fun g * dih8Fun h := by
  cases g <;> cases h <;>
    simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, dih8Fun, aff8_mul, mul_one, one_mul,
      mul_neg, neg_mul, neg_neg, Units.val_one, Units.val_neg] <;> congr 1 <;> ring

@[expose] def dih8 : DihedralGroup 8 →* Perm (ZMod 8) where
  toFun := dih8Fun
  map_one' := by
    rw [DihedralGroup.one_def]
    exact aff8_one
  map_mul' := dih8Fun_mul

@[simp] theorem dih8_r (i : ZMod 8) : dih8 (r i) = aff8 1 i := rfl

@[simp] theorem dih8_sr (i : ZMod 8) : dih8 (sr i) = aff8 (-1) (-i) := rfl

private theorem one_ne_neg_one_units : (1 : (ZMod 8)ˣ) ≠ -1 := by decide

theorem dih8_injective : Function.Injective dih8 := by
  intro g h hgh
  cases g <;> cases h <;> simp only [dih8_r, dih8_sr] at hgh
  · rw [(aff8_injective hgh).2]
  · exact absurd (aff8_injective hgh).1 one_ne_neg_one_units
  · exact absurd (aff8_injective hgh).1.symm one_ne_neg_one_units
  · rw [neg_inj.mp (aff8_injective hgh).2]

theorem dih8_mem_D16 (g : DihedralGroup 8) : dih8 g ∈ D16 := by
  cases g
  · exact ⟨1, _, Or.inl rfl, rfl⟩
  · exact ⟨-1, _, Or.inr rfl, rfl⟩

@[expose] def shiftFun : DihedralGroup 8 → DihedralGroup 8
  | r i => r i
  | sr i => sr (i + 1)

@[expose] def dshift : DihedralGroup 8 →* DihedralGroup 8 where
  toFun := shiftFun
  map_one' := rfl
  map_mul' g h := by
    cases g <;> cases h <;> simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, shiftFun] <;>
      congr 1 <;> ring

theorem dshift_injective : Function.Injective dshift := by
  intro g h hgh
  cases g <;> cases h <;> simp only [dshift, MonoidHom.coe_mk] at hgh
  · exact hgh
  · cases hgh
  · cases hgh
  · exact congrArg sr (add_right_cancel (sr.inj hgh))

private theorem dbit8_neg : ∀ i : ZMod 8, dbit8 (-i) = dbit8 i := by decide

private theorem dbit8_neg_add_one : ∀ i : ZMod 8, dbit8 (-(i + 1)) = dbit8 i + 1 := by decide

private theorem fbit8_one : fbit8 ((1 : (ZMod 8)ˣ) : ZMod 8) = 0 := by decide

private theorem fbit8_neg_one : fbit8 ((-1 : (ZMod 8)ˣ) : ZMod 8) = 0 := by decide

private theorem exists_two_mul_of_dbit8 : ∀ b : ZMod 8, dbit8 b = 0 → ∃ c, b = 2 * c := by
  decide

private theorem dbit8_eq_val (i : ZMod 8) : dbit8 i = (i.val : ZMod 2) := rfl

private theorem toAdd_chi_r {χ : DihedralGroup 8 →* Multiplicative (ZMod 2)} (hχ : χ (r 1) ≠ 1)
    (i : ZMod 8) : Multiplicative.toAdd (χ (r i)) = dbit8 i := by
  have h1 : Multiplicative.toAdd (χ (r 1)) = 1 := by
    have : Multiplicative.toAdd (χ (r 1)) ≠ 0 := fun h0 => hχ (by
      rw [← ofAdd_toAdd (χ (r 1)), h0, ofAdd_zero])
    revert this
    generalize Multiplicative.toAdd (χ (r 1)) = a
    revert a
    decide
  have hi : r i = (r 1 : DihedralGroup 8) ^ i.val := by
    rw [r_one_pow, ZMod.natCast_zmod_val]
  rw [hi, map_pow, toAdd_pow, h1, nsmul_eq_mul, mul_one, dbit8_eq_val]

theorem exists_dih8_embedding (χ : DihedralGroup 8 →* Multiplicative (ZMod 2))
    (hχ : χ (r 1) ≠ 1) :
    ∃ j : DihedralGroup 8 →* Perm (ZMod 8), Function.Injective j ∧ (∀ g, j g ∈ D16) ∧
      (∀ g, typeP (j g) = Multiplicative.ofAdd (Multiplicative.toAdd (χ g), 0)) ∧
      (∀ g, χ g = 1 → j g ∈ R8) := by
  have hsr : ∀ i : ZMod 8, sr i = sr 0 * r i := fun i => by rw [sr_mul_r, zero_add]
  have hR8 : ∀ (j : DihedralGroup 8 →* Perm (ZMod 8)), (∀ g, j g ∈ D16) →
      (∀ g, typeP (j g) = Multiplicative.ofAdd (Multiplicative.toAdd (χ g), 0)) →
      ∀ g, χ g = 1 → j g ∈ R8 := by
    intro j hjD hjt g hg
    obtain ⟨u, b, hu, hub⟩ := hjD g
    have h1 := hjt g
    rw [← hub, typeP_aff8, hg, toAdd_one] at h1
    have hb : dbit8 b = 0 := congrArg Prod.fst (congrArg Multiplicative.toAdd h1)
    obtain ⟨c, rfl⟩ := exists_two_mul_of_dbit8 b hb
    exact ⟨u, c, hu, hub⟩
  by_cases hs : χ (sr 0) = 1
  · have ht : ∀ g, typeP (dih8 g) = Multiplicative.ofAdd (Multiplicative.toAdd (χ g), 0) := by
      intro g
      cases g with
      | r i => rw [dih8_r, typeP_aff8, fbit8_one, toAdd_chi_r hχ]
      | sr i => rw [dih8_sr, typeP_aff8, fbit8_neg_one, dbit8_neg, hsr i, map_mul, hs,
          one_mul, toAdd_chi_r hχ]
    exact ⟨dih8, dih8_injective, dih8_mem_D16, ht, hR8 dih8 dih8_mem_D16 ht⟩
  · have hs1 : Multiplicative.toAdd (χ (sr 0)) = 1 := by
      have : Multiplicative.toAdd (χ (sr 0)) ≠ 0 := fun h0 => hs (by
        rw [← ofAdd_toAdd (χ (sr 0)), h0, ofAdd_zero])
      revert this
      generalize Multiplicative.toAdd (χ (sr 0)) = a
      revert a
      decide
    set j := dih8.comp dshift with hj
    have hjD : ∀ g, j g ∈ D16 := fun g => dih8_mem_D16 _
    have ht : ∀ g, typeP (j g) = Multiplicative.ofAdd (Multiplicative.toAdd (χ g), 0) := by
      intro g
      cases g with
      | r i =>
        change typeP (dih8 (r i)) = _
        rw [dih8_r, typeP_aff8, fbit8_one, toAdd_chi_r hχ]
      | sr i =>
        change typeP (dih8 (sr (i + 1))) = _
        rw [dih8_sr, typeP_aff8, fbit8_neg_one, dbit8_neg_add_one, hsr i, map_mul, toAdd_mul,
          hs1, toAdd_chi_r hχ, add_comm]
    exact ⟨j, dih8_injective.comp dshift_injective, hjD, ht, hR8 j hjD ht⟩

end CFSG.ComponentClassification.HSFLit.L2Act
