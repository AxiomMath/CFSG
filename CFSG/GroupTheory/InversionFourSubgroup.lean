module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Data.Fintype.Parity

set_option autoImplicit false

public section

open Subgroup

namespace CFSG

universe u

private theorem model_exponent :
    ∀ x : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)), x ^ 4 = 1 := by
  decide +kernel

private theorem model_square_card :
    Nat.card ↥(Subgroup.square (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) = 4 := by
  let dec : DecidablePred (fun x : (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) =>
      x ∈ Subgroup.square (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :=
    fun x => inferInstanceAs (Decidable (IsSquare x))
  let F : Fintype ↥(Subgroup.square (Multiplicative (ZMod 4) ×
      Multiplicative (ZMod 4))) :=
    @Subgroup.instFintypeSubtypeMemOfDecidablePred
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) _
      (Subgroup.square (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) dec _
  rw [@Nat.card_eq_fintype_card _ F]
  decide +kernel

private theorem exponent_four_of_c4_prod_c4 {A : Type u} [Group A]
    (e : A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    ∀ a : A, a ^ 4 = 1 := by
  intro a
  apply e.injective
  rw [map_pow, model_exponent (e a), map_one]

private theorem square_map_of_c4_prod_c4 {A : Type u} [CommGroup A]
    (e : A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    (Subgroup.square A).map e.toMonoidHom =
      Subgroup.square (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Subgroup.mem_square.mpr (IsSquare.map e (Subgroup.mem_square.mp hw))
  · intro hx
    obtain ⟨r, hr⟩ := IsSquare.exists_mul_self x (Subgroup.mem_square.mp hx)
    refine ⟨e.symm x, ?_, by simp⟩
    exact Subgroup.mem_square.mpr ⟨e.symm r, by rw [hr, map_mul]⟩

private theorem square_card_of_c4_prod_c4 {A : Type u} [CommGroup A]
    (e : A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Nat.card ↥(Subgroup.square A) = 4 := by
  have hmap := square_map_of_c4_prod_c4 e
  calc
    Nat.card ↥(Subgroup.square A)
        = Nat.card ↥((Subgroup.square A).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
    _ = Nat.card ↥(Subgroup.square (Multiplicative (ZMod 4) ×
          Multiplicative (ZMod 4))) := by rw [hmap]
    _ = 4 := model_square_card

theorem four_le_card_fixed_of_c4_prod_c4_involutive
    {A : Type u} [Group A]
    (hA : Nonempty (A ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (alpha : MulAut A) (halpha : Function.Involutive alpha) :
    4 ≤ Nat.card {a : A // alpha a = a} := by
  obtain ⟨e⟩ := hA
  let commA : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => e.injective (by simp only [map_mul, mul_comm]) }
  let finiteA : Finite A := Finite.of_injective e e.injective
  let sqA : Subgroup A := @Subgroup.square A commA
  have mem_sqA : ∀ {a : A}, a ∈ sqA ↔ IsSquare a :=
    fun {a} => @Subgroup.mem_square A commA a
  have hfour : ∀ a : A, a ^ 4 = 1 := @exponent_four_of_c4_prod_c4 A _ e
  have hsquareCard : Nat.card ↥sqA = 4 := @square_card_of_c4_prod_c4 A commA e
  let F : Subgroup A := MonoidHom.eqLocus alpha.toMonoidHom (MonoidHom.id A)
  change 4 ≤ Nat.card ↥F
  let finiteF : Finite ↥F :=
    @Finite.of_injective ↥F A finiteA F.subtype Subtype.coe_injective
  by_cases hfixsq : ∀ w : A, alpha (w ^ 2) = w ^ 2
  · have hle : sqA ≤ F := by
      intro x hx
      obtain ⟨w, hw⟩ := IsSquare.exists_mul_self x (mem_sqA.mp hx)
      change alpha x = x
      rw [hw, ← pow_two]
      exact hfixsq w
    calc
      4 = Nat.card ↥sqA := hsquareCard.symm
      _ ≤ Nat.card ↥F := @Subgroup.card_le_of_le A _ sqA F finiteF hle
  · obtain ⟨w, hw⟩ := not_forall.mp hfixsq
    let z : A := w * alpha w
    have hz : z ∈ F := by
      change alpha z = z
      dsimp [z]
      rw [map_mul, halpha w]
      exact commA.mul_comm (alpha w) w
    have hz4 : z ^ 4 = 1 := hfour z
    have hzsq : z ^ 2 = w ^ 2 * alpha (w ^ 2) := by
      dsimp [z]
      rw [mul_pow, ← map_pow]
    have hz2 : z ^ 2 ≠ 1 := by
      intro hz2eq
      apply hw
      calc
        alpha (w ^ 2) = w ^ 2 * (w ^ 2 * alpha (w ^ 2)) := by
          rw [← mul_assoc, ← pow_add, show (2 + 2 : ℕ) = 4 by rfl, hfour w, one_mul]
        _ = w ^ 2 * z ^ 2 := by rw [hzsq]
        _ = w ^ 2 := by rw [hz2eq, mul_one]
    let fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnot : ¬ z ^ 2 ^ 1 = 1 := by simpa using hz2
    have hfin : z ^ 2 ^ (1 + 1) = 1 := by simpa using hz4
    have horder : orderOf z = 4 := by
      have h := @orderOf_eq_prime_pow A _ z 1 2 fact hnot hfin
      simpa using h
    have hzcard : orderOf z ≤ Nat.card ↥F :=
      @Subgroup.orderOf_le_card A _ F (@Set.toFinite A (F : Set A) finiteF) z hz
    calc
      4 = orderOf z := horder.symm
      _ ≤ Nat.card ↥F := hzcard

theorem four_le_card_inf_centralizer_of_c4_prod_c4 {G : Type u} [Group G] {W : Subgroup G}
    (hW : Nonempty (↥W ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    {t : G} (ht : t * t = 1) (hNt : t ∈ Subgroup.normalizer (W : Set G)) :
    4 ≤ Nat.card ↥(W ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let x : Subgroup.normalizer (W : Set G) := ⟨t, hNt⟩
  let alpha : MulAut W := W.normalizerMonoidHom x
  have hxx : x * x = 1 := Subtype.ext ht
  have haa : alpha * alpha = 1 := by
    dsimp only [alpha]
    rw [← map_mul, hxx, map_one]
  have halpha : Function.Involutive alpha := by
    intro w
    have h := congrArg (fun f : MulAut W => f w) haa
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  have hfixed : 4 ≤ Nat.card {w : W // t * (w : G) * t⁻¹ = (w : G)} := by
    have h := four_le_card_fixed_of_c4_prod_c4_involutive hW alpha halpha
    simpa only [alpha, x, Subtype.ext_iff, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  have hcentral : 4 ≤ Nat.card ↥((Subgroup.centralizer ({t} : Set G)).subgroupOf W) := by
    change 4 ≤ Nat.card {w : W // (w : G) ∈ Subgroup.centralizer ({t} : Set G)}
    simp only [mul_inv_eq_iff_eq_mul] at hfixed
    simpa only [Subgroup.mem_centralizer_singleton_iff, eq_comm] using hfixed
  have hcard : Nat.card ↥((W ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf W) =
      Nat.card ↥(W ⊓ Subgroup.centralizer ({t} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : W ⊓ Subgroup.centralizer ({t} : Set G) ≤ W)).toEquiv
  rw [Subgroup.inf_subgroupOf_left (H := Subgroup.centralizer ({t} : Set G)) (K := W)] at hcard
  rw [← hcard]
  exact hcentral

section C4C2FixedPoints

local instance : NeZero 4 := ⟨by decide⟩
local instance : NeZero 2 := ⟨by decide⟩

end C4C2FixedPoints

end CFSG

end
