module

public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.CharacterTheory.Burnside

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32.Loc

@[expose] def fixSub {Q : Type} [Group Q] (σ : MulAut Q) : Subgroup Q :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id Q)

@[expose] def conjAut {Z : Type} [Group Z] (L : Subgroup Z) (s : Z) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) : MulAut ↥L where
  toFun l := ⟨s * l * s⁻¹, hsL l l.2⟩
  invFun l := ⟨s * l * s⁻¹, hsL l l.2⟩
  left_inv l := by
    apply Subtype.ext
    have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    show s * (s * (l : Z) * s⁻¹) * s⁻¹ = l
    rw [hs]
    calc s * (s * (l : Z) * s) * s = (s * s) * l * (s * s) := by group
      _ = l := by rw [hs2]; group
  right_inv l := by
    apply Subtype.ext
    have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    show s * (s * (l : Z) * s⁻¹) * s⁻¹ = l
    rw [hs]
    calc s * (s * (l : Z) * s) * s = (s * s) * l * (s * s) := by group
      _ = l := by rw [hs2]; group
  map_mul' a b := by
    apply Subtype.ext
    show s * ((a : Z) * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹)
    group

theorem local_data {Z : Type} [Group Z] (L : Subgroup Z) (s : Z) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hmove : ∃ l ∈ L, s * l * s⁻¹ ≠ l)
    (P : Subgroup Z) (hPL : P ≤ L) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPs : ∀ x ∈ P, s * x * s⁻¹ = x)
    (hsub : (P.subgroupOf (centralizer ({s} : Set Z))).IsSubnormal) :
    ∃ (σ : MulAut ↥L) (P' : Subgroup ↥L), (∀ l : ↥L, ((σ l : ↥L) : Z) = s * l * s⁻¹) ∧
      σ * σ = 1 ∧ σ ≠ 1 ∧ Nonempty (↥P ≃* ↥P') ∧ P' ≠ ⊥ ∧ ⁅P', P'⁆ = P' ∧
      (∀ x ∈ P', σ x = x) ∧ (P'.subgroupOf (fixSub σ)).IsSubnormal := by
  refine ⟨conjAut L s hs2 hsL, P.subgroupOf L, fun l => rfl, ?_, ?_,
    ⟨(Subgroup.subgroupOfEquivOfLe hPL).symm⟩, ?_, ?_, ?_, ?_⟩
  · ext l
    show s * (s * (l : Z) * s⁻¹) * s⁻¹ = l
    have hs : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rw [hs]
    calc s * (s * (l : Z) * s) * s = (s * s) * l * (s * s) := by group
      _ = l := by rw [hs2]; group
  · intro h
    obtain ⟨l, hl, hne⟩ := hmove
    apply hne
    have := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : Z)) h
    exact this
  · intro h
    apply hP1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hPL hx⟩ : ↥L) ∈ P.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPL, hP]
  · intro x hx
    apply Subtype.ext
    exact hPs x hx
  · set C : Subgroup Z := centralizer ({s} : Set Z) with hC
    let f : ↥(fixSub (conjAut L s hs2 hsL)) →* ↥C :=
      ((L.subtype.comp (fixSub (conjAut L s hs2 hsL)).subtype)).codRestrict C (fun x => by
        have hx : s * ((x : ↥L) : Z) * s⁻¹ = ((x : ↥L) : Z) :=
          congrArg Subtype.val (x.2 : (conjAut L s hs2 hsL) (x : ↥L) = (x : ↥L))
        rw [hC, mem_centralizer_singleton_iff]
        calc ((x : ↥L) : Z) * s = (s * ((x : ↥L) : Z) * s⁻¹) * s := by rw [hx]
          _ = s * ((x : ↥L) : Z) := by group)
    have h1 := hsub.comap f
    convert h1 using 1
    ext x
    simp [f, Subgroup.mem_subgroupOf]

theorem isSolvable_of_card_two_pow_mul_three_pow {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (hX : Nat.card X = 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  let _ : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hX)

end CFSG.GH74.GLS.C3.Layer1.Thm1L32.Loc
