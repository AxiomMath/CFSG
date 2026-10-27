module

public import CFSG.Certificates.Kernel.Co2Cls.Sound

public section

namespace CFSG.KC.Co2Cls

open Subgroup

section Units

variable {M : Type*} [Monoid M]

theorem isUnit_of_mul_eq_one_fin [Finite M] {a b : M} (h : a * b = 1) : IsUnit b := by
  have hinj : Function.Injective (fun x : M => b * x) := by
    intro x y e
    have e2 : a * (b * x) = a * (b * y) := congrArg (a * ·) e
    rwa [← mul_assoc, ← mul_assoc, h, one_mul, one_mul] at e2
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.1 hinj) 1
  have hc' : b * c = 1 := hc
  have hac : a = c := calc
    a = a * (b * c) := by rw [hc', mul_one]
    _ = c := by rw [← mul_assoc, h, one_mul]
  exact ⟨⟨b, a, by rw [hac]; exact hc', h⟩, rfl⟩

theorem isUnit_of_mem_closure {s : Set M} (hs : ∀ x ∈ s, IsUnit x) {x : M}
    (hx : x ∈ Submonoid.closure s) : IsUnit x := by
  induction hx using Submonoid.closure_induction with
  | mem x h => exact hs x h
  | one => exact isUnit_one
  | mul x y _ _ hx hy => exact hx.mul hy

variable [Finite M]

instance finite_units : Finite Mˣ := Finite.of_injective (fun u : Mˣ => (u : M)) fun _ _ => Units.ext

@[expose] def unitsIn (S : Submonoid M) : Subgroup Mˣ where
  carrier := {u | (u : M) ∈ S}
  one_mem' := S.one_mem
  mul_mem' := by
    intro a b ha hb
    change ((a * b : Mˣ) : M) ∈ S
    rw [Units.val_mul]
    exact S.mul_mem ha hb
  inv_mem' := by
    intro u hu
    change ((u⁻¹ : Mˣ) : M) ∈ S
    have hf : IsOfFinOrder u := isOfFinOrder_of_finite u
    have e : u⁻¹ = u ^ (orderOf u - 1) := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [pow_sub_one_mul (Nat.pos_iff_ne_zero.1 hf.orderOf_pos), pow_orderOf_eq_one]
    rw [e, Units.val_pow_eq_pow_val]
    exact S.pow_mem hu _

variable {S : Submonoid M}

variable (hS : ∀ x ∈ S, IsUnit x)
include hS

theorem exists_unitsIn {x : M} (hx : x ∈ S) :
    ∃ u ∈ unitsIn S, (u : M) = x ∧ orderOf u = orderOf x := by
  refine ⟨(hS x hx).unit, ?_, (hS x hx).unit_spec, ?_⟩
  · change ((hS x hx).unit : M) ∈ S
    rw [(hS x hx).unit_spec]
    exact hx
  · rw [← orderOf_units, (hS x hx).unit_spec]

theorem card_unitsIn : Nat.card (unitsIn S) = Nat.card S := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun u => ⟨(u.1 : M), u.2⟩) ⟨fun u v e => ?_, fun x => ?_⟩
  · exact Subtype.ext (Units.ext (congrArg Subtype.val e))
  · obtain ⟨u, hu, e, -⟩ := exists_unitsIn hS x.2
    exact ⟨⟨u, hu⟩, Subtype.ext e⟩

theorem card_conj_unitsIn (a : Mˣ) :
    Nat.card {y : Mˣ // ∃ g ∈ unitsIn S, g * a = y * g} =
      Nat.card {y : M // ∃ g ∈ S, g * (a : M) = y * g} := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun y => ⟨(y.1 : M), ?_⟩) ⟨fun y z e => ?_, fun y => ?_⟩
  · obtain ⟨g, hg, e⟩ := y.2
    exact ⟨g, hg, by rw [← Units.val_mul, e, Units.val_mul]⟩
  · exact Subtype.ext (Units.ext (congrArg Subtype.val e))
  · obtain ⟨g, hg, e⟩ := y.2
    obtain ⟨u, hu, hug, -⟩ := exists_unitsIn hS hg
    refine ⟨⟨u * a * u⁻¹, u, hu, by group⟩, Subtype.ext ?_⟩
    change ((u * a * u⁻¹ : Mˣ) : M) = y.1
    rw [Units.val_mul, Units.val_mul, hug, e, mul_assoc, ← hug, Units.mul_inv, mul_one]

theorem card_cent_unitsIn (a : Mˣ) :
    Nat.card (unitsIn S ⊓ centralizer {a} : Subgroup Mˣ) =
      Nat.card {g : M // g ∈ S ∧ g * (a : M) = a * g} := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun u => ⟨(u.1 : M), u.2.1, ?_⟩) ⟨fun u v e => ?_, fun g => ?_⟩
  · rw [← Units.val_mul, mem_centralizer_singleton_iff.1 u.2.2, Units.val_mul]
  · exact Subtype.ext (Units.ext (congrArg Subtype.val e))
  · obtain ⟨u, hu, hug, -⟩ := exists_unitsIn hS g.2.1
    refine ⟨⟨u, hu, mem_centralizer_singleton_iff.2 (Units.ext ?_)⟩, Subtype.ext hug⟩
    rw [Units.val_mul, Units.val_mul, hug]
    exact g.2.2

end Units

theorem genMonN_isUnit {n : Nat} {G L : Nat → Nat}
    (h : ∀ j < n, Nat.beq (CFSG.KC.Co2InvS.mulV (L j) (G j)) CFSG.KC.Co2InvS.IDP = true) :
    ∀ x ∈ genMonN n G, IsUnit x := by
  intro x hx
  refine isUnit_of_mem_closure ?_ hx
  rintro _ ⟨j, rfl⟩
  have e := congrArg (CFSG.KC.TabMatGrp.MatP 22) (Nat.eq_of_beq_eq_true (h j j.2))
  rw [CFSG.KC.Co2Syl.MatP_mulV, CFSG.KC.Co2Syl.MatP_IDP] at e
  exact isUnit_of_mul_eq_one_fin e

end CFSG.KC.Co2Cls

end
