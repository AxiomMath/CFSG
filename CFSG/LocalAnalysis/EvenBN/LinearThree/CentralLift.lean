module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup
open scoped commutatorElement

section CentralLift

variable {Y P : Type*} [Group Y] [Group P] (π : Y →* P)

theorem mul_self_eq_one_of_conj {x y c : Y} (hc : c ∈ center Y) (hx : x * x = 1)
    (hxy : x * y * x⁻¹ = c * y) : c * c = 1 := by
  have hcx : c * x = x * c := (mem_center_iff.1 hc x).symm
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [hxinv] at hxy
  have h1 : y = x * (x * y * x) * x := by
    rw [show x * (x * y * x) * x = (x * x) * y * (x * x) by group, hx, one_mul, mul_one]
  have h2 : x * (c * y) * x = c * (x * y * x) := by
    rw [← mul_assoc, ← mul_assoc, ← hcx]; group
  rw [hxy, h2, hxy] at h1
  have h3 : c * c * y = 1 * y := by rw [one_mul, ← mul_assoc] at *; exact h1.symm
  exact mul_right_cancel h3

variable {π}

theorem eq_one_of_mem_ker_of_mul_self (hodd : Odd (Nat.card π.ker)) {z : Y} (hz : z ∈ π.ker)
    (hz2 : z * z = 1) : z = 1 := by
  by_contra hz1
  have h2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have h := Subgroup.orderOf_dvd_natCard π.ker hz
  rw [h2] at h
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)

theorem commute_of_mul_self (hker : π.ker ≤ center Y) (hodd : Odd (Nat.card π.ker)) {x y : Y}
    (hx : x * x = 1) (_hy : y * y = 1) (hc : π x * π y = π y * π x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcK : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hxy : x * y * x⁻¹ = c * y := by rw [hcdef]; group
  have hc1 := eq_one_of_mem_ker_of_mul_self hodd hcK (mul_self_eq_one_of_conj (hker hcK) hx hxy)
  rw [hc1, one_mul] at hxy
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [hxy]

theorem exists_liftSq (hker : π.ker ≤ center Y) (hodd : Odd (Nat.card π.ker)) (E : Subgroup P)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∃ R : Subgroup Y, ∀ x, x ∈ R ↔ π x ∈ E ∧ x * x = 1 := by
  refine ⟨{ carrier := {x | π x ∈ E ∧ x * x = 1}
            mul_mem' := ?_
            one_mem' := ⟨by rw [map_one]; exact one_mem E, mul_one 1⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxE, hx⟩ ⟨hyE, hy⟩
    have hxy := commute_of_mul_self hker hodd hx hy (hE _ hxE _ hyE)
    refine ⟨by rw [map_mul]; exact mul_mem hxE hyE, ?_⟩
    calc x * y * (x * y) = (x * x) * (y * y) := by
          rw [mul_assoc, ← mul_assoc y, ← hxy]; group
      _ = 1 := by rw [hx, hy, one_mul]
  · rintro x ⟨hxE, hx⟩
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    exact ⟨by rw [hxinv]; exact hxE, by rw [hxinv]; exact hx⟩

theorem comm_of_liftSq (hker : π.ker ≤ center Y) (hodd : Odd (Nat.card π.ker)) {E : Subgroup P}
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {S : Subgroup Y}
    (hS : ∀ x, x ∈ S ↔ π x ∈ E ∧ x * x = 1) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  intro x hx y hy
  obtain ⟨hxE, hx2⟩ := (hS x).1 hx
  obtain ⟨hyE, hy2⟩ := (hS y).1 hy
  exact commute_of_mul_self hker hodd hx2 hy2 (hE _ hxE _ hyE)

theorem eq_of_liftSq (hodd : Odd (Nat.card π.ker)) {E : Subgroup P} {S : Subgroup Y}
    (hS : ∀ x, x ∈ S ↔ π x ∈ E ∧ x * x = 1) {x y : Y} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : π x = π y) : x = y := by
  have hm : x⁻¹ * y ∈ S := mul_mem (inv_mem hx) hy
  have hk : x⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have h1 := eq_one_of_mem_ker_of_mul_self hodd hk ((hS _).1 hm).2
  calc x = x * (x⁻¹ * y) := by rw [h1, mul_one]
    _ = y := by group

theorem map_liftSq (hodd : Odd (Nat.card π.ker)) {E : Subgroup P} (hEπ : E ≤ π.range)
    (hE2 : ∀ a ∈ E, a * a = 1) {S : Subgroup Y} (hS : ∀ x, x ∈ S ↔ π x ∈ E ∧ x * x = 1) :
    S.map π = E := by
  refine le_antisymm (fun _ ⟨x, hx, hxv⟩ => hxv ▸ ((hS x).1 hx).1) fun v hv => ?_
  obtain ⟨x, rfl⟩ := hEπ hv
  have hxx : x * x ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul]; exact hE2 _ hv
  set m := orderOf (x * x) with hm
  have hmodd : Odd m := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard π.ker hxx)
  obtain ⟨k, hk⟩ := hmodd
  have hv2 : π x * π x = 1 := hE2 _ hv
  have hpow : π x ^ m = π x := by
    rw [hk, pow_succ, pow_mul, sq, hv2, one_pow, one_mul]
  refine ⟨x ^ m, (hS _).2 ⟨by rw [map_pow, hpow]; exact hv, ?_⟩, by rw [map_pow, hpow]⟩
  rw [← pow_add, ← two_mul, pow_mul, sq, pow_orderOf_eq_one]

theorem card_liftSq (hodd : Odd (Nat.card π.ker)) {E : Subgroup P} (hEπ : E ≤ π.range)
    (hE2 : ∀ a ∈ E, a * a = 1) {S : Subgroup Y} (hS : ∀ x, x ∈ S ↔ π x ∈ E ∧ x * x = 1) :
    Nat.card S = Nat.card E := by
  have hmap := map_liftSq hodd hEπ hE2 hS
  let φ : S →* E := (π.comp S.subtype).codRestrict E fun x => ((hS x).1 x.2).1
  have hinj : Function.Injective φ := fun x y hxy =>
    Subtype.ext (eq_of_liftSq hodd hS x.2 y.2 (congrArg Subtype.val hxy))
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    rw [← hmap] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).toEquiv

theorem commutatorElement_mul_mul_of_mem_center {x y z z' : Y} (hz : z ∈ center Y)
    (hz' : z' ∈ center Y) : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  have h1 : z * y = y * z := (mem_center_iff.1 hz y).symm
  have h2 : z * z' = z' * z := (mem_center_iff.1 hz z').symm
  have h3 : z' * x = x * z' := (mem_center_iff.1 hz' x).symm
  have e1 : z * (y * z') * z⁻¹ = y * z' := by
    calc z * (y * z') * z⁻¹ = (z * y) * z' * z⁻¹ := by group
      _ = y * (z * z') * z⁻¹ := by rw [h1]; group
      _ = y * z' := by rw [h2]; group
  have e2 : z' * x⁻¹ * z'⁻¹ = x⁻¹ := by
    have h3' : z' * x⁻¹ = x⁻¹ * z' := by
      calc z' * x⁻¹ = x⁻¹ * (x * z') * x⁻¹ := by group
        _ = x⁻¹ * (z' * x) * x⁻¹ := by rw [h3]
        _ = x⁻¹ * z' := by group
    rw [h3', mul_inv_cancel_right]
  calc ⁅x * z, y * z'⁆ = x * (z * (y * z') * z⁻¹) * x⁻¹ * z'⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * (z' * x⁻¹ * z'⁻¹) * y⁻¹ := by rw [e1]; group
    _ = ⁅x, y⁆ := by rw [e2, commutatorElement_def]

theorem commutator_sup_le_of_le_center {H Z : Subgroup Y} (hZ : Z ≤ center Y) :
    ⁅H ⊔ Z, H ⊔ Z⁆ ≤ ⁅H, H⁆ := by
  have : Z.Normal :=
    ⟨fun z hz g => by rw [mem_center_iff.1 (hZ hz) g, mul_inv_cancel_right]; exact hz⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, z, hz, rfl⟩ := mem_sup_of_normal_right.1 ha
  obtain ⟨x', hx', z', hz', rfl⟩ := mem_sup_of_normal_right.1 hb
  rw [commutatorElement_mul_mul_of_mem_center (hZ hz) (hZ hz')]
  exact commutator_mem_commutator hx hx'

theorem exists_liftPerfect (hker : π.ker ≤ center Y) {D : Subgroup P} (hD : ⁅D, D⁆ = D)
    (hDπ : D ≤ π.range) : ∃ X : Subgroup Y, ⁅X, X⁆ = X ∧ X.map π = D ∧ X ≤ D.comap π := by
  set C := D.comap π with hC
  have hCD : C.map π = D := by
    rw [hC, Subgroup.map_comap_eq, inf_eq_right.2 hDπ]
  have hmap : (⁅C, C⁆).map π = D := by rw [map_commutator, hCD, hD]
  have hCle : C ≤ ⁅C, C⁆ ⊔ π.ker := by
    intro y hy
    have hy' : π y ∈ (⁅C, C⁆).map π := by rw [hmap]; exact hy
    obtain ⟨x, hx, hxy⟩ := hy'
    have hk : x⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    rw [show y = x * (x⁻¹ * y) by group]
    exact mul_mem (mem_sup_left hx) (mem_sup_right hk)
  have hCC : ⁅C, C⁆ ≤ C := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  refine ⟨⁅C, C⁆, le_antisymm (commutator_mono hCC hCC) ?_, hmap, hCC⟩
  exact (commutator_mono hCle hCle).trans (commutator_sup_le_of_le_center hker)

variable (π) in
theorem exists_mulAut_comp [Finite P] (hπ : Function.Surjective π) (α : Y ≃* Y)
    (hα : ∀ z ∈ π.ker, α z ∈ π.ker) : ∃ β : MulAut P, ∀ x, β (π x) = π (α x) := by
  have key : ∀ x y : Y, π x = π y → π (α x) = π (α y) := by
    intro x y hxy
    have hk : x⁻¹ * y ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have hk' := hα _ hk
    rw [MonoidHom.mem_ker] at hk'
    simp only [map_mul, map_inv] at hk'
    exact inv_mul_eq_one.1 hk'
  set s := Function.surjInv hπ with hs
  have hss : ∀ p, π (s p) = p := Function.surjInv_eq hπ
  let β₀ : P →* P :=
    { toFun := fun p => π (α (s p))
      map_one' := by
        rw [key (s 1) 1 (by rw [hss, map_one]), map_one, map_one]
      map_mul' := fun p p' => by
        rw [key (s (p * p')) (s p * s p') (by rw [hss, map_mul, hss, hss]), map_mul, map_mul] }
  have hβ : ∀ x, β₀ (π x) = π (α x) := fun x => key _ _ (hss (π x))
  have hsurj : Function.Surjective β₀ := by
    intro p
    obtain ⟨x, rfl⟩ := hπ p
    exact ⟨π (α.symm x), by rw [hβ, MulEquiv.apply_symm_apply]⟩
  exact ⟨MulEquiv.ofBijective β₀ ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩, hβ⟩

variable {X : Subgroup Y}

theorem forall_apply_eq_of_perfect (α : Y →* Y) (hX : ⁅X, X⁆ = X)
    (hZ : ∀ x ∈ X, ∃ z ∈ center Y, α x = x * z) : ∀ x ∈ X, α x = x := by
  have hle : ⁅X, X⁆ ≤ MonoidHom.eqLocus α (MonoidHom.id Y) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨z, hz, hza⟩ := hZ a ha
    obtain ⟨z', hz', hzb⟩ := hZ b hb
    show α ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hza, hzb, commutatorElement_mul_mul_of_mem_center hz hz']
  intro x hx
  rw [← hX] at hx
  exact hle hx

end CentralLift

end CFSG.LocalAnalysis.EvenBN.LinearThree
