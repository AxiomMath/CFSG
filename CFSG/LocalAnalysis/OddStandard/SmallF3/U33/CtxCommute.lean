module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G]

private lemma mul_mul_assoc_comm {b a' b' : G} (hb : b * a' = a' * b) :
    b * (a' * b') = a' * (b * b') := by
  rw [← mul_assoc, hb, mul_assoc]

private lemma mul_mul_comm_of_commute {a a' b b' : G} (hb : b * a' = a' * b) :
    (a * b) * (a' * b') = (a * a') * (b * b') := by
  simp only [mul_assoc]
  rw [mul_mul_assoc_comm hb]

private lemma inv_mul_eq_mul_inv_of_mul_eq_mul {a a' b b' : G} (h : a * b = a' * b') :
    a'⁻¹ * a = b' * b⁻¹ := by
  have h1 : a = a' * (b' * b⁻¹) := by
    calc
      a = a * b * b⁻¹ := (mul_inv_cancel_right a b).symm
      _ = a' * b' * b⁻¹ := by rw [h]
      _ = a' * (b' * b⁻¹) := by rw [mul_assoc]
  calc
    a'⁻¹ * a = a'⁻¹ * (a' * (b' * b⁻¹)) := by rw [h1]
    _ = b' * b⁻¹ := by rw [inv_mul_cancel_left]

theorem mem_sup_iff_of_commute {P Q : Subgroup G} (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} :
    x ∈ P ⊔ Q ↔ ∃ a ∈ P, ∃ b ∈ Q, x = a * b := by
  constructor
  · intro hx
    let R : Subgroup G :=
      { carrier := {x | ∃ a ∈ P, ∃ b ∈ Q, x = a * b}
        one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, (one_mul 1).symm⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          exact ⟨a * a', P.mul_mem ha ha', b * b', Q.mul_mem hb hb',
            mul_mul_comm_of_commute (a := a) (a' := a') (b := b) (b' := b')
              (h a' ha' b hb).symm⟩
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, P.inv_mem ha, b⁻¹, Q.inv_mem hb, by
            rw [mul_inv_rev, h a⁻¹ (P.inv_mem ha) b⁻¹ (Q.inv_mem hb)]⟩ }
    have hle : P ⊔ Q ≤ R :=
      sup_le (fun a ha => ⟨a, ha, 1, Q.one_mem, (mul_one a).symm⟩)
        (fun b hb => ⟨1, P.one_mem, b, hb, (one_mul b).symm⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem card_sup_of_commute {P Q : Subgroup G} (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a)
    (hinf : P ⊓ Q = ⊥) : Nat.card ↥(P ⊔ Q) = Nat.card ↥P * Nat.card ↥Q := by
  let f : ↥P × ↥Q → ↥(P ⊔ Q) := fun x =>
    ⟨x.1.1 * x.2.1,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
      have heq' : a * b = a' * b' := by
        simpa [f] using Subtype.ext_iff.mp heq
      have hEq : a'⁻¹ * a = b' * b⁻¹ := inv_mul_eq_mul_inv_of_mul_eq_mul heq'
      have hmemP : a'⁻¹ * a ∈ P := P.mul_mem (P.inv_mem ha') ha
      have hmemQ : a'⁻¹ * a ∈ Q := by rw [hEq]; exact Q.mul_mem hb' (Q.inv_mem hb)
      have hmem : a'⁻¹ * a ∈ P ⊓ Q := ⟨hmemP, hmemQ⟩
      have h1 : a'⁻¹ * a = 1 := by
        have := hinf ▸ hmem
        exact Subgroup.mem_bot.mp this
      have haa' : a = a' := (inv_mul_eq_one.mp h1).symm
      have h2 : b' * b⁻¹ = 1 := by
        rw [← hEq, haa']
        exact inv_mul_cancel a'
      have hbb' : b = b' := (mul_inv_eq_one.mp h2).symm
      exact Prod.ext (Subtype.ext haa') (Subtype.ext hbb')
    · intro x
      obtain ⟨a, ha, b, hb, hx⟩ := (mem_sup_iff_of_commute h).1 x.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hx.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_prod _ _)

theorem isPGroup_sup_of_commute {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (hP : IsPGroup p P) (hQ : IsPGroup p Q) :
    IsPGroup p ↥(P ⊔ Q) := by
  rw [IsPGroup.iff_orderOf]
  intro x
  obtain ⟨a, ha, b, hb, hx⟩ := (mem_sup_iff_of_commute h).1 x.2
  obtain ⟨i, hi⟩ := (IsPGroup.iff_orderOf (p := p) (G := ↥P)).1 hP ⟨a, ha⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf (p := p) (G := ↥Q)).1 hQ ⟨b, hb⟩
  have hi' : orderOf a = p ^ i := (Subgroup.orderOf_mk a ha).symm.trans hi
  have hj' : orderOf b = p ^ j := (Subgroup.orderOf_mk b hb).symm.trans hj
  have hcomm : Commute a b := h a ha b hb
  have hdiv : orderOf (a * b) ∣ p ^ max i j := by
    refine (hcomm.orderOf_mul_dvd_lcm).trans (Nat.lcm_dvd ?_ ?_)
    · rw [hi']; exact pow_dvd_pow p (le_max_left i j)
    · rw [hj']; exact pow_dvd_pow p (le_max_right i j)
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdiv
  exact ⟨k, by rw [← Subgroup.orderOf_coe x, hx]; exact hk⟩

theorem isMulCommutative_sup_of_commute {P Q : Subgroup G}
    (h : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) (hP : IsMulCommutative P) (hQ : IsMulCommutative Q) :
    IsMulCommutative ↥(P ⊔ Q) := by
  haveI : IsMulCommutative ↥P := hP
  haveI : IsMulCommutative ↥Q := hQ
  rw [isMulCommutative_iff]
  intro x y
  obtain ⟨a, ha, b, hb, hx⟩ := (mem_sup_iff_of_commute h).1 x.2
  obtain ⟨a', ha', b', hb', hy⟩ := (mem_sup_iff_of_commute h).1 y.2
  have hPcomm : a * a' = a' * a := by
    simpa using congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : P) ⟨a', ha'⟩)
  have hQcomm : b * b' = b' * b := by
    simpa using congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : Q) ⟨b', hb'⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hx, hy,
    mul_mul_comm_of_commute (a := a) (a' := a') (b := b) (b' := b') (h a' ha' b hb).symm,
    mul_mul_comm_of_commute (a := a') (a' := a) (b := b') (b' := b) (h a ha b' hb').symm,
    hPcomm, hQcomm]

end CFSG.OddStandard.SmallF3.HarrisU33