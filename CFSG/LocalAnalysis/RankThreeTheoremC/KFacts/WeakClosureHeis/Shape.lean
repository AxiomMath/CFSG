module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup

@[expose] def heisZ {X : Type*} [Group X] (Q₁ : Subgroup X) : Subgroup X :=
  Q₁ ⊓ centralizer (Q₁ : Set X)

structure HeisShape (p : ℕ) {X : Type*} [Group X] (Q Q₀ Q₁ : Subgroup X) : Prop where
  pgrp : IsPGroup p Q
  cyc : IsCyclic Q₀
  ne_bot : Q₀ ≠ ⊥
  card : Nat.card Q₁ = p ^ 3
  nonab : ¬ IsMulCommutative Q₁
  exp : ∀ q ∈ Q₁, q ^ p = 1
  comm : ∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a
  disj : Q₀ ⊓ Q₁ = ⊥
  sup : Q₀ ⊔ Q₁ = Q

private theorem commutator_mem_heisZ {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] {T : Subgroup X}
    (hcard : Nat.card T = p ^ 3) (hnc : ¬ IsMulCommutative T) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ heisZ T := by
  have hZ : Nat.card (center T) = p :=
    Generic49U3.card_center_of_nonabelian_card_p_cube hcard hnc
  have hQ : Nat.card (T ⧸ center T) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [hcard, hZ] at h1
    apply Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
    rw [← h1]
    ring
  have hcomm : IsMulCommutative (T ⧸ center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  intro a ha b hb
  have key : (⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ ∈ center T := by
    rw [← QuotientGroup.eq_one_iff]
    have hab := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ center T)
      (QuotientGroup.mk ⟨b, hb⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hab
  refine Subgroup.mem_inf.mpr
    ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := mem_center_iff.mp key ⟨s, hs⟩
  exact congrArg Subtype.val this

namespace HeisShape

variable {p : ℕ} {X : Type*} [Group X] {Q Q₀ Q₁ : Subgroup X}

theorem left_le (h : HeisShape p Q Q₀ Q₁) : Q₀ ≤ Q := h.sup ▸ le_sup_left

theorem right_le (h : HeisShape p Q Q₀ Q₁) : Q₁ ≤ Q := h.sup ▸ le_sup_right

theorem left_pgrp (h : HeisShape p Q Q₀ Q₁) : IsPGroup p Q₀ :=
  IsPGroup.to_le h.pgrp h.left_le

theorem exists_mul (h : HeisShape p Q Q₀ Q₁) {q : X} (hq : q ∈ Q) :
    ∃ a ∈ Q₀, ∃ b ∈ Q₁, q = a * b := by
  let S : Subgroup X :=
    { carrier := {q | ∃ a ∈ Q₀, ∃ b ∈ Q₁, q = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', Q₀.mul_mem ha ha', b * b', Q₁.mul_mem hb hb', ?_⟩
        have hc : b * a' = a' * b := (h.comm a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hc]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, Q₀.one_mem, 1, Q₁.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, Q₀.inv_mem ha, b⁻¹, Q₁.inv_mem hb, ?_⟩
        rw [mul_inv_rev]
        exact (h.comm a⁻¹ (Q₀.inv_mem ha) b⁻¹ (Q₁.inv_mem hb)).symm }
  have hle : Q₀ ⊔ Q₁ ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, Q₁.one_mem, (mul_one a).symm⟩)
      (fun b hb => ⟨1, Q₀.one_mem, b, hb, (one_mul b).symm⟩)
  rw [h.sup] at hle
  exact hle hq

theorem eq_of_mul_eq (h : HeisShape p Q Q₀ Q₁) {a a' b b' : X} (ha : a ∈ Q₀) (ha' : a' ∈ Q₀)
    (hb : b ∈ Q₁) (hb' : b' ∈ Q₁) (hab : a * b = a' * b') : a = a' ∧ b = b' := by
  have key : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
      _ = b' * b⁻¹ := by group
  have h0 : a'⁻¹ * a ∈ Q₀ ⊓ Q₁ :=
    Subgroup.mem_inf.mpr ⟨Q₀.mul_mem (Q₀.inv_mem ha') ha, by
      rw [key]
      exact Q₁.mul_mem hb' (Q₁.inv_mem hb)⟩
  rw [h.disj, Subgroup.mem_bot] at h0
  have h1 : a = a' := (inv_mul_eq_one.mp h0).symm
  refine ⟨h1, ?_⟩
  subst h1
  exact mul_left_cancel hab

theorem mul_mem (h : HeisShape p Q Q₀ Q₁) {a b : X} (ha : a ∈ Q₀) (hb : b ∈ Q₁) : a * b ∈ Q :=
  Q.mul_mem (h.left_le ha) (h.right_le hb)

private theorem comm_left (h : HeisShape p Q Q₀ Q₁) {a a' : X} (ha : a ∈ Q₀) (ha' : a' ∈ Q₀) :
    a * a' = a' * a := by
  haveI := h.cyc
  have := (IsCyclic.isMulCommutative (α := Q₀)).is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩
  exact congrArg Subtype.val this

theorem commute_left (h : HeisShape p Q Q₀ Q₁) {a q : X} (ha : a ∈ Q₀) (hq : q ∈ Q) :
    a * q = q * a := by
  obtain ⟨a', ha', b, hb, rfl⟩ := h.exists_mul hq
  have h1 : a * a' = a' * a := h.comm_left ha ha'
  have h2 : a * b = b * a := h.comm a ha b hb
  calc a * (a' * b) = (a * a') * b := by group
    _ = (a' * a) * b := by rw [h1]
    _ = a' * (a * b) := by group
    _ = a' * (b * a) := by rw [h2]
    _ = a' * b * a := by group

theorem card_heisZ [Fact p.Prime] [Finite X] (h : HeisShape p Q Q₀ Q₁) : Nat.card (heisZ Q₁) = p :=
  Generic49U3.card_inf_centralizer_of_nonabelian_card_p_cube h.card h.nonab

theorem commutator_mem [Fact p.Prime] [Finite X] (h : HeisShape p Q Q₀ Q₁) {q q' : X} (hq : q ∈ Q)
    (hq' : q' ∈ Q) : q * q' * q⁻¹ * q'⁻¹ ∈ heisZ Q₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hq
  obtain ⟨a', ha', b', hb', rfl⟩ := h.exists_mul hq'
  have hbQ : b ∈ Q := h.right_le hb
  have hb'Q : b' ∈ Q := h.right_le hb'
  have hA : a * (b * (a' * b') * b⁻¹) = (b * (a' * b') * b⁻¹) * a :=
    h.commute_left ha (Q.mul_mem (Q.mul_mem hbQ hq') (Q.inv_mem hbQ))
  have hB : a' * (b * b' * b⁻¹ * b'⁻¹) = (b * b' * b⁻¹ * b'⁻¹) * a' :=
    h.commute_left ha'
      (Q.mul_mem (Q.mul_mem (Q.mul_mem hbQ hb'Q) (Q.inv_mem hbQ)) (Q.inv_mem hb'Q))
  have hC : a' * b = b * a' := h.comm a' ha' b hb
  have heq : a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹ = b * b' * b⁻¹ * b'⁻¹ := by
    calc a * b * (a' * b') * (a * b)⁻¹ * (a' * b')⁻¹
        = a * (b * (a' * b') * b⁻¹) * a⁻¹ * (a' * b')⁻¹ := by group
      _ = (b * (a' * b') * b⁻¹) * a * a⁻¹ * (a' * b')⁻¹ := by rw [hA]
      _ = (b * a') * (b' * b⁻¹ * b'⁻¹) * a'⁻¹ := by group
      _ = a' * (b * b' * b⁻¹ * b'⁻¹) * a'⁻¹ := by rw [← hC]; group
      _ = (b * b' * b⁻¹ * b'⁻¹) * a' * a'⁻¹ := by rw [hB]
      _ = b * b' * b⁻¹ * b'⁻¹ := by group
  rw [heq]
  exact commutator_mem_heisZ h.card h.nonab b hb b' hb'

theorem pow_eq_one_iff (h : HeisShape p Q Q₀ Q₁) {a b : X} (ha : a ∈ Q₀) (hb : b ∈ Q₁) :
    (a * b) ^ p = 1 ↔ a ^ p = 1 := by
  have hc : Commute a b := h.comm a ha b hb
  rw [hc.mul_pow, h.exp b hb, mul_one]

theorem ncard_pow_eq_one_le [Fact p.Prime] [Finite X] (h : HeisShape p Q Q₀ Q₁) :
    {q : X | q ∈ Q ∧ q ^ p = 1}.ncard ≤ p ^ 4 := by
  classical
  haveI : Fintype Q₀ := Fintype.ofFinite _
  haveI := h.cyc
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hΩ : {a : X | a ∈ Q₀ ∧ a ^ p = 1}.ncard ≤ p := by
    have h1 : {a : X | a ∈ Q₀ ∧ a ^ p = 1} = Subtype.val '' {a : Q₀ | a ^ p = 1} := by
      ext x
      constructor
      · rintro ⟨hx, hxp⟩
        exact ⟨⟨x, hx⟩, Subtype.ext_iff.mpr (by simpa using hxp), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    rw [h1]
    calc (Subtype.val '' {a : Q₀ | a ^ p = 1}).ncard
        ≤ {a : Q₀ | a ^ p = 1}.ncard := Set.ncard_image_le
      _ = (Finset.univ.filter (fun a : Q₀ => a ^ p = 1)).card := by
        rw [← Set.ncard_coe_finset]; simp
      _ ≤ p := IsCyclic.card_pow_eq_one_le hp
  have hB : (Q₁ : Set X).ncard = p ^ 3 := by
    rw [← h.card]
    exact (Nat.card_coe_set_eq (Q₁ : Set X)).symm
  have hsub : {q : X | q ∈ Q ∧ q ^ p = 1} ⊆
      (fun x : X × X => x.1 * x.2) '' ({a : X | a ∈ Q₀ ∧ a ^ p = 1} ×ˢ (Q₁ : Set X)) := by
    rintro q ⟨hq, hqp⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul hq
    exact ⟨(a, b), ⟨⟨ha, (h.pow_eq_one_iff ha hb).mp hqp⟩, hb⟩, rfl⟩
  calc {q : X | q ∈ Q ∧ q ^ p = 1}.ncard
      ≤ ((fun x : X × X => x.1 * x.2) ''
          ({a : X | a ∈ Q₀ ∧ a ^ p = 1} ×ˢ (Q₁ : Set X))).ncard := Set.ncard_le_ncard hsub
    _ ≤ ({a : X | a ∈ Q₀ ∧ a ^ p = 1} ×ˢ (Q₁ : Set X)).ncard := Set.ncard_image_le
    _ = {a : X | a ∈ Q₀ ∧ a ^ p = 1}.ncard * (Q₁ : Set X).ncard := Set.ncard_prod
    _ ≤ p * p ^ 3 := by rw [hB]; exact Nat.mul_le_mul_right _ hΩ
    _ = p ^ 4 := by ring

end HeisShape

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
