module

public import CFSG.ClassicalInvolution.AschTight.S1916Wreath

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G]

theorem centralizes_of_isCyclic_of_odd [Finite G] {D : Subgroup G} (hDcyc : IsCyclic D)
    (hD2 : IsPGroup 2 D) {n : G} (hnD : conjSub n D = D) (hno : Odd (orderOf n)) :
    ∀ x ∈ D, n * x * n⁻¹ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ x ∈ D, n * x * n⁻¹ ∈ D := fun x hx => hnD ▸ conj_mem_conjSub hx
  have hmem' : ∀ x ∈ D, n⁻¹ * x * n ∈ D := by
    intro x hx
    have h1 : x ∈ conjSub n D := hnD.symm ▸ hx
    rw [mem_conjSub_iff] at h1
    exact h1
  let α : MulAut ↥D :=
    { toFun := fun x => ⟨n * x * n⁻¹, hmem x x.2⟩
      invFun := fun x => ⟨n⁻¹ * x * n, hmem' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hαpow : ∀ k : ℕ, ∀ x : ↥D, (((α ^ k) x : ↥D) : G) = n ^ k * x * (n ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply]
      change n * (((α ^ k) x : ↥D) : G) * n⁻¹ = _
      rw [ih x, pow_succ']
      group
  have hα1 : α ^ orderOf n = 1 := by
    ext x
    rw [hαpow, pow_orderOf_eq_one]
    simp
  have hdvd1 : orderOf α ∣ orderOf n := orderOf_dvd_of_pow_eq_one hα1
  obtain ⟨k, hk⟩ := hD2.exists_card_eq
  have hdvd2 : orderOf α ∣ 2 ^ (k - 1) := by
    have h1 := orderOf_dvd_natCard α
    rw [IsCyclic.card_mulAut, hk] at h1
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk0] at h1 ⊢
      simpa using h1
    · rw [Nat.totient_prime_pow Nat.prime_two hk0] at h1
      simpa using h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hj0
    have h2 : 2 ∣ orderOf n := (hj ▸ dvd_pow_self 2 hj0 : 2 ∣ orderOf α).trans hdvd1
    exact (Nat.not_even_iff_odd.mpr hno) (even_iff_two_dvd.mpr h2)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  intro x hx
  have := congrArg (fun β : MulAut ↥D => ((β ⟨x, hx⟩ : ↥D) : G)) hj
  exact this

structure WrData (P : Subgroup G) (a c b : G) (B : Subgroup G) : Prop where
  B_eq : Subgroup.zpowers a ⊔ Subgroup.zpowers c = B
  comm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  four : 4 ≤ orderOf a
  hac : a * c = c * a
  b2 : b * b = 1
  bac : b * a * b⁻¹ = c
  bca : b * c * b⁻¹ = a
  P_eq : P = B ⊔ Subgroup.zpowers b
  bB : b ∉ B
  bN : b ∈ Subgroup.normalizer (B : Set G)
  card_B : Nat.card B = orderOf a * orderOf a
  card_P : Nat.card P = 2 * (orderOf a * orderOf a)
  inter : ∀ x ∈ Subgroup.zpowers a, x ∈ Subgroup.zpowers c → x = 1
  ord_ac : orderOf (a * c) = orderOf a

theorem WrData.BP {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) : B ≤ P :=
  h.P_eq ▸ le_sup_left

theorem WrData.bP {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) : b ∈ P :=
  h.P_eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b)

theorem WrData.PB {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) :
    ∀ x ∈ P, x ∈ B ∨ x * b ∈ B := fun _ hx =>
  mem_or_mul_mem_of_closure h.b2 h.bN (h.P_eq ▸ hx)

theorem WrData.conj {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) (i j : ℤ) :
    b * (a ^ i * c ^ j) * b⁻¹ = c ^ i * a ^ j := by
  rw [show b * (a ^ i * c ^ j) * b⁻¹ = (b * a * b⁻¹) ^ i * (b * c * b⁻¹) ^ j by
    rw [conj_zpow, conj_zpow]; group, h.bac, h.bca]

theorem WrData.mem_B {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) {x : G}
    (hx : x ∈ B) : ∃ i j : ℤ, a ^ i * c ^ j = x :=
  exists_zpow_mul_zpow_of_mem_sup h.hac (h.B_eq ▸ hx)

theorem WrData.fix {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) {x : G} (hx : x ∈ B)
    (hbx : b * x * b⁻¹ = x) : x ∈ Subgroup.zpowers (a * c) := by
  obtain ⟨i, j, rfl⟩ := h.mem_B hx
  have hacc : Commute a c := h.hac
  have hx' : a ^ i * c ^ j = (a * c) ^ i * c ^ (j - i) := by
    rw [hacc.mul_zpow, mul_assoc, ← zpow_add, add_sub_cancel]
  have hx'' : c ^ i * a ^ j = (a * c) ^ i * a ^ (j - i) := by
    rw [hacc.mul_zpow, show a ^ i * c ^ i = c ^ i * a ^ i from (hacc.zpow_zpow i i).eq,
      mul_assoc, ← zpow_add, add_sub_cancel]
  rw [h.conj, hx'', hx'] at hbx
  have h1 : a ^ (j - i) = c ^ (j - i) := mul_left_cancel hbx
  have h2 : c ^ (j - i) = 1 := by
    rw [← h1]
    refine h.inter _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _) ?_
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _
  rw [hx', h2, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem WrData.anti {P B : Subgroup G} {a c b : G} (h : WrData P a c b B) {x : G} (hx : x ∈ B)
    (hbx : b * x * b⁻¹ = x⁻¹) : x ∈ Subgroup.zpowers (a * c⁻¹) := by
  obtain ⟨i, j, rfl⟩ := h.mem_B hx
  have hacc : Commute a c := h.hac
  rw [h.conj] at hbx
  have h1 : c ^ (i + j) = a ^ (-(i + j)) := by
    calc c ^ (i + j) = c ^ j * (c ^ i * a ^ j) * a ^ (-j) := by group
      _ = c ^ j * (a ^ i * c ^ j)⁻¹ * a ^ (-j) := by rw [hbx]
      _ = a ^ (-(i + j)) := by group
  have h2 : c ^ (i + j) = 1 := by
    refine h.inter _ ?_ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _)
    rw [h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _
  have hx' : a ^ i * c ^ j = (a * c⁻¹) ^ i * c ^ (i + j) := by
    rw [(hacc.inv_right).mul_zpow, inv_zpow', mul_assoc, ← zpow_add]
    congr 2
    ring
  rw [hx', h2, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
