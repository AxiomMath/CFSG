module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup

variable {G : Type*} [Group G] [Finite G]

namespace NormHeis

theorem eq_one_or_eq_of_mem_zpowers {z : G} (hzz : z * z = 1) {c : G} (hc : c ∈ zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_two, hzz, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hzz, one_zpow, one_mul, zpow_one]

theorem mul_comm_iff_commutator_eq_one {a b : G} :
    a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem mem_inf_centralizer_iff {H : Subgroup G} {u : G} :
    u ∈ H ⊓ centralizer (H : Set G) ↔ u ∈ H ∧ ∀ y ∈ H, y * u = u * y := by
  simp [mem_inf, mem_centralizer_iff]

theorem mem_inf_centralizer_singleton_iff {H : Subgroup G} {a b : G} :
    b ∈ H ⊓ centralizer ({a} : Set G) ↔ b ∈ H ∧ a * b = b * a := by
  simp [mem_inf, mem_centralizer_iff]

theorem card_eq_two_mul_of_xor {K L : Subgroup G} (hKL : K ≤ L) {c : G} (hc : c ∈ L)
    (h : ∀ b ∈ L, Xor (b * c ∈ K) (b ∈ K)) : Nat.card L = 2 * Nat.card K := by
  have h2 : K.relIndex L = 2 := relIndex_eq_two_iff.2 ⟨c, hc, h⟩
  have h3 := relIndex_mul_card (H := K) (K := L)
  rw [h2, inf_of_le_left hKL] at h3
  exact h3.symm

theorem forall_mul_comm_of_cover {H H₁ : Subgroup G} {y₀ w : G}
    (hcov : ∀ y ∈ H, Xor (y * y₀ ∈ H₁) (y ∈ H₁)) (hw₁ : ∀ y ∈ H₁, y * w = w * y)
    (hw₀ : y₀ * w = w * y₀) : ∀ y ∈ H, y * w = w * y := by
  intro y hy
  rcases (hcov y hy).or with h | h
  · have h1 : y * y₀ * w = w * (y * y₀) := hw₁ _ h
    have h2 : y * w * y₀ = w * y * y₀ :=
      calc y * w * y₀ = y * (w * y₀) := by rw [mul_assoc]
        _ = y * (y₀ * w) := by rw [hw₀]
        _ = y * y₀ * w := by rw [mul_assoc]
        _ = w * (y * y₀) := h1
        _ = w * y * y₀ := by rw [mul_assoc]
    exact mul_right_cancel h2
  · exact hw₁ y h

section Commutator

variable {z : G} {H : Subgroup G}

theorem mul_comm_commutator (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a b y : G}
    (ha : a ∈ H) (hb : b ∈ H) (hy : y ∈ H) :
    y * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * y := by
  rcases eq_one_or_eq_of_mem_zpowers hzz (hcomm a ha b hb) with h | h
  · rw [h, mul_one, one_mul]
  · rw [h]
    exact hHz y hy

theorem commutator_mul (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a b c : G}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by
  have h := mul_comm_commutator hzz hHz hcomm ha hc hb
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * c * a⁻¹ * c⁻¹) * b * b⁻¹) := by rw [h]
    _ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group

theorem commutator_eq_of_not_comm (hzz : z * z = 1)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a y₀ : G}
    (ha : a ∈ H) (hy₀ : y₀ ∈ H) (hne : ¬ a * y₀ = y₀ * a) :
    a * y₀ * a⁻¹ * y₀⁻¹ = z ∧ z ≠ 1 := by
  have h : a * y₀ * a⁻¹ * y₀⁻¹ = z := by
    rcases eq_one_or_eq_of_mem_zpowers hzz (hcomm a ha y₀ hy₀) with h | h
    · exact absurd (mul_comm_iff_commutator_eq_one.2 h) hne
    · exact h
  exact ⟨h, fun h1 => hne (mul_comm_iff_commutator_eq_one.2 (h.trans h1))⟩

theorem mul_comm_mul_iff (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a y₀ b : G}
    (ha : a ∈ H) (hy₀ : y₀ ∈ H) (hb : b ∈ H) (hne : ¬ a * y₀ = y₀ * a) :
    a * (b * y₀) = (b * y₀) * a ↔ ¬ a * b = b * a := by
  obtain ⟨hc₂, hz1⟩ := commutator_eq_of_not_comm hzz hcomm ha hy₀ hne
  rw [mul_comm_iff_commutator_eq_one (a := a) (b := b * y₀),
    mul_comm_iff_commutator_eq_one (a := a) (b := b), commutator_mul hzz hHz hcomm ha hb hy₀,
    hc₂, mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right hzz]
  rcases eq_one_or_eq_of_mem_zpowers hzz (hcomm a ha b hb) with h | h
  · rw [h]
    simp [hz1.symm]
  · rw [h]
    simp [hz1]

theorem xor_mul_mem_of_not_comm (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a y₀ : G} {H₁ : Subgroup G}
    (ha : a ∈ H) (hy₀ : y₀ ∈ H) (hne : ¬ a * y₀ = y₀ * a)
    (hH₁ : ∀ x, x ∈ H₁ ↔ x ∈ H ∧ a * x = x * a) :
    ∀ b ∈ H, Xor (b * y₀ ∈ H₁) (b ∈ H₁) := by
  intro b hb
  rw [hH₁, hH₁, mul_comm_mul_iff hzz hHz hcomm ha hy₀ hb hne]
  by_cases hP : a * b = b * a
  · exact Or.inr ⟨⟨hb, hP⟩, fun h => h.2 hP⟩
  · exact Or.inl ⟨⟨H.mul_mem hb hy₀, hP⟩, fun h => hP h.2⟩

theorem card_eq_two_mul_of_not_comm (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a y₀ : G} {H₁ : Subgroup G}
    (ha : a ∈ H) (hy₀ : y₀ ∈ H) (hne : ¬ a * y₀ = y₀ * a)
    (hH₁ : ∀ x, x ∈ H₁ ↔ x ∈ H ∧ a * x = x * a) :
    Nat.card H = 2 * Nat.card H₁ :=
  card_eq_two_mul_of_xor (fun x hx => ((hH₁ x).1 hx).1) hy₀
    (xor_mul_mem_of_not_comm hzz hHz hcomm ha hy₀ hne hH₁)

theorem card_center_eq_two_mul (hzz : z * z = 1) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) {a y₀ : G} {H₁ : Subgroup G}
    (ha : a ∈ H) (hy₀ : y₀ ∈ H) (hne : ¬ a * y₀ = y₀ * a)
    (hH₁ : ∀ x, x ∈ H₁ ↔ x ∈ H ∧ a * x = x * a) :
    Nat.card (H₁ ⊓ centralizer (H₁ : Set G) : Subgroup G) =
      2 * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) := by
  have hcov := xor_mul_mem_of_not_comm hzz hHz hcomm ha hy₀ hne hH₁
  have haH₁ : a ∈ H₁ := (hH₁ a).2 ⟨ha, rfl⟩
  have hH₁H : ∀ x ∈ H₁, x ∈ H := fun x hx => ((hH₁ x).1 hx).1
  have hax : ∀ x ∈ H₁, x * a = a * x := fun x hx => ((hH₁ x).1 hx).2.symm
  have haZ : a ∉ H ⊓ centralizer (H : Set G) := by
    rw [mem_inf_centralizer_iff]
    exact fun h => hne (h.2 y₀ hy₀).symm
  refine card_eq_two_mul_of_xor (c := a) ?_ ?_ ?_
  · intro u hu
    rw [mem_inf_centralizer_iff] at hu ⊢
    obtain ⟨huH, hu⟩ := hu
    exact ⟨(hH₁ u).2 ⟨huH, hu a ha⟩, fun y hy => hu y (hH₁H y hy)⟩
  · rw [mem_inf_centralizer_iff]
    exact ⟨haH₁, hax⟩
  · intro b hb
    rw [mem_inf_centralizer_iff] at hb
    obtain ⟨hbH₁, hb⟩ := hb
    have hbH : b ∈ H := hH₁H b hbH₁
    by_cases hbZ : b ∈ H ⊓ centralizer (H : Set G)
    · refine Or.inr ⟨hbZ, fun h => haZ ?_⟩
      simpa using (H ⊓ centralizer (H : Set G)).mul_mem
        ((H ⊓ centralizer (H : Set G)).inv_mem hbZ) h
    · refine Or.inl ⟨?_, hbZ⟩
      have hy₀b : ¬ y₀ * b = b * y₀ := fun h =>
        hbZ (mem_inf_centralizer_iff.2 ⟨hbH, forall_mul_comm_of_cover hcov hb h⟩)
      obtain ⟨h1, -⟩ := commutator_eq_of_not_comm hzz hcomm hy₀ hbH hy₀b
      obtain ⟨h2, -⟩ := commutator_eq_of_not_comm hzz hcomm hy₀ ha (fun h => hne h.symm)
      have hw₀ : y₀ * (b * a) = (b * a) * y₀ := by
        rw [mul_comm_iff_commutator_eq_one, commutator_mul hzz hHz hcomm hy₀ hbH ha, h1, h2, hzz]
      refine mem_inf_centralizer_iff.2 ⟨H.mul_mem hbH ha, forall_mul_comm_of_cover hcov ?_ hw₀⟩
      intro y hy
      rw [← mul_assoc, hb y hy, mul_assoc, hax y hy, ← mul_assoc]

end Commutator

theorem card_sq_le_aux {z : G} (hzz : z * z = 1) :
    ∀ n : ℕ, ∀ H : Subgroup G, Nat.card H = n → (∀ y ∈ H, y * z = z * y) →
      (∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z) →
      ∀ A : Subgroup G, A ≤ H → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A ^ 2 ≤ 2 * Nat.card H * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H hn hHz hcomm A hAH hA
    by_cases hAZ : A ≤ H ⊓ centralizer (H : Set G)
    · have h1 : Nat.card A ≤ Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le hAZ
      have h2 : Nat.card A ≤ Nat.card H := Subgroup.card_le_of_le hAH
      calc Nat.card A ^ 2 = Nat.card A * Nat.card A := sq _
        _ ≤ Nat.card H * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) :=
          Nat.mul_le_mul h2 h1
        _ ≤ 2 * Nat.card H * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ (by omega)
    · obtain ⟨a, haA, haZ⟩ := IsConcreteLE.not_le_iff_exists.1 hAZ
      have haH : a ∈ H := hAH haA
      obtain ⟨y₀, hy₀, hne⟩ : ∃ y₀ ∈ H, ¬ a * y₀ = y₀ * a := by
        by_contra hcon
        refine haZ (mem_inf_centralizer_iff.2 ⟨haH, fun y hy => ?_⟩)
        by_contra h
        exact hcon ⟨y, hy, fun h' => h h'.symm⟩
      set H₁ : Subgroup G := H ⊓ centralizer ({a} : Set G) with hH₁def
      have hH₁ : ∀ x, x ∈ H₁ ↔ x ∈ H ∧ a * x = x * a := fun x =>
        mem_inf_centralizer_singleton_iff
      have hH₁H : H₁ ≤ H := inf_le_left
      have hcard := card_eq_two_mul_of_not_comm hzz hHz hcomm haH hy₀ hne hH₁
      have hcenter := card_center_eq_two_mul hzz hHz hcomm haH hy₀ hne hH₁
      have hpos : 0 < Nat.card H₁ := Nat.card_pos
      have hAH₁ : A ≤ H₁ := fun x hx => (hH₁ x).2 ⟨hAH hx, hA a haA x hx⟩
      have key := ih (Nat.card H₁) (by omega) H₁ rfl (fun y hy => hHz y (hH₁H hy))
        (fun a' ha' b hb => hcomm a' (hH₁H ha') b (hH₁H hb)) A hAH₁ hA
      calc Nat.card A ^ 2
          ≤ 2 * Nat.card H₁ * Nat.card (H₁ ⊓ centralizer (H₁ : Set G) : Subgroup G) := key
        _ = 2 * (2 * Nat.card H₁) * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) := by
          rw [hcenter]
          ring
        _ = 2 * Nat.card H * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) := by
          rw [hcard]

end NormHeis

theorem card_sq_le_of_commutators_mem_zpowers {z : G} (hzz : z * z = 1)
    (H : Subgroup G) (hHz : ∀ y ∈ H, y * z = z * y)
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ zpowers z)
    (A : Subgroup G) (hAH : A ≤ H) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ^ 2 ≤ 2 * Nat.card H * Nat.card (H ⊓ centralizer (H : Set G) : Subgroup G) :=
  NormHeis.card_sq_le_aux hzz _ H rfl hHz hcomm A hAH hA

end CFSG.EvenSporadicStandard.TwoB
