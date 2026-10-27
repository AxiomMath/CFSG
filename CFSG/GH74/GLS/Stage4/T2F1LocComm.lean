module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup

section Abstract

variable {Q : Type*} [Group Q] {c w₁ w₂ : Q}

private theorem klein_sq (hw₁ : w₁ * w₁ = 1) (hw₂ : w₂ * w₂ = 1) (hcomm : w₁ * w₂ = w₂ * w₁) {v : Q}
    (hv : v ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q)) : v * v = 1 := by
  rcases hv with rfl | rfl | rfl | rfl
  · simp
  · exact hw₁
  · exact hw₂
  · calc w₁ * w₂ * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [hcomm]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁, hw₂, one_mul]

private theorem klein_mul (hw₁ : w₁ * w₁ = 1) (hw₂ : w₂ * w₂ = 1) (hcomm : w₁ * w₂ = w₂ * w₁)
    {u v : Q} (hu : u ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q)) (hv : v ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q)) :
    u * v ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q) := by
  have e₁₂ : w₁ * (w₁ * w₂) = w₂ := by rw [← mul_assoc, hw₁, one_mul]
  have e₂₁ : w₂ * (w₁ * w₂) = w₁ := by rw [hcomm, ← mul_assoc, hw₂, one_mul]
  have e₃₁ : w₁ * w₂ * w₁ = w₂ := by rw [hcomm, mul_assoc, hw₁, mul_one]
  have e₃₂ : w₁ * w₂ * w₂ = w₁ := by rw [mul_assoc, hw₂, mul_one]
  have e₃₃ : w₁ * w₂ * (w₁ * w₂) = 1 := klein_sq hw₁ hw₂ hcomm (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv ⊢
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;>
    simp [hw₁, hw₂, hcomm.symm, e₁₂, e₂₁, e₃₁, e₃₂, e₃₃]

private theorem klein_conj (hw₁c : w₁ * c * w₁⁻¹ = c⁻¹) (hw₂c : w₂ * c * w₂⁻¹ = c⁻¹) {v : Q}
    (hv : v ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q)) {z : Q} (hz : z ∈ zpowers c) :
    v * z * v⁻¹ ∈ zpowers c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have h : v * c * v⁻¹ ∈ zpowers c := by
    rcases hv with rfl | rfl | rfl | rfl
    · simp [mem_zpowers]
    · rw [hw₁c]; exact inv_mem (mem_zpowers c)
    · rw [hw₂c]; exact inv_mem (mem_zpowers c)
    · have : w₁ * w₂ * c * (w₁ * w₂)⁻¹ = c := by
        calc w₁ * w₂ * c * (w₁ * w₂)⁻¹ = w₁ * (w₂ * c * w₂⁻¹) * w₁⁻¹ := by group
          _ = w₁ * c⁻¹ * w₁⁻¹ := by rw [hw₂c]
          _ = (w₁ * c * w₁⁻¹)⁻¹ := by group
          _ = c := by rw [hw₁c, inv_inv]
      rw [this]; exact mem_zpowers c
  have := zpow_mem h k
  rwa [conj_zpow] at this

private theorem exists_mul_of_mem_closure (hw₁ : w₁ * w₁ = 1) (hw₂ : w₂ * w₂ = 1)
    (hcomm : w₁ * w₂ = w₂ * w₁) (hw₁c : w₁ * c * w₁⁻¹ = c⁻¹) (hw₂c : w₂ * c * w₂⁻¹ = c⁻¹)
    {x : Q} (hx : x ∈ closure ({c, w₁, w₂} : Set Q)) :
    ∃ z ∈ zpowers c, ∃ v ∈ ({1, w₁, w₂, w₁ * w₂} : Set Q), x = z * v := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨x, mem_zpowers x, 1, by simp, by simp⟩
    · exact ⟨1, one_mem _, x, by simp, by simp⟩
    · exact ⟨1, one_mem _, x, by simp, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨z, hz, v, hv, rfl⟩ := hx
    obtain ⟨z', hz', v', hv', rfl⟩ := hy
    refine ⟨z * (v * z' * v⁻¹), mul_mem hz (klein_conj hw₁c hw₂c hv hz'), v * v',
      klein_mul hw₁ hw₂ hcomm hv hv', by group⟩
  | inv x _ hx =>
    obtain ⟨z, hz, v, hv, rfl⟩ := hx
    have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (klein_sq hw₁ hw₂ hcomm hv)
    refine ⟨v * z⁻¹ * v⁻¹, klein_conj hw₁c hw₂c hv (inv_mem hz), v, hv, ?_⟩
    calc (z * v)⁻¹ = v⁻¹ * z⁻¹ := mul_inv_rev _ _
      _ = v * z⁻¹ := by rw [hvv]
      _ = v * z⁻¹ * v⁻¹ * v := by group

private theorem sq_mem_zpowers (hw₁ : w₁ * w₁ = 1) (hw₂ : w₂ * w₂ = 1)
    (hcomm : w₁ * w₂ = w₂ * w₁) (hw₁c : w₁ * c * w₁⁻¹ = c⁻¹) (hw₂c : w₂ * c * w₂⁻¹ = c⁻¹)
    {x : Q} (hx : x ∈ closure ({c, w₁, w₂} : Set Q)) : ∃ i : ℤ, x * x = c ^ i := by
  obtain ⟨z, hz, v, hv, rfl⟩ := exists_mul_of_mem_closure hw₁ hw₂ hcomm hw₁c hw₂c hx
  have h : z * v * (z * v) = z * (v * z * v⁻¹) * (v * v) := by group
  rw [klein_sq hw₁ hw₂ hcomm hv, mul_one] at h
  have hmem : z * v * (z * v) ∈ zpowers c := by
    rw [h]; exact mul_mem hz (klein_conj hw₁c hw₂c hv hz)
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
  exact ⟨i, hi.symm⟩

private theorem zpow_mod_three (hc3 : c ^ 3 = 1) (n : ℤ) : c ^ n = c ^ (n % 3) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv n 3]
  have h3 : c ^ (3 : ℤ) = 1 := by exact_mod_cast hc3
  rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]

private theorem comm_of_relations (hc3 : c ^ 3 = 1) (hw₁ : w₁ * w₁ = 1) (hw₂ : w₂ * w₂ = 1)
    (hcomm : w₁ * w₂ = w₂ * w₁) (hw₁c : w₁ * c * w₁⁻¹ = c⁻¹) (hw₂c : w₂ * c * w₂⁻¹ = c⁻¹)
    {f : Q} {r : ℕ} (hfr : f ^ r = 1) (hr : Odd r)
    (hx : f * c * f⁻¹ ∈ closure ({c, w₁, w₂} : Set Q)) : f * c * f⁻¹ = c := by
  obtain ⟨i, hi⟩ := sq_mem_zpowers hw₁ hw₂ hcomm hw₁c hw₂c hx
  have hx3 : f * c * f⁻¹ * (f * c * f⁻¹ * (f * c * f⁻¹)) = 1 := by
    rw [← pow_three, conj_pow, hc3]; group
  obtain ⟨j, hfc⟩ : ∃ j : ℤ, f * c * f⁻¹ = c ^ j :=
    ⟨-i, by rw [zpow_neg, ← hi]; exact eq_inv_of_mul_eq_one_left hx3⟩
  have hff : f * f * c * (f * f)⁻¹ = c ^ (j * j) := by
    calc f * f * c * (f * f)⁻¹ = f * (f * c * f⁻¹) * f⁻¹ := by group
      _ = f * c ^ j * f⁻¹ := by rw [hfc]
      _ = (f * c * f⁻¹) ^ j := (conj_zpow).symm
      _ = (c ^ j) ^ j := by rw [hfc]
      _ = c ^ (j * j) := (zpow_mul c j j).symm
  have hsq : (j * j) % 3 = 0 ∨ (j * j) % 3 = 1 := by
    have h3 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases h3 with h | h | h <;> simp [Int.mul_emod, h]
  rcases hsq with h0 | h1
  · have h1 : c ^ (j * j) = 1 := by rw [zpow_mod_three hc3, h0]; simp
    rw [h1, mul_inv_eq_one] at hff
    have hc : c = 1 := by simpa using hff
    subst hc
    simp
  · have h1' : c ^ (j * j) = c := by rw [zpow_mod_three hc3, h1]; simp
    rw [h1', mul_inv_eq_iff_eq_mul] at hff
    obtain ⟨m, rfl⟩ := hr
    have hf : f = (f * f) ^ (m + 1) := by
      calc f = f * f ^ (2 * m + 1) := by rw [hfr, mul_one]
        _ = (f * f) ^ (m + 1) := by rw [← pow_succ', ← sq, ← pow_mul]; ring_nf
    have hcf : Commute f c := by
      rw [hf]
      exact (Commute.pow_left (show Commute (f * f) c from hff) (m + 1))
    exact hcf.mul_inv_cancel

end Abstract

section Quotient

variable {G : Type} [Group G]

private abbrev normH (H : Subgroup G) : Subgroup G := normalizer (H : Set G)

private abbrev quoH (H : Subgroup G) : Type := ↥(normH H) ⧸ H.subgroupOf (normH H)

private def projH (H : Subgroup G) : normH H →* quoH H := QuotientGroup.mk' (H.subgroupOf (normH H))

private theorem projH_eq_projH_iff {H : Subgroup G} (x y : normH H) :
    projH H x = projH H y ↔ (x : G)⁻¹ * y ∈ H := by
  unfold projH
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  rfl

private theorem projH_eq_one_iff {H : Subgroup G} (x : normH H) : projH H x = 1 ↔ (x : G) ∈ H := by
  unfold projH
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

private theorem mem_normH_of_pow_mem {H : Subgroup G} {g : G} {n : ℕ} (hn : 0 < n)
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hgn : g ^ n ∈ H) : g ∈ normH H := by
  have hk : ∀ k : ℕ, ∀ y ∈ H, g ^ k * y * (g ^ k)⁻¹ ∈ H := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have := hg _ (ih y hy)
      convert this using 1
      group
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hg x, fun hx => ?_⟩
  have h1 : (g ^ (m + 1))⁻¹ * (g * x * g⁻¹) * g ^ (m + 1) ∈ H :=
    mul_mem (mul_mem (inv_mem hgn) hx) hgn
  have h2 := hk m _ h1
  convert h2 using 1
  group

end Quotient

theorem comm_a_mod_H {G : Type} [Group G] {H : Subgroup G} {a w₁ w₂ f : G} {r : ℕ}
    (haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H) (ha3 : a ^ 3 ∈ H)
    (hw₁H : ∀ x ∈ H, w₁ * x * w₁⁻¹ ∈ H) (hw₂H : ∀ x ∈ H, w₂ * x * w₂⁻¹ ∈ H)
    (hw₁sq : w₁ * w₁ ∈ H) (hw₂sq : w₂ * w₂ ∈ H) (hw₁w₂ : w₁ * w₂ = w₂ * w₁)
    (hw₁a : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) (hw₂a : ∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h)
    (hfH : ∀ x ∈ H, f * x * f⁻¹ ∈ H) (hfr : f ^ r = 1) (hr : Odd r)
    (hfaN : f * a * f⁻¹ ∈ Subgroup.closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a})) :
    ∃ h ∈ H, f * a * f⁻¹ = a * h := by
  have ha : a ∈ normH H := mem_normH_of_pow_mem (n := 3) (by omega) haH ha3
  have hw₁n : w₁ ∈ normH H := mem_normH_of_pow_mem (n := 2) (by omega) hw₁H (by rwa [sq])
  have hw₂n : w₂ ∈ normH H := mem_normH_of_pow_mem (n := 2) (by omega) hw₂H (by rwa [sq])
  have hfn : f ∈ normH H :=
    mem_normH_of_pow_mem (n := r) (by obtain ⟨m, hm⟩ := hr; omega) hfH (by rw [hfr]; exact one_mem _)
  have hyn : a⁻¹ * w₂ * a ∈ normH H := mul_mem (mul_mem (inv_mem ha) hw₂n) ha
  have hle : closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a}) ≤ normH H := by
    rw [closure_le]
    rintro x (hx | hx | hx)
    · exact le_normalizer hx
    · rw [hx]; exact hw₁n
    · rw [Set.mem_singleton_iff.1 hx]; exact hyn
  have key : ∀ x (hx : x ∈ closure ((H : Set G) ∪ {w₁, a⁻¹ * w₂ * a})),
      projH H ⟨x, hle hx⟩ ∈
        closure ({projH H ⟨a, ha⟩, projH H ⟨w₁, hw₁n⟩, projH H ⟨w₂, hw₂n⟩} : Set (quoH H)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx | hx
      · have : projH H ⟨x, hle (subset_closure (Or.inl hx))⟩ = 1 := (projH_eq_one_iff _).2 hx
        rw [this]; exact one_mem _
      · have : (⟨x, hle (subset_closure (Or.inr (Or.inl hx)))⟩ : normH H) = ⟨w₁, hw₁n⟩ :=
          Subtype.ext hx
        rw [this]; exact subset_closure (by simp)
      · have : (⟨x, hle (subset_closure (Or.inr (Or.inr hx)))⟩ : normH H) =
            ⟨a, ha⟩⁻¹ * ⟨w₂, hw₂n⟩ * ⟨a, ha⟩ := Subtype.ext (Set.mem_singleton_iff.1 hx)
        rw [this, map_mul, map_mul, map_inv]
        exact mul_mem (mul_mem (inv_mem (subset_closure (by simp))) (subset_closure (by simp)))
          (subset_closure (by simp))
    | one =>
      have : (⟨1, hle (one_mem _)⟩ : normH H) = 1 := rfl
      rw [this, map_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      have : (⟨x * y, hle (mul_mem hx hy)⟩ : normH H) = ⟨x, hle hx⟩ * ⟨y, hle hy⟩ := rfl
      rw [this, map_mul]; exact mul_mem ihx ihy
    | inv x hx ih =>
      have : (⟨x⁻¹, hle (inv_mem hx)⟩ : normH H) = (⟨x, hle hx⟩)⁻¹ := rfl
      rw [this, map_inv]; exact inv_mem ih
  obtain ⟨h₁, hh₁, h₁eq⟩ := hw₁a
  obtain ⟨h₂, hh₂, h₂eq⟩ := hw₂a
  have R1 : projH H ⟨a, ha⟩ ^ 3 = 1 := by rw [← map_pow, projH_eq_one_iff]; exact ha3
  have R2 : projH H ⟨w₁, hw₁n⟩ * projH H ⟨w₁, hw₁n⟩ = 1 := by
    rw [← map_mul, projH_eq_one_iff]; exact hw₁sq
  have R3 : projH H ⟨w₂, hw₂n⟩ * projH H ⟨w₂, hw₂n⟩ = 1 := by
    rw [← map_mul, projH_eq_one_iff]; exact hw₂sq
  have R4 : projH H ⟨w₁, hw₁n⟩ * projH H ⟨w₂, hw₂n⟩ = projH H ⟨w₂, hw₂n⟩ * projH H ⟨w₁, hw₁n⟩ := by
    rw [← map_mul, ← map_mul]; exact congrArg _ (Subtype.ext hw₁w₂)
  have R5 : projH H ⟨w₁, hw₁n⟩ * projH H ⟨a, ha⟩ * (projH H ⟨w₁, hw₁n⟩)⁻¹ =
      (projH H ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, projH_eq_projH_iff]
    show (w₁ * a * w₁⁻¹)⁻¹ * a⁻¹ ∈ H
    have : (w₁ * a * w₁⁻¹)⁻¹ * a⁻¹ = h₁⁻¹ := by rw [h₁eq]; group
    rw [this]; exact inv_mem hh₁
  have R6 : projH H ⟨w₂, hw₂n⟩ * projH H ⟨a, ha⟩ * (projH H ⟨w₂, hw₂n⟩)⁻¹ =
      (projH H ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, projH_eq_projH_iff]
    show (w₂ * a * w₂⁻¹)⁻¹ * a⁻¹ ∈ H
    have : (w₂ * a * w₂⁻¹)⁻¹ * a⁻¹ = h₂⁻¹ := by rw [h₂eq]; group
    rw [this]; exact inv_mem hh₂
  have R7 : projH H ⟨f, hfn⟩ ^ r = 1 := by
    rw [← map_pow, projH_eq_one_iff]; show f ^ r ∈ H; rw [hfr]; exact one_mem _
  have hmem : projH H ⟨f, hfn⟩ * projH H ⟨a, ha⟩ * (projH H ⟨f, hfn⟩)⁻¹ ∈
      closure ({projH H ⟨a, ha⟩, projH H ⟨w₁, hw₁n⟩, projH H ⟨w₂, hw₂n⟩} : Set (quoH H)) := by
    have := key _ hfaN
    have e : (⟨f * a * f⁻¹, hle hfaN⟩ : normH H) = ⟨f, hfn⟩ * ⟨a, ha⟩ * ⟨f, hfn⟩⁻¹ := rfl
    rwa [e, map_mul, map_mul, map_inv] at this
  have hfin := comm_of_relations R1 R2 R3 R4 R5 R6 R7 hr hmem
  have e2 : projH H ⟨a, ha⟩ = projH H ⟨f * a * f⁻¹, hle hfaN⟩ := by
    rw [← hfin, ← map_inv, ← map_mul, ← map_mul]; rfl
  rw [projH_eq_projH_iff] at e2
  exact ⟨a⁻¹ * (f * a * f⁻¹), e2, by group⟩

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
