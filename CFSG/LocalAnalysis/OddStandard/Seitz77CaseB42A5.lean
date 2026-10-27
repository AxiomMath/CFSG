module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup Equiv Perm

abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

theorem a5_no_order_six : ∀ a c : A5, a * a = 1 → a ≠ 1 → c ^ 3 = 1 → c ≠ 1 → a * c ≠ c * a := by
  decide +kernel

namespace A5Klein

def v1 : A5 := ⟨swap 0 1 * swap 2 3, by rw [mem_alternatingGroup]; decide +kernel⟩

def v2 : A5 := ⟨swap 0 2 * swap 1 3, by rw [mem_alternatingGroup]; decide +kernel⟩

def v3 : A5 := ⟨swap 0 3 * swap 1 2, by rw [mem_alternatingGroup]; decide +kernel⟩

def r3 : A5 := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide +kernel⟩

theorem klein_mul : ∀ a b : A5, (a = 1 ∨ a = v1 ∨ a = v2 ∨ a = v3) →
    (b = 1 ∨ b = v1 ∨ b = v2 ∨ b = v3) → (a * b = 1 ∨ a * b = v1 ∨ a * b = v2 ∨ a * b = v3) := by
  decide +kernel

theorem klein_inv : ∀ a : A5, (a = 1 ∨ a = v1 ∨ a = v2 ∨ a = v3) →
    (a⁻¹ = 1 ∨ a⁻¹ = v1 ∨ a⁻¹ = v2 ∨ a⁻¹ = v3) := by
  decide +kernel

def klein : Subgroup A5 where
  carrier := {g | g = 1 ∨ g = v1 ∨ g = v2 ∨ g = v3}
  mul_mem' := fun {a b} ha hb => klein_mul a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := fun {a} ha => klein_inv a ha

instance : DecidablePred (· ∈ klein) :=
  fun x => inferInstanceAs (Decidable (x = 1 ∨ x = v1 ∨ x = v2 ∨ x = v3))

theorem r3_normalizes : ∀ h : A5, h ∈ klein ↔ r3 * h * r3⁻¹ ∈ klein := by
  decide +kernel

theorem r3_order : r3 ^ 3 = 1 ∧ r3 ≠ 1 := by
  decide +kernel

theorem klein_card : Nat.card klein = 4 := by
  have : Nat.card klein = Nat.card {g : A5 // g = 1 ∨ g = v1 ∨ g = v2 ∨ g = v3} := rfl
  rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_A5 : Nat.card A5 = 60 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

theorem klein_index : klein.index = 15 := by
  have h := klein.card_mul_index
  rw [klein_card, card_A5] at h
  omega

theorem klein_isPGroup : IsPGroup 2 klein :=
  IsPGroup.of_card (n := 2) (by rw [klein_card]; norm_num)

def kleinSylow : Sylow 2 A5 :=
  klein_isPGroup.toSylow (by rw [klein_index]; decide)

theorem r3_mem_normalizer : r3 ∈ normalizer ((kleinSylow : Subgroup A5) : Set A5) :=
  Subgroup.mem_normalizer_iff.mpr r3_normalizes

theorem r3_orderOf : orderOf r3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime r3_order.1 r3_order.2

end A5Klein

theorem a5_exists_order_three_normalizing (P : Sylow 2 A5) :
    ∃ c ∈ normalizer ((P : Subgroup A5) : Set A5), orderOf c = 3 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A5 A5Klein.kleinSylow P
  have hr : A5Klein.r3 • A5Klein.kleinSylow = A5Klein.kleinSylow :=
    Sylow.smul_eq_iff_mem_normalizer.mpr A5Klein.r3_mem_normalizer
  refine ⟨g * A5Klein.r3 * g⁻¹, ?_, ?_⟩
  · have h : (g * A5Klein.r3 * g⁻¹) • P = P := by
      rw [← hg, ← mul_smul, inv_mul_cancel_right, mul_smul, hr]
    exact Sylow.smul_eq_iff_mem_normalizer.mp h
  · have h := (MulAut.conj g).orderOf_eq A5Klein.r3
    rw [MulAut.conj_apply] at h
    rw [h, A5Klein.r3_orderOf]

theorem frattini_aux {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ] (P : Sylow p Γ)
    (Q : Subgroup Γ) (hPQ : (P : Subgroup Γ) ≤ Q) {y : Γ} (hy : y ∈ normalizer (Q : Set Γ)) :
    ∃ n ∈ normalizer ((P : Subgroup Γ) : Set Γ), ∃ q ∈ Q, n * q = y := by
  have hPH : (P : Subgroup Γ) ≤ normalizer (Q : Set Γ) := hPQ.trans Subgroup.le_normalizer
  have hPN : ((P.subtype hPH : Sylow p _) : Subgroup _) ≤
      Q.subgroupOf (normalizer (Q : Set Γ)) := by
    intro x hx
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hx
    exact hPQ hx
  have hfr := Sylow.normalizer_sup_eq_top' (P.subtype hPH) hPN
  have hy' : (⟨y, hy⟩ : normalizer (Q : Set Γ)) ∈ (⊤ : Subgroup (normalizer (Q : Set Γ))) :=
    trivial
  rw [← hfr, ← SetLike.mem_coe, Subgroup.mul_normal] at hy'
  obtain ⟨n, hn, q, hq, hnq⟩ := Set.mem_mul.mp hy'
  refine ⟨n.1, ?_, q.1, hq, congrArg Subtype.val hnq⟩
  have h1 : n ∈ normalizer (((P : Subgroup Γ).subgroupOf (normalizer (Q : Set Γ)) : Subgroup _)
      : Set _) := hn
  rw [← Subgroup.subgroupOf_normalizer_eq hPH] at h1
  exact h1

theorem exists_borel_elt {Γ : Type} [Group Γ] [Finite Γ] (π : Γ →* A5)
    (hπ : Function.Surjective π) (P : Sylow 2 Γ) :
    ∃ y ∈ normalizer ((P : Subgroup Γ) : Set Γ), Odd (orderOf y) ∧ orderOf (π y) = 3 := by
  obtain ⟨c, hc, hc3⟩ := a5_exists_order_three_normalizing (P.mapSurjective hπ)
  rw [Sylow.coe_mapSurjective] at hc
  obtain ⟨y₁, rfl⟩ := hπ c
  have hPQ : (P : Subgroup Γ) ≤ ((P : Subgroup Γ).map π).comap π := Subgroup.le_comap_map π _
  have hy₁ : y₁ ∈ normalizer ((((P : Subgroup Γ).map π).comap π : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcx := Subgroup.mem_normalizer_iff.mp hc (π x)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hcx
  obtain ⟨n, hn, q, hq, hnq⟩ := frattini_aux P _ hPQ hy₁
  obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hq)
  have hy₀ : n * a ∈ normalizer ((P : Subgroup Γ) : Set Γ) :=
    Subgroup.mul_mem _ hn (Subgroup.le_normalizer ha)
  have hπy₀ : π (n * a) = π y₁ := by rw [map_mul, haq, ← map_mul, hnq]
  obtain ⟨s, r, hr, hs⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n * a)).ne'
  refine ⟨(n * a) ^ (2 ^ s), Subgroup.pow_mem _ hy₀ _, ?_, ?_⟩
  · rw [orderOf_pow_of_dvd (by positivity) (hs ▸ dvd_mul_right _ _), hs,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hr
  · rw [map_pow, hπy₀,
      Nat.Coprime.orderOf_pow (by rw [hc3]; exact Nat.Coprime.pow_right _ (by norm_num))]
    exact hc3

end CFSG.OddStandard.Seitz77
