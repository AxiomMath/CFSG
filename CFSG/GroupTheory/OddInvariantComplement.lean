module

public import CFSG.GroupTheory.SupCommute
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_complement_of_odd {J T F L : Subgroup G} (hTcard : Nat.card T = 2)
    (hdisj : T ⊓ F = ⊥) (hsup : T ⊔ F = J) (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hL : Odd (Nat.card L)) (hLJ : ∀ ℓ ∈ L, ∀ j ∈ J, ℓ * j * ℓ⁻¹ ∈ J)
    (hLT : ∀ ℓ ∈ L, ∀ t ∈ T, ℓ * t * ℓ⁻¹ = t) :
    ∃ F' : Subgroup G, F' ≤ J ∧ T ⊓ F' = ⊥ ∧ T ⊔ F' = J ∧
      ∀ ℓ ∈ L, ∀ f ∈ F', ℓ * f * ℓ⁻¹ ∈ F' := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hTcard
  set z₁ : G := (y : G) with hz₁def
  have hz₁T : z₁ ∈ T := y.2
  have hz₁1 : z₁ ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hTcases : ∀ t ∈ T, t = 1 ∨ t = z₁ := by
    intro t ht
    by_cases h1 : t = 1
    · exact Or.inl h1
    · exact Or.inr (congrArg Subtype.val (hyu ⟨t, ht⟩ (fun h => h1 (congrArg Subtype.val h))))
  have hz₁sq : z₁ * z₁ = 1 := by
    rcases hTcases (z₁ * z₁) (T.mul_mem hz₁T hz₁T) with h | h
    · exact h
    · exact absurd (mul_eq_right.mp h) hz₁1
  have hTcomm : ∀ t ∈ T, ∀ t' ∈ T, Commute t t' := by
    intro t ht t' ht'
    rcases hTcases t ht with rfl | rfl
    · exact Commute.one_left _
    · rcases hTcases t' ht' with rfl | rfl
      · exact Commute.one_right _
      · exact Commute.refl _
  have hTJ : T ≤ J := hsup ▸ le_sup_left
  have hFJ : F ≤ J := hsup ▸ le_sup_right
  have hmemF : ∀ t ∈ T, ∀ f ∈ F, (t * f ∈ F ↔ t = 1) := by
    intro t ht f hf
    constructor
    · intro h
      have h1 : t ∈ T ⊓ F := ⟨ht, by simpa using F.mul_mem h (F.inv_mem hf)⟩
      rw [hdisj] at h1
      exact h1
    · rintro rfl
      simpa using hf
  let φ₀ : G → ZMod 2 := fun j => if j ∈ F then 0 else 1
  have hφ₀add : ∀ j ∈ J, ∀ j' ∈ J, φ₀ (j * j') = φ₀ j + φ₀ j' := by
    intro j hj j' hj'
    rw [← hsup] at hj hj'
    obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hj
    obtain ⟨t', ht', f', hf', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hj'
    have hprod : t * f * (t' * f') = (t * t') * (f * f') := by
      calc t * f * (t' * f') = t * (f * t') * f' := by group
        _ = t * (t' * f) * f' := by rw [(hcomm t' ht' f hf).symm.eq]
        _ = (t * t') * (f * f') := by group
    have hF1 : φ₀ (t * f) = if t = 1 then 0 else 1 := by
      by_cases h : t = 1
      · simp only [φ₀, h, one_mul, hf, if_pos]
      · simp only [φ₀, h, (hmemF t ht f hf).not.mpr h, if_neg, not_false_eq_true]
    have hF2 : φ₀ (t' * f') = if t' = 1 then 0 else 1 := by
      by_cases h : t' = 1
      · simp only [φ₀, h, one_mul, hf', if_pos]
      · simp only [φ₀, h, (hmemF t' ht' f' hf').not.mpr h, if_neg, not_false_eq_true]
    have hF3 : φ₀ ((t * t') * (f * f')) = if t * t' = 1 then 0 else 1 := by
      have htt' : t * t' ∈ T := T.mul_mem ht ht'
      have hff' : f * f' ∈ F := F.mul_mem hf hf'
      by_cases h : t * t' = 1
      · simp only [φ₀, h, one_mul, hff', if_pos]
      · simp only [φ₀, h, (hmemF _ htt' _ hff').not.mpr h, if_neg, not_false_eq_true]
    rw [hprod, hF3, hF1, hF2]
    rcases hTcases t ht with rfl | rfl <;> rcases hTcases t' ht' with rfl | rfl
    · simp
    · simp [hz₁1]
    · simp [hz₁1]
    · simp [hz₁sq, hz₁1]
      decide
  let φbar : G → ZMod 2 := fun j => ∑ ℓ : L, φ₀ ((ℓ : G)⁻¹ * j * (ℓ : G))
  have hφbaradd : ∀ j ∈ J, ∀ j' ∈ J, φbar (j * j') = φbar j + φbar j' := by
    intro j hj j' hj'
    simp only [φbar]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hℓJ : ∀ x ∈ J, (ℓ : G)⁻¹ * x * (ℓ : G) ∈ J := by
      intro x hx
      simpa using hLJ ((ℓ : G)⁻¹) (L.inv_mem ℓ.2) x hx
    have e : (ℓ : G)⁻¹ * (j * j') * (ℓ : G) =
        ((ℓ : G)⁻¹ * j * (ℓ : G)) * ((ℓ : G)⁻¹ * j' * (ℓ : G)) := by group
    rw [e]
    exact hφ₀add _ (hℓJ j hj) _ (hℓJ j' hj')
  have hφbarinv : ∀ ℓ₀ ∈ L, ∀ j : G, φbar (ℓ₀ * j * ℓ₀⁻¹) = φbar j := by
    intro ℓ₀ hℓ₀ j
    simp only [φbar]
    let m : L := ⟨ℓ₀, hℓ₀⟩
    rw [← Equiv.sum_comp (Equiv.mulLeft m⁻¹) (fun ℓ : L => φ₀ ((ℓ : G)⁻¹ * j * (ℓ : G)))]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    congr 1
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, m]
    group
  have hφbarz₁ : φbar z₁ = 1 := by
    simp only [φbar]
    have hfix : ∀ ℓ : L, (ℓ : G)⁻¹ * z₁ * (ℓ : G) = z₁ := by
      intro ℓ
      simpa using hLT ((ℓ : G)⁻¹) (L.inv_mem ℓ.2) z₁ hz₁T
    have hz₁F : z₁ ∉ F := by
      intro h
      have : z₁ ∈ T ⊓ F := ⟨hz₁T, h⟩
      rw [hdisj] at this
      exact hz₁1 this
    simp only [hfix]
    simp only [φ₀, hz₁F, if_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    obtain ⟨k, hk⟩ := hL
    rw [Nat.card_eq_fintype_card] at hk
    rw [hk]
    push_cast
    rw [mul_comm]
    simp [CharTwo.two_eq_zero]
  have hφbar_one : φbar 1 = 0 := by
    have h1 := hφbaradd 1 J.one_mem 1 J.one_mem
    rw [one_mul] at h1
    have h2 : φbar 1 + φbar 1 = 0 := CharTwo.add_self_eq_zero _
    calc φbar 1 = φbar 1 + φbar 1 := h1
      _ = 0 := h2
  let F' : Subgroup G :=
    { carrier := {j | j ∈ J ∧ φbar j = 0}
      one_mem' := ⟨J.one_mem, hφbar_one⟩
      mul_mem' := by
        rintro a b ⟨haJ, ha⟩ ⟨hbJ, hb⟩
        exact ⟨J.mul_mem haJ hbJ, by rw [hφbaradd a haJ b hbJ, ha, hb, add_zero]⟩
      inv_mem' := by
        rintro a ⟨haJ, ha⟩
        refine ⟨J.inv_mem haJ, ?_⟩
        have h1 := hφbaradd a haJ a⁻¹ (J.inv_mem haJ)
        rw [mul_inv_cancel, hφbar_one, ha, zero_add] at h1
        exact h1.symm }
  have hmemF' : ∀ j, j ∈ F' ↔ j ∈ J ∧ φbar j = 0 := fun j => Iff.rfl
  refine ⟨F', fun j hj => hj.1, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    rcases hTcases t ht.1 with h | h
    · exact h
    · exfalso
      have h1 := ((hmemF' t).mp ht.2).2
      rw [h, hφbarz₁] at h1
      exact one_ne_zero h1
  · refine le_antisymm (sup_le hTJ (fun j hj => hj.1)) fun j hj => ?_
    by_cases h0 : φbar j = 0
    · exact (le_sup_right : F' ≤ T ⊔ F') ((hmemF' j).mpr ⟨hj, h0⟩)
    · have h1 : φbar j = 1 := by
        rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (φbar j) with h | h
        · exact absurd h h0
        · exact h
      have hmem : z₁ * j ∈ F' := by
        refine (hmemF' _).mpr ⟨J.mul_mem (hTJ hz₁T) hj, ?_⟩
        rw [hφbaradd z₁ (hTJ hz₁T) j hj, hφbarz₁, h1]
        decide
      have e : j = z₁ * (z₁ * j) := by
        rw [← mul_assoc, hz₁sq, one_mul]
      rw [e]
      exact Subgroup.mul_mem_sup hz₁T hmem
  · intro ℓ hℓ f hf
    refine (hmemF' _).mpr ⟨hLJ ℓ hℓ f ((hmemF' f).mp hf).1, ?_⟩
    rw [hφbarinv ℓ hℓ f]
    exact ((hmemF' f).mp hf).2

end CFSG.GroupTheory
