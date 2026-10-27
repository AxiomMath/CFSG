module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Equiv

theorem orderOf_ne_nine_of_cover_isConj_inv {A : Type*} [Group A]
    (hZ : Nat.card (Subgroup.center A) = 3) {X : Type*} [Group X]
    (e : A ⧸ Subgroup.center A ≃* X) (hX : ∀ x : X, orderOf x = 3 → IsConj x x⁻¹)
    (hX9 : ∀ x : X, orderOf x ≠ 9) (g : A) : orderOf g ≠ 9 := by
  intro hg
  set Z := Subgroup.center A with hZdef
  have hZcube : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have h := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ] at h
    have h' : orderOf z = 1 ∨ orderOf z = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 h with h | h <;> simp [h]
    rcases h' with h' | h'
    · rw [orderOf_eq_one_iff.1 h']; simp
    · rw [← h']; exact pow_orderOf_eq_one z
  have hg9 : g ^ 9 = 1 := hg ▸ pow_orderOf_eq_one g
  have hgZ : g ∉ Z := fun h => by
    have h3 := hZcube g h
    have : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [hg] at this
    omega
  set gb : A ⧸ Z := QuotientGroup.mk g with hgb
  have hgb1 : gb ≠ 1 := fun h => hgZ ((QuotientGroup.eq_one_iff g).1 h)
  have hdvd : orderOf gb ∣ 9 :=
    orderOf_dvd_of_pow_eq_one (by rw [hgb, ← QuotientGroup.mk_pow, hg9]; rfl)
  have hne9 : orderOf gb ≠ 9 := by
    rw [← orderOf_injective e.toMonoidHom e.injective gb]
    exact hX9 _
  have hne1 : orderOf gb ≠ 1 := fun h => hgb1 (orderOf_eq_one_iff.1 h)
  have h3 : orderOf gb = 3 := by
    have hle : orderOf gb ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf gb := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    interval_cases h : orderOf gb <;> omega
  have hgZ3 : g ^ 3 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hgb, ← h3]
    exact pow_orderOf_eq_one gb
  have hconj : IsConj gb gb⁻¹ := by
    have h' : IsConj (e gb) (e gb)⁻¹ := hX (e gb)
      ((orderOf_injective e.toMonoidHom e.injective gb).trans h3)
    obtain ⟨c, hc⟩ := isConj_iff.1 h'
    refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
    simpa using hc
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  have hmk : (QuotientGroup.mk (t * g * t⁻¹) : A ⧸ Z) = QuotientGroup.mk g⁻¹ := by
    simpa [hgb] using hc
  have hz := QuotientGroup.eq.1 hmk
  set z : A := (t * g * t⁻¹)⁻¹ * g⁻¹ with hzdef
  have hzc : z ∈ Z := hz
  have hform : t * g * t⁻¹ = g⁻¹ * z⁻¹ := by
    rw [hzdef]; group
  have hcomm : Commute g⁻¹ z⁻¹ := by
    have := Subgroup.mem_center_iff.1 (Z.inv_mem hzc) g⁻¹
    exact this
  have hz3 : (z⁻¹) ^ 3 = 1 := hZcube _ (Z.inv_mem hzc)
  have hcube : (t * g * t⁻¹) ^ 3 = g⁻¹ ^ 3 := by
    rw [hform, hcomm.mul_pow, hz3, mul_one]
  have hcentral : t * g ^ 3 * t⁻¹ = g ^ 3 := by
    have := Subgroup.mem_center_iff.1 hgZ3 t
    rw [this]; group
  have : g ^ 3 = g⁻¹ ^ 3 := by
    rw [← hcube, conj_pow, hcentral]
  have h6 : g ^ 6 = 1 := by
    have h' : g ^ 3 * g ^ 3 = 1 := by
      nth_rewrite 2 [this]
      rw [inv_pow]; exact mul_inv_cancel _
    rwa [← pow_add] at h'
  have : orderOf g ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  rw [hg] at this
  omega

private lemma perm_six_cube_inv :
    ∀ x : Perm (Fin 6), x ^ 3 = 1 → Perm.sign x = 1 →
      ∃ y : Perm (Fin 6), Perm.sign y = 1 ∧ y * x * y⁻¹ = x⁻¹ := by
  decide +kernel

private lemma perm_six_nine :
    ∀ x : Perm (Fin 6), x ^ 9 = 1 → x ^ 3 = 1 := by
  decide +kernel

theorem isConj_inv_of_orderOf_three_alt_six (x : alternatingGroup (Fin 6)) (hx : orderOf x = 3) :
    IsConj x x⁻¹ := by
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have h3 : (x : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  obtain ⟨y, hys, hy⟩ := perm_six_cube_inv x (by exact h3) (Perm.mem_alternatingGroup.1 x.2)
  refine isConj_iff.2 ⟨⟨y, by simpa [Perm.mem_alternatingGroup] using hys⟩, ?_⟩
  apply Subtype.ext
  simpa using hy

theorem orderOf_ne_nine_alt_six (x : alternatingGroup (Fin 6)) : orderOf x ≠ 9 := by
  intro h
  have h9 : x ^ 9 = 1 := h ▸ pow_orderOf_eq_one x
  have h9' : (x : Perm (Fin 6)) ^ 9 = 1 := by
    have := congrArg Subtype.val h9
    simpa using this
  have h3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa using perm_six_nine x h9'
  have : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [h] at this
  omega

theorem orderOf_ne_nine_tripleA6 {A : Type*} [Group A] (hZ : Nat.card (Subgroup.center A) = 3)
    (e : A ⧸ Subgroup.center A ≃* alternatingGroup (Fin 6)) (g : A) : orderOf g ≠ 9 :=
  orderOf_ne_nine_of_cover_isConj_inv hZ e isConj_inv_of_orderOf_three_alt_six
    orderOf_ne_nine_alt_six g

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
