module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup

namespace OrdBr

theorem sq_mul_eq {Y : Type} [Group Y] (i x : Y) :
    (i * x) ^ 2 = (i * (x * i * x⁻¹)) * x ^ 2 := by
  simp only [pow_two, mul_assoc, inv_mul_cancel_left]

theorem mk_inj_of_mem {Y : Type} [Group Y] (I N : Subgroup Y) [N.Normal] (hIN : I ⊓ N = ⊥)
    {i j : Y} (hi : i ∈ I) (hj : j ∈ I) (h : (i : Y ⧸ N) = (j : Y ⧸ N)) : i = j := by
  have h1 : i⁻¹ * j ∈ N := QuotientGroup.eq.mp h
  have h2 : i⁻¹ * j ∈ I := I.mul_mem (I.inv_mem hi) hj
  have h3 : i⁻¹ * j ∈ I ⊓ N := ⟨h2, h1⟩
  rw [hIN, mem_bot] at h3
  exact inv_mul_eq_one.mp h3

theorem card_map_mk {Y : Type} [Group Y] (I N : Subgroup Y) [N.Normal] (hIN : I ⊓ N = ⊥) :
    Nat.card (I.map (QuotientGroup.mk' N)) = Nat.card I := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun i : I => (⟨QuotientGroup.mk' N i.1, i.1, i.2, rfl⟩ : I.map (QuotientGroup.mk' N)))
    ⟨fun a b hab => ?_, ?_⟩)).symm
  · exact Subtype.ext (mk_inj_of_mem I N hIN a.2 b.2 (congrArg Subtype.val hab))
  · rintro ⟨_, i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

end OrdBr

open OrdBr in
theorem sigma_count_abstract {Y : Type} [Group Y] [Finite Y] (I N : Subgroup Y) [I.Normal]
    [N.Normal] (x : Y) (hY : ∀ y : Y, ∃ i ∈ I, ∃ k : ℤ, y = i * x ^ k)
    (hN' : N = zpowers (x ^ 2)) (hIN : I ⊓ N = ⊥) (J : Subgroup (Y ⧸ N)) (hJ2 : J.index = 2)
    (hJ : ∀ H : Subgroup (Y ⧸ N), H.index = 2 → H = J) (s : ℕ)
    (hcount : Nat.card {y : Y ⧸ N // orderOf y = 2 ∧ y ∉ J} * (2 * s) = Nat.card (Y ⧸ N))
    (hcard : 2 * Nat.card I = Nat.card (Y ⧸ N)) :
    Nat.card {i : Y // i ∈ I ∧ i * (x * i * x⁻¹) = 1} * s = Nat.card I := by
  have hx2N : x ^ 2 ∈ N := by rw [hN']; exact mem_zpowers _
  have hmkx2 : (x : Y ⧸ N) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hx2N
  have hz : ∀ m : ℤ, (x : Y ⧸ N) ^ (2 * m) = 1 := by
    intro m
    have h2 : (x : Y ⧸ N) ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hmkx2
    rw [zpow_mul, h2, one_zpow]
  have hIJ : I.map (QuotientGroup.mk' N) = J := by
    apply hJ
    have h1 := card_map_mk I N hIN
    have h2 := Subgroup.index_mul_card (I.map (QuotientGroup.mk' N))
    have h3 : 0 < Nat.card I := Nat.card_pos
    rw [h1, ← hcard] at h2
    exact Nat.eq_of_mul_eq_mul_right h3 h2
  have hiJ : ∀ i ∈ I, (i : Y ⧸ N) ∈ J := by
    intro i hi
    rw [← hIJ]
    exact mem_map_of_mem (QuotientGroup.mk' N) hi
  have hxJ : (x : Y ⧸ N) ∉ J := by
    intro hxJ
    have htop : J = ⊤ := by
      rw [eq_top_iff]
      intro p _
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨i, hi, k, hg⟩ := hY g
      rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      exact J.mul_mem (hiJ i hi) (J.zpow_mem hxJ k)
    rw [htop, index_top] at hJ2
    exact absurd hJ2 (by norm_num)
  have hσ : ∀ i ∈ I, x * i * x⁻¹ ∈ I := fun i hi => Normal.conj_mem inferInstance i hi x
  have key : ∀ i ∈ I, ((i * x : Y) : Y ⧸ N) ^ 2 = 1 ↔ i * (x * i * x⁻¹) = 1 := by
    intro i hi
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, sq_mul_eq]
    constructor
    · intro h
      have h1 : i * (x * i * x⁻¹) ∈ N := by
        have := N.mul_mem h (N.inv_mem hx2N)
        rwa [mul_assoc, mul_inv_cancel, mul_one] at this
      have h3 : i * (x * i * x⁻¹) ∈ I ⊓ N := ⟨I.mul_mem hi (hσ i hi), h1⟩
      rw [hIN, mem_bot] at h3
      exact h3
    · intro h
      rw [h, one_mul]
      exact hx2N
  have hΦ : ∀ i : {i : Y // i ∈ I ∧ i * (x * i * x⁻¹) = 1},
      orderOf ((i.1 * x : Y) : Y ⧸ N) = 2 ∧ ((i.1 * x : Y) : Y ⧸ N) ∉ J := by
    rintro ⟨i, hi, hi1⟩
    have hnot : ((i * x : Y) : Y ⧸ N) ∉ J := by
      intro h
      apply hxJ
      have e : (x : Y ⧸ N) = ((i : Y ⧸ N))⁻¹ * ((i * x : Y) : Y ⧸ N) := by
        rw [QuotientGroup.mk_mul, inv_mul_cancel_left]
      rw [e]
      exact J.mul_mem (J.inv_mem (hiJ i hi)) h
    refine ⟨orderOf_eq_prime ((key i hi).mpr hi1) ?_, hnot⟩
    intro h1
    exact hnot (h1 ▸ J.one_mem)
  let Φ : {i : Y // i ∈ I ∧ i * (x * i * x⁻¹) = 1} → {y : Y ⧸ N // orderOf y = 2 ∧ y ∉ J} :=
    fun i => ⟨((i.1 * x : Y) : Y ⧸ N), hΦ i⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨i, hi, _⟩ ⟨j, hj, _⟩ h
    have h' : ((i * x : Y) : Y ⧸ N) = ((j * x : Y) : Y ⧸ N) := congrArg Subtype.val h
    have h1 : (i * x)⁻¹ * (j * x) ∈ N := QuotientGroup.eq.mp h'
    have h2 : i⁻¹ * j ∈ N := by
      have h4 := Normal.conj_mem inferInstance _ h1 x
      have e : x * ((i * x)⁻¹ * (j * x)) * x⁻¹ = i⁻¹ * j := by group
      rwa [e] at h4
    have h3 : i⁻¹ * j ∈ I ⊓ N := ⟨I.mul_mem (I.inv_mem hi) hj, h2⟩
    rw [hIN, mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hsurj : Function.Surjective Φ := by
    rintro ⟨y, hy2, hyJ⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨i, hi, k, hg⟩ := hY g
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    ·
      exfalso
      apply hyJ
      rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hz, mul_one]
      exact hiJ i hi
    ·
      have hyeq : ((g : Y) : Y ⧸ N) = ((i * x : Y) : Y ⧸ N) := by
        rw [hg, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, zpow_add_one, hz, one_mul,
          QuotientGroup.mk_mul]
      have hsq : ((i * x : Y) : Y ⧸ N) ^ 2 = 1 := by
        rw [← hyeq]
        have h := pow_orderOf_eq_one ((g : Y) : Y ⧸ N)
        rwa [hy2] at h
      exact ⟨⟨i, hi, (key i hi).mp hsq⟩, Subtype.ext hyeq.symm⟩
  have hcardeq : Nat.card {i : Y // i ∈ I ∧ i * (x * i * x⁻¹) = 1} =
      Nat.card {y : Y ⧸ N // orderOf y = 2 ∧ y ∉ J} :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)
  rw [hcardeq]
  have h2 : 2 * (Nat.card {y : Y ⧸ N // orderOf y = 2 ∧ y ∉ J} * s) = 2 * Nat.card I := by
    rw [hcard, ← hcount]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

end CFSG.GH74.GLS.SP.Local
