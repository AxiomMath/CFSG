module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm

open Equiv Subgroup Finset

theorem card_modEq_card_inf_centralizer {G : Type*} [Group G] [Finite G] {p n : ℕ}
    [Fact p.Prime] {y : G} (hy : y ^ p ^ n = 1) {R : Subgroup G}
    (hR : ∀ r ∈ R, y * r * y⁻¹ ∈ R) :
    Nat.card R ≡ Nat.card (R ⊓ centralizer {y} : Subgroup G) [MOD p] := by
  classical
  have := Fintype.ofFinite R
  let f : Function.End R := fun r => ⟨y * r * y⁻¹, hR r r.2⟩
  have hf : ∀ k : ℕ, ∀ r : R, (((f ^ k : Function.End R) r : R) : G) = y ^ k * r * y⁻¹ ^ k := by
    intro k
    induction k with
    | zero => intro r; simp; rfl
    | succ k ih =>
      intro r
      rw [pow_succ']
      show y * ((f ^ k) r : G) * y⁻¹ = _
      rw [ih, pow_succ', pow_succ]
      group
  have hfp : f ^ p ^ n = 1 := by
    funext r
    apply Subtype.ext
    rw [hf]
    simp [inv_pow, hy]
    rfl
  have key := Equiv.Perm.card_fixedPoints_modEq hfp
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at key
  convert key using 1
  refine Nat.card_congr
    { toFun := fun r => ⟨⟨r, (mem_inf.mp r.2).1⟩, Subtype.ext ?_⟩
      invFun := fun r => ⟨r.1, mem_inf.mpr ⟨r.1.2, ?_⟩⟩
      left_inv := fun r => rfl
      right_inv := fun r => rfl }
  · have := (mem_inf.mp r.2).2
    rw [mem_centralizer_singleton_iff] at this
    show y * r * y⁻¹ = r
    rw [← this, mul_inv_cancel_right]
  · have h : y * (r.1 : G) * y⁻¹ = r.1 := congrArg Subtype.val r.2
    rw [mem_centralizer_singleton_iff]
    nth_rw 1 [← h]
    group

theorem index_normalizer_modEq_one {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : (normalizer (P : Set G)).index ≡ 1 [MOD p] := by
  rw [← P.card_eq_index_normalizer]
  exact card_sylow_modEq_one p G

theorem card_sylow_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) {k m : ℕ} (hk : p ^ k ∣ Nat.card G) (hm : Nat.card G ∣ m * p ^ k)
    (hpm : ¬ p ∣ m) : Nat.card P = p ^ k := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp P.2
  have h1 : p ^ k ∣ p ^ j := hj ▸ P.pow_dvd_card_of_pow_dvd_card hk
  have h2 : p ^ j ∣ m * p ^ k := hj ▸ (card_subgroup_dvd_card P.1).trans hm
  have h3 : p ^ j ∣ p ^ k :=
    (Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm)).dvd_of_dvd_mul_left h2
  rw [hj, Nat.dvd_antisymm h3 h1]

theorem card_stabilizer (a : Fin 9) :
    Nat.card (MulAction.stabilizer (Perm (Fin 9)) a) = 40320 := by
  have h1 := (MulAction.stabilizer (Perm (Fin 9)) a).card_mul_index
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at h1
  have : Nat.factorial 9 = 362880 := by decide
  omega

theorem card_dvd_of_forall_apply_eq {Y : Subgroup (Perm (Fin 9))} {a : Fin 9}
    (h : ∀ g ∈ Y, g a = a) : Nat.card Y ∣ 40320 := by
  rw [← card_stabilizer a]
  exact card_dvd_of_le fun g hg => MulAction.mem_stabilizer_iff.mpr (h g hg)

theorem dvd_of_odd_of_dvd_two_pow_mul {c m : ℕ} (hc : Odd c) (h : c ∣ 2 ^ 7 * m) : c ∣ m :=
  (Nat.Coprime.pow_right 7 (Nat.coprime_two_right.mpr hc)).dvd_of_dvd_mul_left h

theorem card_dvd_of_odd {Y : Subgroup (Perm (Fin 9))} (hY : Odd (Nat.card Y)) :
    Nat.card Y ∣ 2835 := by
  have h := card_subgroup_dvd_card Y
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin,
    show Nat.factorial 9 = 2 ^ 7 * 2835 by decide] at h
  exact dvd_of_odd_of_dvd_two_pow_mul hY h

theorem card_dvd_of_odd_of_forall_apply_eq {Y : Subgroup (Perm (Fin 9))} (hY : Odd (Nat.card Y))
    {a : Fin 9} (h : ∀ g ∈ Y, g a = a) : Nat.card Y ∣ 315 :=
  dvd_of_odd_of_dvd_two_pow_mul hY (card_dvd_of_forall_apply_eq h)

theorem cycleType_of_orderOf_prime {x : Perm (Fin 9)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : orderOf x = p) : x.cycleType = {p} := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (hx ▸ hp)
  rw [hx] at hn
  have hle : x.cycleType.sum ≤ 9 := by
    rw [Perm.sum_cycleType]
    exact (card_le_univ _).trans (by simp)
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hle
  have : n = 0 := by nlinarith
  subst this
  simpa using hn

theorem card_support_of_orderOf_prime {x : Perm (Fin 9)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : orderOf x = p) : #x.support = p := by
  rw [← Perm.sum_cycleType, cycleType_of_orderOf_prime hp hp5 hx, Multiset.sum_singleton]

theorem card_centralizer_of_orderOf_prime {x : Perm (Fin 9)} {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hx : orderOf x = p) :
    Nat.card (centralizer {x}) = (9 - p).factorial * p := by
  rw [Perm.nat_card_centralizer, cycleType_of_orderOf_prime hp hp5 hx]
  simp [Multiset.count_singleton]

theorem exists_apply_eq_of_orderOf_prime {x : Perm (Fin 9)} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hx : orderOf x = p) : ∃ a, x a = a := by
  have hs := card_support_of_orderOf_prime hp hp5 hx
  have hp9 : p ≤ 9 := hs ▸ (card_le_univ _).trans (by simp)
  have hp9' : p ≠ 9 := by
    rintro rfl
    exact absurd hp (by decide)
  have hc : 0 < #x.supportᶜ := by
    rw [card_compl, hs, Fintype.card_fin]
    omega
  obtain ⟨a, ha⟩ := card_pos.mp hc
  exact ⟨a, Perm.notMem_support.mp (mem_compl.mp ha)⟩

theorem exists_fixed_pair {q : Perm (Fin 9)} (hq : orderOf q = 7) {a : Fin 9} (ha : q a = a) :
    ∃ b, b ≠ a ∧ q b = b ∧ ∀ i, q i = i → i = a ∨ i = b := by
  have hc : #q.supportᶜ = 2 := by
    rw [card_compl, card_support_of_orderOf_prime Nat.prime_seven (by norm_num) hq,
      Fintype.card_fin]
  have hmem : ∀ i, i ∈ q.supportᶜ ↔ q i = i := fun i => by
    rw [mem_compl, Perm.notMem_support]
  obtain ⟨x, y, hxy, hs⟩ := card_eq_two.mp hc
  have hxa : ∀ i, q i = i → i = x ∨ i = y := fun i hi => by
    have := (hmem i).mpr hi
    rwa [hs, mem_insert, mem_singleton] at this
  have hx : q x = x := (hmem x).mp (by rw [hs]; simp)
  have hy : q y = y := (hmem y).mp (by rw [hs]; simp)
  rcases hxa a ha with rfl | rfl
  · exact ⟨y, hxy.symm, hy, hxa⟩
  · exact ⟨x, hxy, hx, fun i hi => (hxa i hi).symm⟩

theorem apply_eq_of_mem_normalizer {q g : Perm (Fin 9)} (hq : orderOf q = 7)
    (hg : Odd (orderOf g)) (hgq : g ∈ normalizer (zpowers q : Set (Perm (Fin 9))))
    {a : Fin 9} (ha : q a = a) : g a = a := by
  have hfix : ∀ i, q i = i → q (g i) = g i := by
    intro i hi
    have hmem : g⁻¹ * q * g⁻¹⁻¹ ∈ zpowers q :=
      (mem_normalizer_iff.mp (inv_mem hgq) q).mp (mem_zpowers q)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have h := Perm.zpow_apply_eq_self_of_apply_eq_self hi k
    rw [hk, inv_inv, Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h
    exact h
  obtain ⟨b, hba, hqb, hab⟩ := exists_fixed_pair hq ha
  by_contra hne
  have hga : g a = b := (hab _ (hfix a ha)).resolve_left hne
  have hgb : g b = a := by
    rcases hab _ (hfix b hqb) with h | h
    · exact h
    · exact absurd (g.injective (h.trans hga.symm)) hba
  have key : ∀ j : ℕ, (g ^ (2 * j + 1)) a = b := by
    intro j
    induction j with
    | zero => simpa using hga
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add, Perm.mul_apply, ih, sq,
        Perm.mul_apply, hgb, hga]
  obtain ⟨m, hm⟩ := hg
  have h := key m
  rw [← hm, pow_orderOf_eq_one, Perm.one_apply] at h
  exact hba h.symm

theorem eight_le_card_support_of_orderOf_eq_fifteen {g : Perm (Fin 9)} (hg : orderOf g = 15) :
    8 ≤ #g.support := by
  have hsum : g.cycleType.sum ≤ 9 := by
    rw [Perm.sum_cycleType]
    exact (card_le_univ _).trans (by simp)
  have hlcm : g.cycleType.lcm = 15 := by rw [Perm.lcm_cycleType, hg]
  have hmem : ∀ m ∈ g.cycleType, m = 3 ∨ m = 5 := by
    intro m hm
    have h15 : m ∣ 15 := hg ▸ Perm.dvd_of_mem_cycleType hm
    have := Perm.two_le_of_mem_cycleType hm
    have := (Multiset.le_sum_of_mem hm).trans hsum
    interval_cases m <;> omega
  have h5 : 5 ∈ g.cycleType := by
    by_contra h
    have : g.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun m hm => by
      rcases hmem m hm with rfl | rfl
      · exact dvd_rfl
      · exact absurd hm h
    rw [hlcm] at this
    norm_num at this
  have h3 : 3 ∈ g.cycleType := by
    by_contra h
    have : g.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun m hm => by
      rcases hmem m hm with rfl | rfl
      · exact absurd hm h
      · exact dvd_rfl
    rw [hlcm] at this
    norm_num at this
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem h3
  have h5' : 5 ∈ s := by
    rw [hs] at h5
    rcases Multiset.mem_cons.mp h5 with h | h
    · norm_num at h
    · exact h
  obtain ⟨s', hs'⟩ := Multiset.exists_cons_of_mem h5'
  rw [← Perm.sum_cycleType, hs, hs', Multiset.sum_cons, Multiset.sum_cons]
  omega

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm
