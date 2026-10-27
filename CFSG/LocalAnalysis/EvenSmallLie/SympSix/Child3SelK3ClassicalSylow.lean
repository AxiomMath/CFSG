module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelSylow

public section

namespace CFSG.EvenSmallLie.Child3.SelK3Classical

open Subgroup

variable {T : Type} [Group T]

theorem mem_zpowers_of_orderOf_eq_three [Finite T] {a y : T} (ha : orderOf a = 3) :
    y ∈ zpowers a ↔ y = 1 ∨ y = a ∨ y = a ^ 2 := by
  classical
  constructor
  · intro hy
    rw [mem_zpowers_iff_mem_range_orderOf, ha, Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range] at hk
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _
    · exact pow_mem (mem_zpowers _) 2

theorem centralizer_pow_two_of_pow_three {g : T} (hg : g ^ 3 = 1) :
    centralizer ({g ^ 2} : Set T) = centralizer ({g} : Set T) := by
  apply le_antisymm
  · intro z hz
    rw [mem_centralizer_singleton_iff] at hz ⊢
    have h4 : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hg, one_mul]
    rw [h4]
    exact (Commute.pow_left hz.symm 2).eq.symm
  · intro z hz
    rw [mem_centralizer_singleton_iff] at hz ⊢
    exact (Commute.pow_left hz.symm 2).eq.symm

theorem card_zpowers_sup_zpowers [Finite T] {a b : T} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hb' : b ∉ zpowers a) : Nat.card ↥(zpowers a ⊔ zpowers b) = 9 := by
  have hcomm : ∀ (m : zpowers a) (n : zpowers b),
      Commute ((zpowers a).subtype m) ((zpowers b).subtype n) := by
    rintro ⟨_, ⟨i, rfl⟩⟩ ⟨_, ⟨j, rfl⟩⟩
    exact hab.zpow_zpow i j
  set φ := MonoidHom.noncommCoprod (zpowers a).subtype (zpowers b).subtype hcomm
  have hb3 : b ^ 3 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hdisj : Disjoint (zpowers a).subtype.range (zpowers b).subtype.range := by
    rw [range_subtype, range_subtype, disjoint_iff_inf_le]
    intro x ⟨hxa, hxb⟩
    rw [mem_bot]
    rcases (mem_zpowers_of_orderOf_eq_three hb).mp hxb with h | h | h
    · exact h
    · exact absurd (h ▸ hxa) hb'
    · exfalso
      apply hb'
      have : b = x ^ 2 := by
        rw [h, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hb3, one_mul]
      rw [this]
      exact pow_mem hxa 2
  have hinj : Function.Injective φ :=
    (MonoidHom.noncommCoprod_injective _ _ hcomm).mpr
      ⟨Subtype.val_injective, Subtype.val_injective, hdisj⟩
  have hrange : φ.range = zpowers a ⊔ zpowers b := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
    Nat.card_zpowers, Nat.card_zpowers, ha, hb]

theorem four_dvd_card_centralizer_of_sylow [Finite T] (h9 : 9 ∣ Nat.card T)
    (h27 : ¬ 27 ∣ Nat.card T) {a b : T} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Commute a b) (hb' : b ∉ zpowers a)
    (hCa : 4 ∣ Nat.card (centralizer ({a} : Set T)))
    (hCb : 4 ∣ Nat.card (centralizer ({b} : Set T)))
    (hCab : 4 ∣ Nat.card (centralizer ({a * b} : Set T)))
    (hCa2b : 4 ∣ Nat.card (centralizer ({a ^ 2 * b} : Set T)))
    (x : T) (hx : orderOf x = 3) : 4 ∣ Nat.card (centralizer ({x} : Set T)) := by
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hfact : (Nat.card T).factorization 3 = 2 := by
    have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) hT0).mp
      (by norm_num; exact h9)
    have h2 : ¬ 3 ≤ (Nat.card T).factorization 3 := fun h =>
      h27 (by simpa using (Nat.prime_three.pow_dvd_iff_le_factorization (k := 3) hT0).mpr h)
    omega
  refine k3_of_sylow (zpowers a ⊔ zpowers b)
    (by rw [card_zpowers_sup_zpowers ha hb hab hb', hfact]; norm_num) ?_ x hx
  intro y hyP hy3
  have hcomm : ∀ (m : zpowers a) (n : zpowers b),
      Commute ((zpowers a).subtype m) ((zpowers b).subtype n) := by
    rintro ⟨_, ⟨i, rfl⟩⟩ ⟨_, ⟨j, rfl⟩⟩
    exact hab.zpow_zpow i j
  rw [← range_subtype (zpowers a), ← range_subtype (zpowers b),
    ← MonoidHom.noncommCoprod_range _ _ hcomm] at hyP
  obtain ⟨⟨⟨m, hm⟩, ⟨n, hn⟩⟩, hmn⟩ := hyP
  simp only [MonoidHom.noncommCoprod_apply, coe_subtype] at hmn
  have ha3 : a ^ 3 = 1 := by rw [← ha, pow_orderOf_eq_one]
  have hb3 : b ^ 3 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hab3 : (a * b) ^ 3 = 1 := by rw [hab.mul_pow, ha3, hb3, one_mul]
  have ha2b3 : (a ^ 2 * b) ^ 3 = 1 := by
    rw [(hab.pow_left 2).mul_pow, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, ha3, one_pow,
      hb3, one_mul]
  rcases (mem_zpowers_of_orderOf_eq_three ha).mp hm with h1 | h1 | h1 <;>
    rcases (mem_zpowers_of_orderOf_eq_three hb).mp hn with h2 | h2 | h2 <;>
    rw [h1, h2] at hmn <;> rw [← hmn]
  · rw [← hmn, mul_one, orderOf_one] at hy3
    omega
  · rwa [one_mul]
  · rwa [one_mul, centralizer_pow_two_of_pow_three hb3]
  · rwa [mul_one]
  · exact hCab
  · have : a * b ^ 2 = (a ^ 2 * b) ^ 2 := by
      rw [(hab.pow_left 2).mul_pow, ← pow_mul]
      congr 1
      rw [show 2 * 2 = 3 + 1 by rfl, pow_add, ha3, one_mul, pow_one]
    rwa [this, centralizer_pow_two_of_pow_three ha2b3]
  · rwa [mul_one, centralizer_pow_two_of_pow_three ha3]
  · exact hCa2b
  · have : a ^ 2 * b ^ 2 = (a * b) ^ 2 := by rw [hab.mul_pow]
    rwa [this, centralizer_pow_two_of_pow_three hab3]

end CFSG.EvenSmallLie.Child3.SelK3Classical
