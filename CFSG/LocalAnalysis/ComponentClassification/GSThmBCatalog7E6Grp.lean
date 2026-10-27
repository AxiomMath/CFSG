module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Archimedean
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat7E6

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_iff {I : Subgroup G} {a : G} (ha : a ∈ normalizer (I : Set G))
    {x : G} : x ∈ I ⊔ zpowers a ↔ ∃ n ∈ I, ∃ k : ℤ, x = n * a ^ k := by
  have hk : ∀ k : ℤ, ∀ n ∈ I, a ^ k * n * (a ^ k)⁻¹ ∈ I := fun k n hn =>
    (mem_normalizer_iff.mp (zpow_mem ha k) n).mp hn
  constructor
  · intro hx
    let T : Subgroup G :=
      { carrier := {x | ∃ n ∈ I, ∃ k : ℤ, x = n * a ^ k}
        mul_mem' := by
          rintro _ _ ⟨n, hn, k, rfl⟩ ⟨n', hn', k', rfl⟩
          refine ⟨n * (a ^ k * n' * (a ^ k)⁻¹), I.mul_mem hn (hk k n' hn'), k + k', ?_⟩
          rw [zpow_add]
          group
        one_mem' := ⟨1, I.one_mem, 0, by simp⟩
        inv_mem' := by
          rintro _ ⟨n, hn, k, rfl⟩
          refine ⟨a ^ (-k) * n⁻¹ * (a ^ (-k))⁻¹, hk (-k) _ (I.inv_mem hn), -k, ?_⟩
          group }
    have hle : I ⊔ zpowers a ≤ T :=
      sup_le (fun n hn => ⟨n, hn, 0, by simp⟩) (zpowers_le.mpr ⟨1, I.one_mem, 1, by simp⟩)
    exact hle hx
  · rintro ⟨n, hn, k, rfl⟩
    exact mul_mem (mem_sup_left hn) (mem_sup_right (zpow_mem (mem_zpowers a) k))

theorem zpow_mem_iff_even {I : Subgroup G} {a : G} (ha2 : a * a ∈ I) (haI : a ∉ I) (k : ℤ) :
    a ^ k ∈ I ↔ Even k := by
  have h2 : ∀ j : ℤ, a ^ (2 * j) ∈ I := fun j => by
    rw [zpow_mul, zpow_two]
    exact zpow_mem ha2 j
  constructor
  · intro h
    rcases Int.even_or_odd k with he | ⟨j, rfl⟩
    · exact he
    · exfalso
      apply haI
      have h3 := I.mul_mem (I.inv_mem (h2 j)) h
      rwa [zpow_add, zpow_one, inv_mul_cancel_left] at h3
  · rintro ⟨j, rfl⟩
    rw [← two_mul]
    exact h2 j

theorem relIndex_sup_zpowers_eq_two {I : Subgroup G} {a : G} (ha : a ∈ normalizer (I : Set G))
    (ha2 : a * a ∈ I) (haI : a ∉ I) : I.relIndex (I ⊔ zpowers a) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨a, mem_sup_right (mem_zpowers a)⟩, fun b => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul]
  obtain ⟨n, hn, k, hb⟩ := (mem_sup_zpowers_iff ha).mp b.2
  have hiff : ∀ j : ℤ, (n * a ^ j ∈ I ↔ Even j) := fun j => by
    rw [← zpow_mem_iff_even ha2 haI j]
    exact ⟨fun h => by simpa using I.mul_mem (I.inv_mem hn) h, fun h => I.mul_mem hn h⟩
  have hba : (b : G) * a = n * a ^ (k + 1) := by rw [hb, zpow_add_one, mul_assoc]
  rw [hba, hb, hiff, hiff, Int.even_add_one]
  by_cases he : Even k
  · exact Or.inr ⟨he, fun h => h he⟩
  · exact Or.inl ⟨he, he⟩

theorem mem_of_odd_zpow_mem {I : Subgroup G} {a : G} (ha4 : a ^ 4 ∈ I) {k : ℤ}
    (hk : a ^ (1 - 2 * k) ∈ I) : a ∈ I := by
  have h4 : ∀ t : ℤ, a ^ (4 * t) ∈ I := fun t => by
    rw [zpow_mul]
    exact zpow_mem (by exact_mod_cast ha4) t
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h := I.mul_mem hk (h4 t)
    rwa [← zpow_add, show 1 - 2 * (t + t) + 4 * t = 1 by ring, zpow_one] at h
  · have h := I.mul_mem hk (h4 (t + 1))
    rw [← zpow_add, show 1 - 2 * (2 * t + 1) + 4 * (t + 1) = 3 by ring] at h
    have h' := I.mul_mem (I.inv_mem h) (h4 1)
    rw [← zpow_neg, ← zpow_add, show -3 + 4 * 1 = (1 : ℤ) by ring, zpow_one] at h'
    exact h'

theorem relIndex_sup_zpowers_eq_four {I : Subgroup G} {a : G} (ha : a ∈ normalizer (I : Set G))
    (ha4 : a ^ 4 ∈ I) (ha2 : a ^ 2 ∉ I) : I.relIndex (I ⊔ zpowers a) = 4 := by
  have ha2n : a ^ 2 ∈ normalizer (I : Set G) := pow_mem ha 2
  have hJ : I.relIndex (I ⊔ zpowers (a ^ 2)) = 2 :=
    relIndex_sup_zpowers_eq_two ha2n (by rw [← pow_add]; exact ha4) ha2
  have haJ : a ∈ normalizer ((I ⊔ zpowers (a ^ 2) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have hk : ∀ y, y ∈ I ⊔ zpowers (a ^ 2) → a * y * a⁻¹ ∈ I ⊔ zpowers (a ^ 2) := by
      intro y hy
      obtain ⟨n, hn, k, rfl⟩ := (mem_sup_zpowers_iff ha2n).mp hy
      have e : a * (n * (a ^ 2) ^ k) * a⁻¹ = (a * n * a⁻¹) * (a ^ 2) ^ k := by
        rw [show a * (n * (a ^ 2) ^ k) * a⁻¹ = (a * n * a⁻¹) * (a * (a ^ 2) ^ k * a⁻¹) by group]
        congr 1
        rw [(((Commute.refl a).pow_right 2).zpow_right k).eq, mul_inv_cancel_right]
      rw [e]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp ha n).mp hn))
        (mem_sup_right (zpow_mem (mem_zpowers _) k))
    have hk' : ∀ y, y ∈ I ⊔ zpowers (a ^ 2) → a⁻¹ * y * a⁻¹⁻¹ ∈ I ⊔ zpowers (a ^ 2) := by
      intro y hy
      obtain ⟨n, hn, k, rfl⟩ := (mem_sup_zpowers_iff ha2n).mp hy
      have hai : a⁻¹ ∈ normalizer (I : Set G) := inv_mem ha
      have e : a⁻¹ * (n * (a ^ 2) ^ k) * a⁻¹⁻¹ = (a⁻¹ * n * a⁻¹⁻¹) * (a ^ 2) ^ k := by
        rw [show a⁻¹ * (n * (a ^ 2) ^ k) * a⁻¹⁻¹ = (a⁻¹ * n * a⁻¹⁻¹) * (a⁻¹ * (a ^ 2) ^ k * a) by
          group]
        congr 1
        rw [((((Commute.refl a).pow_right 2).zpow_right k).inv_left).eq, inv_mul_cancel_right]
      rw [e]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp hai n).mp hn))
        (mem_sup_right (zpow_mem (mem_zpowers _) k))
    constructor
    · exact hk x
    · intro hx
      have := hk' _ hx
      rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at this
  have haJ2 : a * a ∈ I ⊔ zpowers (a ^ 2) := mem_sup_right (by rw [← sq]; exact mem_zpowers _)
  have haJn : a ∉ I ⊔ zpowers (a ^ 2) := by
    intro h
    obtain ⟨n, hn, k, hk⟩ := (mem_sup_zpowers_iff ha2n).mp h
    have h1 : a ^ (1 - 2 * k) ∈ I := by
      have e2 : (a ^ 2) ^ k = a ^ (2 * k) := by
        rw [← zpow_natCast, ← zpow_mul]
        norm_num
      have e : a ^ (1 - 2 * k) = n := by
        have hn' : n = a * ((a ^ 2) ^ k)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hk.symm
        rw [hn', e2, zpow_sub, zpow_one]
      rw [e]
      exact hn
    exact ha2 (pow_mem (mem_of_odd_zpow_mem ha4 h1) 2)
  have hJ2 : (I ⊔ zpowers (a ^ 2)).relIndex (I ⊔ zpowers (a ^ 2) ⊔ zpowers a) = 2 :=
    relIndex_sup_zpowers_eq_two haJ haJ2 haJn
  have hsup : I ⊔ zpowers (a ^ 2) ⊔ zpowers a = I ⊔ zpowers a := by
    rw [sup_assoc, sup_eq_right.mpr (zpowers_le.mpr (pow_mem (mem_zpowers a) 2))]
  rw [← Subgroup.relIndex_mul_relIndex I (I ⊔ zpowers (a ^ 2)) (I ⊔ zpowers a) le_sup_left
    (sup_le le_sup_left (zpowers_le.mpr (mem_sup_right (pow_mem (mem_zpowers a) 2)))), hJ,
    ← hsup, hJ2]

theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  rw [← heq] at hn
  obtain ⟨x, hx, hxn⟩ := hn
  have : x = n := by
    have := hxn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact mul_left_cancel (mul_right_cancel this)
  rwa [← this]

theorem conj_mem_sup_zpowers {H : Subgroup G} {g a b : G} (ha : g * a * g⁻¹ ∈ H)
    (hb : g * b * g⁻¹ ∈ H) : ∀ x ∈ zpowers a ⊔ zpowers b, g * x * g⁻¹ ∈ H := by
  intro x hx
  have hle : (zpowers a ⊔ zpowers b).map (MulAut.conj g).toMonoidHom ≤ H := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)
  exact hle ⟨x, hx, rfl⟩

theorem card_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have comm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hAB a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype comm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff, hinf]
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype comm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

@[expose] def bpow (x : G) (b : Bool) : G := if b then x else 1

theorem bpow_mul_bpow {x : G} (hx : x * x = 1) (b c : Bool) :
    bpow x b * bpow x c = bpow x (xor b c) := by
  cases b <;> cases c <;> simp [bpow, hx]

@[expose] def prod4 (a b c d : G) (v : Bool × Bool × Bool × Bool) : G :=
  bpow a v.1 * bpow b v.2.1 * bpow c v.2.2.1 * bpow d v.2.2.2

@[expose] def xor4 (v w : Bool × Bool × Bool × Bool) : Bool × Bool × Bool × Bool :=
  (xor v.1 w.1, xor v.2.1 w.2.1, xor v.2.2.1 w.2.2.1, xor v.2.2.2 w.2.2.2)

theorem prod4_mul_prod4 {C : Type*} [CommGroup C] {a b c d : C} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1) (v w : Bool × Bool × Bool × Bool) :
    prod4 a b c d v * prod4 a b c d w = prod4 a b c d (xor4 v w) := by
  simp only [prod4, xor4, ← bpow_mul_bpow ha, ← bpow_mul_bpow hb, ← bpow_mul_bpow hc,
    ← bpow_mul_bpow hd]
  simp only [mul_assoc, mul_left_comm]

theorem xor4_self (v : Bool × Bool × Bool × Bool) : xor4 v v = (false, false, false, false) := by
  simp [xor4]

theorem xor4_eq_zero {v w : Bool × Bool × Bool × Bool}
    (h : xor4 v w = (false, false, false, false)) : v = w := by
  obtain ⟨v1, v2, v3, v4⟩ := v
  obtain ⟨w1, w2, w3, w4⟩ := w
  simp only [xor4, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases v1 <;> cases w1 <;> cases v2 <;> cases w2 <;> cases v3 <;> cases w3 <;> cases v4 <;>
    cases w4 <;> simp_all

theorem card_closure_four_comm {C : Type*} [CommGroup C] {a b c d : C} (ha : a * a = 1)
    (hb : b * b = 1) (hc : c * c = 1) (hd : d * d = 1)
    (hind : ∀ v, prod4 a b c d v = 1 → v = (false, false, false, false)) :
    Nat.card ↥(closure ({a, b, c, d} : Set C)) = 16 ∧
      ∀ y ∈ closure ({a, b, c, d} : Set C), y * y = 1 := by
  classical
  let T : Subgroup C :=
    { carrier := Set.range (prod4 a b c d)
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨xor4 v w, (prod4_mul_prod4 ha hb hc hd v w).symm⟩
      one_mem' := ⟨(false, false, false, false), by simp [prod4, bpow]⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        refine ⟨v, ?_⟩
        have h := prod4_mul_prod4 ha hb hc hd v v
        rw [xor4_self, show prod4 a b c d (false, false, false, false) = 1 by
          simp [prod4, bpow]] at h
        exact (inv_eq_of_mul_eq_one_right h).symm }
  have hT : closure ({a, b, c, d} : Set C) = T := by
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨(true, false, false, false), by simp [prod4, bpow]⟩
      · exact ⟨(false, true, false, false), by simp [prod4, bpow]⟩
      · exact ⟨(false, false, true, false), by simp [prod4, bpow]⟩
      · exact ⟨(false, false, false, true), by simp [prod4, bpow]⟩
    · rintro _ ⟨v, rfl⟩
      have hmem : ∀ (x : C) (e : Bool), x ∈ closure ({a, b, c, d} : Set C) →
          bpow x e ∈ closure ({a, b, c, d} : Set C) := fun x e hx => by
        cases e
        · exact one_mem _
        · exact hx
      exact mul_mem (mul_mem (mul_mem (hmem a _ (subset_closure (by simp)))
        (hmem b _ (subset_closure (by simp)))) (hmem c _ (subset_closure (by simp))))
        (hmem d _ (subset_closure (by simp)))
  have hinj : Function.Injective (prod4 a b c d) := by
    intro v w hvw
    apply xor4_eq_zero
    apply hind
    rw [← prod4_mul_prod4 ha hb hc hd, hvw, prod4_mul_prod4 ha hb hc hd, xor4_self]
    simp [prod4, bpow]
  refine ⟨?_, ?_⟩
  · rw [hT]
    change Nat.card (Set.range (prod4 a b c d)) = 16
    rw [Nat.card_range_of_injective hinj]
    simp
  · rw [hT]
    rintro _ ⟨v, rfl⟩
    rw [prod4_mul_prod4 ha hb hc hd, xor4_self]
    simp [prod4, bpow]

theorem card_closure_four {a b c d : G} (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hd : d * d = 1) (hab : a * b = b * a) (hac : a * c = c * a) (had : a * d = d * a)
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (hind : ∀ v, prod4 a b c d v = 1 → v = (false, false, false, false)) :
    Nat.card ↥(closure ({a, b, c, d} : Set G)) = 16 ∧
      ∀ y ∈ closure ({a, b, c, d} : Set G), y * y = 1 := by
  classical
  set k : Set G := {a, b, c, d} with hk
  have hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x := by
    intro x hx y hy
    simp only [hk, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first | rfl | assumption | exact Eq.symm ‹_›
  have hpw : k.Pairwise Commute := fun x hx y hy _ => hcomm x hx y hy
  have : IsMulCommutative ↥(closure k) := Subgroup.isMulCommutative_closure hpw
  let _ : CommGroup ↥(closure k) :=
    { (inferInstance : Group ↥(closure k)) with
      mul_comm := fun x y => (IsMulCommutative.is_comm (M := ↥(closure k))).comm x y }
  have hmem : ∀ x ∈ k, x ∈ closure k := fun x hx => subset_closure hx
  set a' : ↥(closure k) := ⟨a, hmem a (by simp [hk])⟩
  set b' : ↥(closure k) := ⟨b, hmem b (by simp [hk])⟩
  set c' : ↥(closure k) := ⟨c, hmem c (by simp [hk])⟩
  set d' : ↥(closure k) := ⟨d, hmem d (by simp [hk])⟩
  have hcoe : ∀ v, ((prod4 a' b' c' d' v : ↥(closure k)) : G) = prod4 a b c d v := by
    rintro ⟨v1, v2, v3, v4⟩
    cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> simp [prod4, bpow, a', b', c', d']
  have hsq : ∀ x : ↥(closure k), (x : G) * x = 1 → x * x = 1 := fun x hx => Subtype.ext hx
  obtain ⟨h16, -⟩ := card_closure_four_comm (hsq a' ha) (hsq b' hb) (hsq c' hc) (hsq d' hd)
    (fun v hv => hind v (by rw [← hcoe, hv]; rfl))
  have htop : closure ({a', b', c', d'} : Set ↥(closure k)) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := k), closure_le]
    rintro x hx
    have hx' : (x : G) ∈ k := hx
    simp only [hk, Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
    apply subset_closure
    rcases hx' with h | h | h | h
    · left; exact Subtype.ext h
    · right; left; exact Subtype.ext h
    · right; right; left; exact Subtype.ext h
    · right; right; right; exact Subtype.ext h
  refine ⟨?_, fun y hy => ?_⟩
  · rw [htop, Subgroup.card_top] at h16
    exact h16
  · obtain ⟨-, h2⟩ := card_closure_four_comm (hsq a' ha) (hsq b' hb) (hsq c' hc) (hsq d' hd)
      (fun v hv => hind v (by rw [← hcoe, hv]; rfl))
    have := h2 ⟨y, hy⟩ (by rw [htop]; exact mem_top _)
    exact congrArg Subtype.val this

theorem exists_zpow_eq {I : Subgroup G} {a : G} (ha : a ∈ normalizer (I : Set G)) {n₀ : G}
    (hn₀ : n₀ ∈ I) (m j : ℤ) : ∃ n' ∈ I, (n₀ * a ^ m) ^ j = n' * a ^ (j * m) := by
  have hk : ∀ k : ℤ, ∀ n ∈ I, a ^ k * n * (a ^ k)⁻¹ ∈ I := fun k n hn =>
    (mem_normalizer_iff.mp (zpow_mem ha k) n).mp hn
  have hnat : ∀ j : ℕ, ∃ n' ∈ I, (n₀ * a ^ m) ^ j = n' * a ^ ((j : ℤ) * m) := by
    intro j
    induction j with
    | zero => exact ⟨1, I.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨n', hn', h⟩ := ih
      refine ⟨n' * (a ^ ((j : ℤ) * m) * n₀ * (a ^ ((j : ℤ) * m))⁻¹),
        I.mul_mem hn' (hk _ _ hn₀), ?_⟩
      rw [pow_succ, h, show ((j + 1 : ℕ) : ℤ) * m = (j : ℤ) * m + m by push_cast; ring,
        zpow_add]
      group
  rcases Int.eq_nat_or_neg j with ⟨j, rfl | rfl⟩
  · obtain ⟨n', hn', h⟩ := hnat j
    exact ⟨n', hn', by rw [zpow_natCast]; exact h⟩
  · obtain ⟨n', hn', h⟩ := hnat j
    refine ⟨a ^ (-((j : ℤ) * m)) * n'⁻¹ * (a ^ (-((j : ℤ) * m)))⁻¹,
      hk _ _ (I.inv_mem hn'), ?_⟩
    rw [zpow_neg, zpow_natCast, h, show -(j : ℤ) * m = -((j : ℤ) * m) by ring]
    group

theorem exists_inf_eq_sup_zpowers {I : Subgroup G} {a : G} (ha : a ∈ normalizer (I : Set G))
    (R : Subgroup G) : ∃ y ∈ R, R ⊓ (I ⊔ zpowers a) = (R ⊓ I) ⊔ zpowers y := by
  have hk : ∀ k : ℤ, ∀ n ∈ I, a ^ k * n * (a ^ k)⁻¹ ∈ I := fun k n hn =>
    (mem_normalizer_iff.mp (zpow_mem ha k) n).mp hn
  let S : AddSubgroup ℤ :=
    { carrier := {k | ∃ n ∈ I, n * a ^ k ∈ R}
      add_mem' := by
        rintro k k' ⟨n, hn, hr⟩ ⟨n', hn', hr'⟩
        refine ⟨n * (a ^ k * n' * (a ^ k)⁻¹), I.mul_mem hn (hk k n' hn'), ?_⟩
        have h := R.mul_mem hr hr'
        convert h using 1
        rw [zpow_add]
        group
      zero_mem' := ⟨1, I.one_mem, by simp⟩
      neg_mem' := by
        rintro k ⟨n, hn, hr⟩
        refine ⟨a ^ (-k) * n⁻¹ * (a ^ (-k))⁻¹, hk (-k) _ (I.inv_mem hn), ?_⟩
        have h := R.inv_mem hr
        convert h using 1
        group }
  obtain ⟨m, hm⟩ := Int.subgroup_cyclic S
  have hmS : m ∈ S := by rw [hm]; exact AddSubgroup.subset_closure rfl
  obtain ⟨n₀, hn₀, hr₀⟩ := hmS
  refine ⟨n₀ * a ^ m, hr₀, le_antisymm ?_ ?_⟩
  · rintro x ⟨hxR, hxH⟩
    obtain ⟨n, hn, k, rfl⟩ := (mem_sup_zpowers_iff ha).mp hxH
    have hkS : k ∈ S := ⟨n, hn, hxR⟩
    rw [hm, AddSubgroup.mem_closure_singleton] at hkS
    obtain ⟨j, rfl⟩ := hkS
    obtain ⟨n', hn', hpow⟩ := exists_zpow_eq ha hn₀ m j
    have hx : n * a ^ (j • m) = (n * n'⁻¹) * (n₀ * a ^ m) ^ j := by
      rw [hpow, smul_eq_mul]
      group
    rw [hx]
    refine mul_mem (mem_sup_left ⟨?_, I.mul_mem hn (I.inv_mem hn')⟩)
      (mem_sup_right (zpow_mem (mem_zpowers _) j))
    have h1 : n * n'⁻¹ = n * a ^ (j • m) * ((n₀ * a ^ m) ^ j)⁻¹ := by
      rw [hpow, smul_eq_mul]
      group
    rw [h1]
    exact R.mul_mem hxR (R.inv_mem (zpow_mem hr₀ j))
  · apply sup_le (inf_le_inf_left R le_sup_left)
    rw [zpowers_le]
    exact ⟨hr₀, mul_mem (mem_sup_left hn₀) (mem_sup_right (zpow_mem (mem_zpowers a) m))⟩

theorem exists_finset_card_le_four {a₁ a₂ a₃ a₄ : G}
    (h₂ : a₂ ∈ normalizer ((zpowers a₁ : Subgroup G) : Set G))
    (h₃ : a₃ ∈ normalizer ((zpowers a₁ ⊔ zpowers a₂ : Subgroup G) : Set G))
    (h₄ : a₄ ∈ normalizer ((zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers a₃ : Subgroup G) : Set G))
    {R : Subgroup G} (hR : R ≤ zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers a₃ ⊔ zpowers a₄) :
    ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = R := by
  classical
  have h₁ : a₁ ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    simp only [mem_bot]
    constructor
    · rintro rfl
      group
    · intro h'
      have : h = a₁⁻¹ * (a₁ * h * a₁⁻¹) * a₁ := by group
      rw [this, h']
      group
  obtain ⟨y₁, -, e₁⟩ := exists_inf_eq_sup_zpowers h₁ R
  obtain ⟨y₂, -, e₂⟩ := exists_inf_eq_sup_zpowers h₂ R
  obtain ⟨y₃, -, e₃⟩ := exists_inf_eq_sup_zpowers h₃ R
  obtain ⟨y₄, -, e₄⟩ := exists_inf_eq_sup_zpowers h₄ R
  rw [bot_sup_eq, inf_bot_eq, bot_sup_eq] at e₁
  rw [e₁] at e₂
  rw [e₂] at e₃
  rw [e₃, inf_eq_left.mpr hR] at e₄
  refine ⟨{y₁, y₂, y₃, y₄}, Finset.card_le_four, ?_⟩
  rw [e₄]
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [Set.insert_eq, Set.insert_eq, Set.insert_eq, closure_union, closure_union, closure_union,
    ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure]
  simp only [sup_assoc]

end Cat7E6

end CFSG.ComponentClassification.GSThmB
