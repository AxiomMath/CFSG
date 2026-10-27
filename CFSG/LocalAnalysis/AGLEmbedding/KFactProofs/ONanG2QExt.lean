module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.AGLEmbedding.KFactProofs.G2Q

variable {G : Type*} [Group G]

structure Ext3 (T : Subgroup G) (y : G) : Prop where
  pow_three : y ^ 3 = 1
  normal : ∀ t ∈ T, y * t * y⁻¹ ∈ T
  not_mem : y ∉ T

variable {T : Subgroup G} {y : G}

theorem Ext3.conj_pow (h : Ext3 T y) (k : ℕ) : ∀ t ∈ T, y ^ k * t * (y ^ k)⁻¹ ∈ T := by
  induction k with
  | zero => intro t ht; simpa using ht
  | succ k ih =>
    intro t ht
    have := h.normal _ (ih t ht)
    simpa [pow_succ', mul_assoc] using this

theorem Ext3.inv_pow_eq (h : Ext3 T y) (k : ℕ) : (y ^ k)⁻¹ = y ^ (2 * k) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, h.pow_three, one_pow]

theorem Ext3.sq_not_mem (h : Ext3 T y) : y ^ 2 ∉ T := by
  intro h2
  apply h.not_mem
  have : y = (y ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, h.pow_three, one_mul, pow_one]
  rw [this]
  exact pow_mem h2 2

theorem Ext3.pow_mod (h : Ext3 T y) (n : ℕ) : y ^ n = y ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h.pow_three, one_pow, one_mul]

theorem Ext3.pow_not_mem (h : Ext3 T y) {m : ℕ} (h0 : m % 3 ≠ 0) : y ^ m ∉ T := by
  rw [h.pow_mod]
  have : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases this with h1 | h1 <;> rw [h1]
  · simpa using h.not_mem
  · exact h.sq_not_mem

def extSub (h : Ext3 T y) : Subgroup G where
  carrier := {g | ∃ t ∈ T, ∃ k : ℕ, g = t * y ^ k}
  mul_mem' := by
    rintro _ _ ⟨t, ht, k, rfl⟩ ⟨t', ht', l, rfl⟩
    refine ⟨t * (y ^ k * t' * (y ^ k)⁻¹), T.mul_mem ht (h.conj_pow k t' ht'), k + l, ?_⟩
    rw [pow_add]
    group
  one_mem' := ⟨1, T.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨t, ht, k, rfl⟩
    refine ⟨y ^ (2 * k) * t⁻¹ * (y ^ (2 * k))⁻¹, h.conj_pow (2 * k) _ (T.inv_mem ht), 2 * k, ?_⟩
    rw [mul_inv_rev, ← h.inv_pow_eq k]
    group

theorem mem_extSub_iff (h : Ext3 T y) {g : G} :
    g ∈ extSub h ↔ ∃ t ∈ T, ∃ k : ℕ, g = t * y ^ k := Iff.rfl

theorem le_extSub (h : Ext3 T y) : T ≤ extSub h := fun t ht => ⟨t, ht, 0, by simp⟩

theorem y_mem_extSub (h : Ext3 T y) : y ∈ extSub h := ⟨1, T.one_mem, 1, by simp⟩

theorem mem_extSub_iff_lt (h : Ext3 T y) {g : G} :
    g ∈ extSub h ↔ ∃ t ∈ T, ∃ k < 3, g = t * y ^ k := by
  constructor
  · rintro ⟨t, ht, k, rfl⟩
    refine ⟨t, ht, k % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [h.pow_mod k]
  · rintro ⟨t, ht, k, -, rfl⟩
    exact ⟨t, ht, k, rfl⟩

theorem card_extSub (h : Ext3 T y) : Nat.card (extSub h) = 3 * Nat.card T := by
  have hf : ∀ p : T × Fin 3, (p.1 : G) * y ^ (p.2 : ℕ) ∈ extSub h :=
    fun p => ⟨p.1, p.1.2, p.2, rfl⟩
  let f : T × Fin 3 → extSub h := fun p => ⟨(p.1 : G) * y ^ (p.2 : ℕ), hf p⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨t, ht⟩, k⟩ ⟨⟨t', ht'⟩, l⟩ hfe
    have h1 : t * y ^ (k : ℕ) = t' * y ^ (l : ℕ) := congrArg Subtype.val hfe
    have hkl : k = l := by
      by_contra hne
      have hne' : (k : ℕ) ≠ l := fun e => hne (Fin.ext e)
      have hmem : y ^ (k : ℕ) * (y ^ (l : ℕ))⁻¹ ∈ T := by
        have : y ^ (k : ℕ) * (y ^ (l : ℕ))⁻¹ = t⁻¹ * t' := by
          calc y ^ (k : ℕ) * (y ^ (l : ℕ))⁻¹
              = t⁻¹ * (t * y ^ (k : ℕ)) * (y ^ (l : ℕ))⁻¹ := by group
            _ = t⁻¹ * (t' * y ^ (l : ℕ)) * (y ^ (l : ℕ))⁻¹ := by rw [h1]
            _ = t⁻¹ * t' := by group
        rw [this]
        exact T.mul_mem (T.inv_mem ht) ht'
      rw [h.inv_pow_eq, ← pow_add] at hmem
      refine h.pow_not_mem ?_ hmem
      have := k.2
      have := l.2
      omega
    subst hkl
    have : t = t' := mul_right_cancel h1
    subst this
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨t, ht, k, hk, rfl⟩ := (mem_extSub_iff_lt h).1 hg
    exact ⟨(⟨t, ht⟩, ⟨k, hk⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_fin]
  ring

theorem relIndex_extSub [Finite G] (h : Ext3 T y) : T.relIndex (extSub h) = 3 := by
  have h1 := Subgroup.index_mul_card (T.subgroupOf (extSub h))
  have h2 : Nat.card (T.subgroupOf (extSub h)) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_extSub h)).toEquiv
  rw [h2, card_extSub h] at h1
  have hpos : 0 < Nat.card T := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem card_le_nine [Finite G] (h : Ext3 T y)
    (hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hT9 : ∀ F : Subgroup G, F ≤ T → (∀ x ∈ F, x ^ 3 = 1) → Nat.card F ≤ 9)
    (hT3 : ∀ F : Subgroup G, F ≤ T → (∀ x ∈ F, x ^ 3 = 1 ∧ y * x * y⁻¹ = x) → Nat.card F ≤ 3)
    {E : Subgroup G} (hE : E ≤ extSub h) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 9 := by
  by_cases hET : E ≤ T
  · exact hT9 E hET hE3
  obtain ⟨e, heE, heT⟩ := IsConcreteLE.not_le_iff_exists.1 hET
  obtain ⟨t₀, ht₀, k, hk3, he⟩ := (mem_extSub_iff_lt h).1 (hE heE)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact heT (by simpa [he] using ht₀)
  set F : Subgroup G := (T.subgroupOf E).map E.subtype with hF
  have hFle : F ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hFx : ∀ x ∈ F, x ∈ E ∧ x ∈ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  have hFfix : ∀ x ∈ F, x ^ 3 = 1 ∧ y * x * y⁻¹ = x := by
    intro x hx
    obtain ⟨hxE, hxT⟩ := hFx x hx
    refine ⟨hE3 x hxE, ?_⟩
    have hxe : x * e = e * x := hEc x hxE e heE
    have hxt : x * t₀ = t₀ * x := hTc x hxT t₀ ht₀
    have hxy : x * y ^ k = y ^ k * x := by
      rw [he] at hxe
      have : t₀ * (x * y ^ k) = t₀ * (y ^ k * x) := by
        calc t₀ * (x * y ^ k) = (t₀ * x) * y ^ k := by group
          _ = (x * t₀) * y ^ k := by rw [hxt]
          _ = x * (t₀ * y ^ k) := by group
          _ = t₀ * y ^ k * x := hxe
          _ = t₀ * (y ^ k * x) := by group
      exact mul_left_cancel this
    have hyx : x * y = y * x := by
      have hk12 : k = 1 ∨ k = 2 := by omega
      rcases hk12 with rfl | rfl
      · simpa using hxy
      · have hy4 : y = y ^ 2 * y ^ 2 := by
          rw [← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, h.pow_three, one_mul, pow_one]
        calc x * y = x * (y ^ 2 * y ^ 2) := by rw [← hy4]
          _ = (x * y ^ 2) * y ^ 2 := by group
          _ = (y ^ 2 * x) * y ^ 2 := by rw [hxy]
          _ = y ^ 2 * (x * y ^ 2) := by group
          _ = y ^ 2 * (y ^ 2 * x) := by rw [hxy]
          _ = (y ^ 2 * y ^ 2) * x := by group
          _ = y * x := by rw [← hy4]
    calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [hyx]
      _ = x := by group
  have hFcard : Nat.card F ≤ 3 := hT3 F hFle hFfix
  have hF' : Nat.card (T.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.equivMapOfInjective _ E.subtype E.subtype_injective).toEquiv
  have hidx : T.relIndex E ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right hE (H := T)
      (by rw [relIndex_extSub h]; norm_num)
    rwa [relIndex_extSub h] at this
  have hcard := Subgroup.card_mul_index (T.subgroupOf E)
  calc Nat.card E = Nat.card (T.subgroupOf E) * T.relIndex E := hcard.symm
    _ ≤ 3 * 3 := Nat.mul_le_mul (hF' ▸ hFcard) hidx
    _ = 9 := by norm_num

theorem pow_six_mem (A : Subgroup G) (a b : G) (ha2 : a ^ 2 ∈ A) (hb2 : b ^ 2 ∈ A)
    (ha : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (hb : ∀ x ∈ A, b * x * b⁻¹ ∈ A)
    (hab : (a * b) ^ 3 = (b * a) ^ 3) : (a * b) ^ 6 ∈ A := by
  have hmem : ∀ c : G, c ^ 2 ∈ A → (∀ x ∈ A, c * x * c⁻¹ ∈ A) →
      c ∈ Subgroup.normalizer (A : Set G) := by
    intro c hc2 hc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hc x hx, fun hx => ?_⟩
    have h1 : x = (c ^ 2)⁻¹ * (c * (c * x * c⁻¹) * c⁻¹) * c ^ 2 := by group
    rw [h1]
    exact A.mul_mem (A.mul_mem (A.inv_mem hc2) (hc _ hx)) hc2
  set N := Subgroup.normalizer (A : Set G) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).2 le_rfl
  let a' : N := ⟨a, hmem a ha2 ha⟩
  let b' : N := ⟨b, hmem b hb2 hb⟩
  have h1 : ∀ c : N, ((c : G) ^ 2 ∈ A) → (QuotientGroup.mk c : N ⧸ A.subgroupOf N) ^ 2 = 1 := by
    intro c hc
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hc
  have hx := h1 a' ha2
  have hz := h1 b' hb2
  set x : N ⧸ A.subgroupOf N := QuotientGroup.mk a'
  set z : N ⧸ A.subgroupOf N := QuotientGroup.mk b'
  have hbraid : (x * z) ^ 3 = (z * x) ^ 3 := by
    have : (a' * b') ^ 3 = (b' * a') ^ 3 := Subtype.ext hab
    have := congrArg (QuotientGroup.mk : N → N ⧸ A.subgroupOf N) this
    simpa [x, z, QuotientGroup.mk_mul, QuotientGroup.mk_pow] using this
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz)
  have hinv : (x * z)⁻¹ = z * x := by rw [mul_inv_rev, hxinv, hzinv]
  have h6 : (x * z) ^ 6 = 1 := by
    calc (x * z) ^ 6 = (x * z) ^ 3 * (x * z) ^ 3 := by rw [← pow_add]
      _ = (x * z) ^ 3 * (z * x) ^ 3 := by rw [hbraid]
      _ = (x * z) ^ 3 * ((x * z)⁻¹) ^ 3 := by rw [hinv]
      _ = 1 := by rw [inv_pow]; exact mul_inv_cancel _
  have : ((a' * b') ^ 6 : N) ∈ A.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
    exact h6
  exact this

end CFSG.AGLEmbedding.KFactProofs.G2Q
