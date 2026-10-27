module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open QuaternionGroup

theorem noncyclic_pow_half {X : Type*} [Group X] [Finite X] {m : ℕ} (hcard : Nat.card X = 2 ^ m)
    (hnc : ¬ IsCyclic X) (g : X) : g ^ (2 ^ (m - 1)) = 1 := by
  have hdvd : orderOf g ∣ 2 ^ m := hcard ▸ orderOf_dvd_natCard g
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hm : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hcard
    have : Subsingleton X := (Nat.card_eq_one_iff_unique.1 hcard).1
    exact hnc inferInstance
  have hjm : j < m := by
    rcases lt_or_eq_of_le hj with h | h
    · exact h
    · exfalso
      apply hnc
      have : orderOf g = Nat.card X := by rw [hjo, h, hcard]
      exact isCyclic_of_orderOf_eq_card g this
  rw [← orderOf_dvd_iff_pow_eq_one, hjo]
  exact pow_dvd_pow 2 (by omega)

section QG

variable {m : ℕ} [NeZero m]

theorem m_ne_zero : ((m : ℕ) : ZMod (2 * m)) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (NeZero.pos m) h
  have := NeZero.pos m
  omega

theorem two_mul_eq_zero_iff (i : ZMod (2 * m)) : i + i = 0 ↔ i = 0 ∨ i = (m : ZMod (2 * m)) := by
  constructor
  · intro h
    have h2 : ((2 * i.val : ℕ) : ZMod (2 * m)) = 0 := by
      have e1 : ((2 * i.val : ℕ) : ZMod (2 * m)) = (i.val : ZMod (2 * m)) + (i.val : ZMod (2 * m)) := by
        push_cast
        exact two_mul _
      rw [e1, ZMod.natCast_zmod_val]
      exact h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have hm : m ∣ i.val := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 h2
    have hlt : i.val < 2 * m := ZMod.val_lt i
    obtain ⟨c, hc⟩ := hm
    have hc2 : c < 2 := by
      by_contra hcon
      have hcon' : 2 ≤ c := not_lt.1 hcon
      have : m * 2 ≤ m * c := Nat.mul_le_mul_left m hcon'
      omega
    interval_cases c
    · left
      have : i.val = 0 := by omega
      exact (ZMod.val_eq_zero i).1 this
    · right
      have h3 : i.val = m := by omega
      have h4 : ((i.val : ℕ) : ZMod (2 * m)) = (m : ZMod (2 * m)) := by rw [h3]
      rwa [ZMod.natCast_zmod_val] at h4
  · rintro (rfl | rfl)
    · simp
    · have h5 : ((m + m : ℕ) : ZMod (2 * m)) = 0 := by
        have : m + m = 2 * m := by omega
        rw [this]
        exact ZMod.natCast_self (2 * m)
      push_cast at h5
      exact h5

theorem a_m_ne_one : (a (m : ZMod (2 * m)) : QuaternionGroup m) ≠ 1 := by
  intro h
  have h' : (a (m : ZMod (2 * m)) : QuaternionGroup m) = a 0 := h
  have h'' := a.inj h'
  exact m_ne_zero h''

theorem sq_eq_one_iff (x : QuaternionGroup m) : x * x = 1 ↔ x = 1 ∨ x = a (m : ZMod (2 * m)) := by
  cases x with
  | a i =>
    rw [a_mul_a]
    have h1 : (1 : QuaternionGroup m) = a 0 := rfl
    rw [h1]
    simp only [a.injEq]
    exact two_mul_eq_zero_iff i
  | xa i =>
    rw [xa_mul_xa]
    constructor
    · intro h
      exfalso
      have h' : (a ((m : ZMod (2 * m)) + i - i) : QuaternionGroup m) = a 0 := h
      have h'' := a.inj h'
      apply m_ne_zero (m := m)
      simpa using h''
    · rintro (h | h) <;> cases h

def rotSub (m : ℕ) : Subgroup (QuaternionGroup m) where
  carrier := {x | ∃ i, x = a i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, by rw [a_mul_a]⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

theorem a_mem_zpowers (i : ZMod (2 * m)) : a i ∈ Subgroup.zpowers (a 1 : QuaternionGroup m) := by
  refine ⟨(i.val : ℤ), ?_⟩
  simp only [zpow_natCast]
  rw [a_one_pow]
  simp

theorem mem_zpowers_a1 {x : QuaternionGroup m} :
    x ∈ Subgroup.zpowers (a 1 : QuaternionGroup m) ↔ ∃ i, x = a i := by
  constructor
  · intro h
    exact (Subgroup.zpowers_le (H := rotSub m)).2 ⟨1, rfl⟩ h
  · rintro ⟨i, rfl⟩
    exact a_mem_zpowers i

theorem xa_not_mem_zpowers (i : ZMod (2 * m)) :
    xa i ∉ Subgroup.zpowers (a 1 : QuaternionGroup m) := by
  intro h
  obtain ⟨j, hj⟩ := mem_zpowers_a1.1 h
  cases hj

omit [NeZero m] in
theorem card_zpowers_a1 : Nat.card (Subgroup.zpowers (a 1 : QuaternionGroup m)) = 2 * m := by
  rw [Nat.card_zpowers, orderOf_a_one]

theorem card_quat : Nat.card (QuaternionGroup m) = 4 * m := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

omit [NeZero m] in
theorem xa_inv_conj (i j : ZMod (2 * m)) : xa i * a j * (xa i)⁻¹ = (a j)⁻¹ := by
  have h1 : (xa i : QuaternionGroup m)⁻¹ = xa ((m : ZMod (2 * m)) + i) := rfl
  rw [h1, xa_mul_a, xa_mul_xa]
  have h2 : (a j : QuaternionGroup m)⁻¹ = a (-j) := rfl
  rw [h2]
  congr 1
  have h3 : ((m : ZMod (2 * m)) + ((m : ZMod (2 * m)) + i) - (i + j)) =
      ((m : ZMod (2 * m)) + m) - j := by ring
  rw [h3]
  have h4 : ((m : ZMod (2 * m)) + m) = 0 := by
    have : ((m + m : ℕ) : ZMod (2 * m)) = 0 := by
      have e : m + m = 2 * m := by omega
      rw [e]
      exact ZMod.natCast_self (2 * m)
    push_cast at this
    exact this
  rw [h4]
  ring

end QG

structure GQ {G : Type*} [Group G] (Q : Subgroup G) (z : G) : Prop where
  z_sq : z * z = 1
  z_ne : z ≠ 1
  z_mem : z ∈ Q
  uniq : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z
  ex : ∃ M : Subgroup G, M ≤ Q ∧ IsCyclic ↥M ∧ z ∈ M ∧ 4 ≤ Nat.card ↥M ∧ M.relIndex Q = 2 ∧
    ∀ x ∈ Q, x ∉ M → x * x = z ∧ ∀ y ∈ M, x * y * x⁻¹ = y⁻¹

theorem gq_of_equiv {G : Type*} [Group G] {Q : Subgroup G} {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (e : ↥Q ≃* QuaternionGroup m) {z : G} (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    GQ Q z := by
  let zq : ↥Q := ⟨z, hzQ⟩
  have hzq2 : zq * zq = 1 := Subtype.ext hz2
  have hzq1 : zq ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hez : e zq = a (m : ZMod (2 * m)) := by
    have : e zq * e zq = 1 := by rw [← map_mul, hzq2, map_one]
    rcases (sq_eq_one_iff _).1 this with h | h
    · exact absurd (e.injective (h.trans (map_one e).symm)) hzq1
    · exact h
  refine ⟨hz2, hz1, hzQ, ?_, ?_⟩
  · intro x hx hx2
    let xq : ↥Q := ⟨x, hx⟩
    have hxq2 : xq * xq = 1 := Subtype.ext hx2
    have : e xq * e xq = 1 := by rw [← map_mul, hxq2, map_one]
    rcases (sq_eq_one_iff _).1 this with h | h
    · left
      exact congrArg Subtype.val (e.injective (h.trans (map_one e).symm))
    · right
      exact congrArg Subtype.val (e.injective (h.trans hez.symm))
  · let g₀q : ↥Q := e.symm (a 1)
    let g₀ : G := (g₀q : G)
    have hmem : ∀ x : G, x ∈ Subgroup.zpowers g₀ ↔
        ∃ hx : x ∈ Q, e ⟨x, hx⟩ ∈ Subgroup.zpowers (a 1 : QuaternionGroup m) := by
      intro x
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨zpow_mem g₀q.2 k, ?_⟩
        have : (⟨g₀ ^ k, zpow_mem g₀q.2 k⟩ : ↥Q) = g₀q ^ k := Subtype.ext (by simp [g₀])
        rw [this, map_zpow]
        simp only [g₀q, MulEquiv.apply_symm_apply]
        exact ⟨k, rfl⟩
      · rintro ⟨hx, k, hk⟩
        refine ⟨k, ?_⟩
        have hk' : (a 1 : QuaternionGroup m) ^ k = e ⟨x, hx⟩ := hk
        have h1 : e.symm ((a 1 : QuaternionGroup m) ^ k) = g₀q ^ k := by rw [map_zpow]
        have h2 : (⟨x, hx⟩ : ↥Q) = e.symm ((a 1 : QuaternionGroup m) ^ k) := by
          rw [hk']; simp
        have h3 : (⟨x, hx⟩ : ↥Q) = g₀q ^ k := h2.trans h1
        have := congrArg Subtype.val h3
        simpa [g₀] using this.symm
    have hcard : Nat.card (Subgroup.zpowers g₀) = 2 * m := by
      rw [Nat.card_zpowers]
      have h1 : orderOf g₀ = orderOf g₀q := Subgroup.orderOf_coe g₀q
      rw [h1]
      have h2 : orderOf g₀q = orderOf (a 1 : QuaternionGroup m) := by
        show orderOf (e.symm (a 1)) = _
        exact MulEquiv.orderOf_eq _ _
      rw [h2, orderOf_a_one]
    have hle : Subgroup.zpowers g₀ ≤ Q := by rw [Subgroup.zpowers_le]; exact g₀q.2
    refine ⟨Subgroup.zpowers g₀, hle, inferInstance, ?_, ?_, ?_, ?_⟩
    · rw [hmem]
      refine ⟨hzQ, ?_⟩
      show e zq ∈ _
      rw [hez]
      exact (mem_zpowers_a1).2 ⟨_, rfl⟩
    · omega
    · have h1 : Nat.card (Subgroup.zpowers g₀ |>.subgroupOf Q) = 2 * m := by
        rw [← hcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      have h2 := Subgroup.card_mul_index ((Subgroup.zpowers g₀).subgroupOf Q)
      have h3 : Nat.card ↥Q = 4 * m := by
        rw [Nat.card_congr e.toEquiv, card_quat]
      rw [h1, h3] at h2
      have : 2 * m * Subgroup.index ((Subgroup.zpowers g₀).subgroupOf Q) = 2 * m * 2 := by omega
      exact Nat.eq_of_mul_eq_mul_left (by have := NeZero.pos m; omega) this
    · intro x hx hxM
      let xq : ↥Q := ⟨x, hx⟩
      have hxM' : e xq ∉ Subgroup.zpowers (a 1 : QuaternionGroup m) :=
        fun h => hxM ((hmem x).2 ⟨hx, h⟩)
      obtain ⟨i, hi⟩ : ∃ i, e xq = xa i := by
        rcases h : e xq with j | j
        · exact absurd (mem_zpowers_a1.2 ⟨j, rfl⟩) (h ▸ hxM')
        · exact ⟨j, rfl⟩
      refine ⟨?_, ?_⟩
      · have : e (xq * xq) = e zq := by
          rw [map_mul, hi, hez, xa_mul_xa]
          congr 1
          ring
        exact congrArg Subtype.val (e.injective this)
      · intro y hy
        obtain ⟨hyQ, hy'⟩ := (hmem y).1 hy
        obtain ⟨j, hj⟩ := mem_zpowers_a1.1 hy'
        let yq : ↥Q := ⟨y, hyQ⟩
        have : e (xq * yq * xq⁻¹) = e yq⁻¹ := by
          rw [map_mul, map_mul, map_inv, map_inv, hi, hj, xa_inv_conj]
        exact congrArg Subtype.val (e.injective this)

section Arith

variable {G : Type*} [Group G]

theorem card_mul_relIndex_of_le {A B : Subgroup G} (hle : A ≤ B) :
    Nat.card ↥A * A.relIndex B = Nat.card ↥B := by
  have h1 : Nat.card ↥(A.subgroupOf B) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 := Subgroup.card_mul_index (A.subgroupOf B)
  rw [h1] at h2
  rw [Subgroup.relIndex]
  simpa using h2

theorem exists_generator_of_cyclic {W : Subgroup G} (hWc : IsCyclic ↥W) :
    ∃ g ∈ W, W = Subgroup.zpowers g := by
  obtain ⟨⟨g, hg⟩, hgg⟩ := hWc.exists_generator
  refine ⟨g, hg, ?_⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨k, hk⟩ := hgg ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  · rw [Subgroup.zpowers_le]; exact hg

theorem isCyclic_of_le {A B : Subgroup G} (hle : A ≤ B) (hB : IsCyclic ↥B) : IsCyclic ↥A := by
  have : IsCyclic ↥(A.subgroupOf B) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hle).surjective

theorem relIndex_ne_zero' [Finite G] (W P : Subgroup G) : W.relIndex P ≠ 0 := by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem two_mul_card_inf [Finite G] {P Q W : Subgroup G} (hPQ : P ≤ Q)
    (hW : IsCyclic ↥W) (hWi : W.relIndex Q = 2) (hP : ¬ IsCyclic ↥P) :
    2 * Nat.card ↥(W ⊓ P) = Nat.card ↥P := by
  have h1 : (W ⊓ P).relIndex P = W.relIndex P := Subgroup.inf_relIndex_right W P
  have h2 : W.relIndex P ≤ W.relIndex Q :=
    Subgroup.relIndex_le_of_le_right hPQ (by rw [hWi]; norm_num)
  have h3 : W.relIndex P ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hP (isCyclic_of_le h hW)
  have h4 : W.relIndex P ≠ 0 := relIndex_ne_zero' W P
  have h5 : W.relIndex P = 2 := by omega
  have h6 := card_mul_relIndex_of_le (A := W ⊓ P) (B := P) inf_le_right
  rw [h1, h5] at h6
  omega

theorem pow_four_eq (g : G) : g ^ 4 = (g * g) * (g * g) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem mem_sup_of_commute' {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G}
    (hy : y ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hc a ha b hb]; group
      rwa [this]
    · intro hb
      have h1 := hc a ha _ hb
      have : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [h1]
          _ = b := by group
      rwa [this] at hb
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

end Arith

theorem two_mul_card_mul_card_le {G : Type*} [Group G] [Finite G] {S₁ Q V : Subgroup G}
    [(Q.subgroupOf S₁).Normal]
    (hS₁ : IsPGroup 2 ↥S₁) (hQS : Q ≤ S₁)
    (hnc : ¬ IsCyclic (↥S₁ ⧸ Q.subgroupOf S₁)) (hV : IsCyclic ↥V) (hVS : V ≤ S₁)
    (hVQ : V ⊓ Q = ⊥) : 2 * Nat.card ↥V * Nat.card ↥Q ≤ Nat.card ↥S₁ := by
  let φ : ↥V →* (↥S₁ ⧸ Q.subgroupOf S₁) :=
    (QuotientGroup.mk' (Q.subgroupOf S₁)).comp (Subgroup.inclusion hVS)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : (Subgroup.inclusion hVS v) ∈ Q.subgroupOf S₁ := by
      have : QuotientGroup.mk' (Q.subgroupOf S₁) (Subgroup.inclusion hVS v) = 1 := hv
      exact (QuotientGroup.eq_one_iff _).1 this
    have h2 : (v : G) ∈ Q := h1
    have h3 : (v : G) ∈ V ⊓ Q := ⟨v.2, h2⟩
    rw [hVQ] at h3
    exact Subtype.ext (by simpa using h3)
  have hXp : IsPGroup 2 (↥S₁ ⧸ Q.subgroupOf S₁) :=
    hS₁.of_surjective (QuotientGroup.mk' (Q.subgroupOf S₁)) (QuotientGroup.mk'_surjective _)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hXp
  obtain ⟨g, hgV, hgen⟩ := exists_generator_of_cyclic hV
  have hord : orderOf (φ ⟨g, hgV⟩) = Nat.card ↥V := by
    rw [orderOf_injective φ hφ]
    have : orderOf (⟨g, hgV⟩ : ↥V) = orderOf g := Subgroup.orderOf_mk g hgV
    rw [this, ← Nat.card_zpowers, ← hgen]
  have hpow := noncyclic_pow_half hm hnc (φ ⟨g, hgV⟩)
  have hdvd : Nat.card ↥V ∣ 2 ^ (m - 1) := by
    rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpow
  have hle : Nat.card ↥V ≤ 2 ^ (m - 1) := Nat.le_of_dvd (by positivity) hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at hm
    have : Subsingleton (↥S₁ ⧸ Q.subgroupOf S₁) := (Nat.card_eq_one_iff_unique.1 hm).1
    exact hnc inferInstance
  have hXcard : Nat.card (↥S₁ ⧸ Q.subgroupOf S₁) * Nat.card ↥Q = Nat.card ↥S₁ := by
    have h1 : Nat.card ↥(Q.subgroupOf S₁) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf S₁)
    rw [h1] at this
    exact this.symm
  have h2m : 2 * 2 ^ (m - 1) = 2 ^ m := by
    rw [← pow_succ']; congr 1; omega
  calc 2 * Nat.card ↥V * Nat.card ↥Q ≤ 2 * 2 ^ (m - 1) * Nat.card ↥Q := by
        apply Nat.mul_le_mul_right; omega
    _ = Nat.card (↥S₁ ⧸ Q.subgroupOf S₁) * Nat.card ↥Q := by rw [h2m, hm]
    _ = Nat.card ↥S₁ := hXcard

theorem GQ.card_of_normal_maxCyclic {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z : G}
    (hQ : GQ Q z) {W : Subgroup G} (hWQ : W ≤ Q) (hWc : IsCyclic ↥W)
    (hWmax : ∀ C : Subgroup G, W ≤ C → C ≤ Q → IsCyclic ↥C → C = W)
    (hWn : ∀ x ∈ Q, ∀ w ∈ W, x * w * x⁻¹ ∈ W) : 2 * Nat.card ↥W = Nat.card ↥Q := by
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have hQM : Nat.card ↥M * 2 = Nat.card ↥Q := by
    have := card_mul_relIndex_of_le hMQ
    rwa [hMi] at this
  obtain ⟨g, hgW, hgen⟩ := exists_generator_of_cyclic hWc
  by_cases hgM : g ∈ M
  · have hWM : W ≤ M := by rw [hgen, Subgroup.zpowers_le]; exact hgM
    have : M = W := hWmax M hWM hMQ hMc
    rw [← this]
    omega
  · obtain ⟨hg2, hginv⟩ := hM g (hWQ hgW) hgM
    have hz1 := hQ.z_ne
    have hzz := hQ.z_sq
    have hord : orderOf g = 4 := by
      have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := g) (by
        intro h
        apply hz1
        rw [← hg2]
        simpa [pow_two] using h) (by
        have : g ^ 2 ^ (1 + 1) = (g * g) * (g * g) := by
          rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
          exact pow_four_eq g
        rw [this, hg2, hzz])
      simpa using h
    have hWelts : ∀ w ∈ W, w = 1 ∨ w = z ∨ w = g ∨ w = g * z := by
      intro w hw
      rw [hgen] at hw
      obtain ⟨k, hk⟩ := hw
      have hk' : g ^ k = w := hk
      subst hk'
      have h1 : g ^ k = g ^ (k % 4) := by
        have := zpow_mod_orderOf g k
        rw [hord] at this
        simpa using this.symm
      rw [h1]
      have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
      rcases h4 with h | h | h | h <;> rw [h]
      · left; simp
      · right; right; left; simp
      · right; left; rw [zpow_two]; exact hg2
      · right; right; right
        have : g ^ (3 : ℤ) = g * (g * g) := by
          rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [this, hg2]
    have hy2 : ∀ y ∈ M, y * y = 1 ∨ y * y = z := by
      intro y hy
      have h1 := hWn y (hMQ hy) g hgW
      have h3 : g * y⁻¹ * g⁻¹ = y := by
        have := hginv y⁻¹ (inv_mem hy)
        simpa using this
      have h2 : y * g * y⁻¹ = (y * y) * g := by
        calc y * g * y⁻¹ = y * (g * y⁻¹ * g⁻¹) * g := by group
          _ = y * y * g := by rw [h3]
      rw [h2] at h1
      have h4 : y * y ∈ W := by
        have := mul_mem h1 (inv_mem hgW)
        simpa using this
      rcases hWelts _ h4 with h | h | h | h
      · left; exact h
      · right; exact h
      · exfalso; apply hgM; rw [← h]; exact mul_mem hy hy
      · exfalso; apply hgM
        have : g = (y * y) * z := by rw [h]; simp [mul_assoc, hzz]
        rw [this]; exact mul_mem (mul_mem hy hy) hzM
    have hM4' : ∀ y ∈ M, y ^ 4 = 1 := by
      intro y hy
      rw [pow_four_eq]
      rcases hy2 y hy with h | h <;> rw [h]
      · simp
      · exact hzz
    obtain ⟨c, hcM, hcgen⟩ := exists_generator_of_cyclic hMc
    have hc4 : c ^ 4 = 1 := hM4' c hcM
    have hMcard : Nat.card ↥M = orderOf c := by
      rw [hcgen, Nat.card_zpowers]
    have hdvd : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one hc4
    have hle4 : orderOf c ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hMc4 : Nat.card ↥M = 4 := by omega
    have hWc4 : Nat.card ↥W = 4 := by
      rw [hgen, Nat.card_zpowers, hord]
    omega

theorem no_cyclic_in_central_prod {G : Type*} [Group G] {z : G} {P₁ P₂ V : Subgroup G} {k : ℕ}
    (hk : 1 ≤ k) (h12 : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a) (hzP₁ : z ∈ P₁)
    (hP₂ : ∀ x ∈ P₂, x ^ (2 ^ (k - 1)) = 1 ∨ x ^ (2 ^ (k - 1)) = z)
    (hV : IsCyclic ↥V) (hVcard : Nat.card ↥V = 2 ^ k) (hVP : V ≤ P₁ ⊔ P₂) (hVP₁ : V ⊓ P₁ = ⊥) :
    False := by
  obtain ⟨g, hgV, hgen⟩ := exists_generator_of_cyclic hV
  have hord : orderOf g = 2 ^ k := by
    rw [← hVcard, hgen, Nat.card_zpowers]
  obtain ⟨p₁, hp₁, p₂, hp₂, hg⟩ := mem_sup_of_commute' h12 (hVP hgV)
  have hcomm : p₁ * p₂ = p₂ * p₁ := h12 p₁ hp₁ p₂ hp₂
  have hpow : g ^ (2 ^ (k - 1)) = p₁ ^ (2 ^ (k - 1)) * p₂ ^ (2 ^ (k - 1)) := by
    rw [hg]
    exact (Commute.mul_pow hcomm _)
  have hmem : g ^ (2 ^ (k - 1)) ∈ P₁ := by
    rw [hpow]
    apply mul_mem (pow_mem hp₁ _)
    rcases hP₂ p₂ hp₂ with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hzP₁
  have hmemV : g ^ (2 ^ (k - 1)) ∈ V := pow_mem hgV _
  have h1 : g ^ (2 ^ (k - 1)) ∈ V ⊓ P₁ := ⟨hmemV, hmem⟩
  rw [hVP₁] at h1
  have h2 : g ^ (2 ^ (k - 1)) = 1 := by simpa using h1
  have h3 : orderOf g ∣ 2 ^ (k - 1) := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at h3
  have h4 : 2 ^ k ≤ 2 ^ (k - 1) := Nat.le_of_dvd (by positivity) h3
  have h5 : 2 ^ (k - 1) < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem cyclic_comm {G : Type*} [Group G] {W : Subgroup G} (hW : IsCyclic ↥W) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  obtain ⟨g, hg, hgen⟩ := exists_generator_of_cyclic hW
  rw [hgen]
  rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
  exact (Commute.zpow_zpow_self g i j).eq

theorem GQ.not_isCyclic {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) :
    ¬ IsCyclic ↥Q := by
  intro hc
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have hcomm := cyclic_comm hc
  have hne : ∃ x ∈ Q, x ∉ M := by
    by_contra hcon
    push Not at hcon
    have : Q ≤ M := hcon
    have h1 : M.relIndex Q = 1 := Subgroup.relIndex_eq_one.2 this
    omega
  obtain ⟨x, hxQ, hxM⟩ := hne
  obtain ⟨y, hyM, hygen⟩ := exists_generator_of_cyclic hMc
  have hyo : orderOf y = Nat.card ↥M := by rw [hygen, Nat.card_zpowers]
  have hy2 : y * y ≠ 1 := by
    intro h
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain ⟨-, hinv⟩ := hM x hxQ hxM
  have h1 := hinv y hyM
  have h2 : x * y * x⁻¹ = y := by
    rw [hcomm x hxQ y (hMQ hyM)]; group
  rw [h2] at h1
  apply hy2
  calc y * y = y * y⁻¹⁻¹ := by group
    _ = y⁻¹ * y⁻¹⁻¹ := by rw [← h1]
    _ = 1 := by group

theorem mem_of_pow_four_eq_one {G : Type*} [Group G] [Finite G] {W V : Subgroup G} (hW : IsCyclic ↥W)
    (hV : V ≤ W) (hV2 : IsPGroup 2 ↥V) (hV4 : 4 ≤ Nat.card ↥V) {w : G} (hw : w ∈ W)
    (hw4 : w ^ 4 = 1) : w ∈ V := by
  have hVc : IsCyclic ↥V := isCyclic_of_le hV hW
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hV2
  obtain ⟨a, haV, hagen⟩ := exists_generator_of_cyclic hVc
  have hao : orderOf a = 2 ^ j := by rw [← hj, hagen, Nat.card_zpowers]
  have hj2 : 2 ≤ j := by
    by_contra hcon
    have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set d := orderOf w with hd
  have hdvd4 : d ∣ 4 := orderOf_dvd_of_pow_eq_one hw4
  have hdvdj : d ∣ orderOf a := by
    rw [hao]
    exact hdvd4.trans (by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this]; exact pow_dvd_pow 2 hj2)
  set c := a ^ (orderOf a / d) with hc
  have hco : orderOf c = d := orderOf_pow_orderOf_div (by rw [hao]; positivity) hdvdj
  have hcV : c ∈ V := pow_mem haV _
  have hcW : c ∈ W := hV hcV
  let H : Subgroup ↥W := (Subgroup.zpowers w).subgroupOf W
  let K : Subgroup ↥W := (Subgroup.zpowers c).subgroupOf W
  have hwle : Subgroup.zpowers w ≤ W := by rw [Subgroup.zpowers_le]; exact hw
  have hcle : Subgroup.zpowers c ≤ W := by rw [Subgroup.zpowers_le]; exact hcW
  have hHK : H = K := by
    have := hW
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    have e1 : Nat.card ↥H = Nat.card ↥(Subgroup.zpowers w) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hwle).toEquiv
    have e2 : Nat.card ↥K = Nat.card ↥(Subgroup.zpowers c) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcle).toEquiv
    rw [e1, e2, Nat.card_zpowers, Nat.card_zpowers, hco]
  have hwH : (⟨w, hw⟩ : ↥W) ∈ H := Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers w)
  rw [hHK] at hwH
  have hwK : w ∈ Subgroup.zpowers c := Subgroup.mem_subgroupOf.1 hwH
  exact (Subgroup.zpowers_le.2 hcV) hwK

theorem mem_sup_of_le_normalizer' {G : Type*} [Group G] {A B : Subgroup G}
    (hnorm : A ≤ Subgroup.normalizer (B : Set G)) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

theorem commute_of_involution_mem_sup {G : Type*} [Group G] [Finite G] {z u : G}
    {W₁ W₂ V₁ V₂ : Subgroup G} (hz2 : z * z = 1)
    (hW₁c : IsCyclic ↥W₁) (hW₂c : IsCyclic ↥W₂)
    (hV₁W₂ : V₁ ≤ W₂) (hV₂W₁ : V₂ ≤ W₁) (hV₁p : IsPGroup 2 ↥V₁) (hV₂p : IsPGroup 2 ↥V₂)
    (hV₁4 : 4 ≤ Nat.card ↥V₁) (hV₂4 : 4 ≤ Nat.card ↥V₂)
    (hV₁c : ∀ a ∈ V₁, ∀ b ∈ W₁, a * b = b * a) (hV₂c : ∀ a ∈ V₂, ∀ b ∈ W₂, a * b = b * a)
    (hn₁ : ∀ b ∈ W₂, ∀ a ∈ W₁, b * a * b⁻¹ ∈ W₁) (hn₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b * a⁻¹ ∈ W₂)
    (hinter : ∀ x ∈ W₁, x ∈ W₂ → x = 1 ∨ x = z)
    (hu : u ∈ W₁ ⊔ W₂) (hu2 : u * u = 1) :
    (∀ c ∈ W₂, c * u = u * c) ∧ (∀ c ∈ W₁, c * u = u * c) := by
  have hnorm : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha; exact hn₁ b hb a ha
    · intro ha
      have h1 := hn₁ b⁻¹ (inv_mem hb) _ ha
      have e : b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ = a := by group
      rwa [e] at h1
  obtain ⟨b, hb, a, ha, hba⟩ := mem_sup_of_le_normalizer' hnorm (sup_comm W₁ W₂ ▸ hu)
  set w₁ := b * a * b⁻¹ with hw₁
  have hw₁W : w₁ ∈ W₁ := hn₁ b hb a ha
  have huw : u = w₁ * b := by rw [hba, hw₁]; group
  set w₂ := b with hw₂
  have hw₂W : w₂ ∈ W₂ := hb
  set ε := w₂ * w₁ * w₂⁻¹ * w₁⁻¹ with hε
  have hεW₁ : ε ∈ W₁ := mul_mem (hn₁ w₂ hw₂W w₁ hw₁W) (inv_mem hw₁W)
  have hεW₂ : ε ∈ W₂ := by
    have : ε = w₂ * (w₁ * w₂⁻¹ * w₁⁻¹) := by rw [hε]; group
    rw [this]
    exact mul_mem hw₂W (hn₂ w₁ hw₁W w₂⁻¹ (inv_mem hw₂W))
  have hεc : ε * w₁ = w₁ * ε := cyclic_comm hW₁c ε hεW₁ w₁ hw₁W
  have hu2' : ε * (w₁ * w₁) * (w₂ * w₂) = 1 := by
    have e1 : w₂ * w₁ = ε * w₁ * w₂ := by rw [hε]; group
    calc ε * (w₁ * w₁) * (w₂ * w₂) = ε * w₁ * (w₁ * w₂ * w₂) := by group
      _ = w₁ * ε * (w₁ * w₂ * w₂) := by rw [hεc]
      _ = w₁ * (ε * w₁ * w₂) * w₂ := by group
      _ = w₁ * (w₂ * w₁) * w₂ := by rw [← e1]
      _ = u * u := by rw [huw]; group
      _ = 1 := hu2
  have h1 : (w₁ * w₁) * (w₂ * w₂) = ε⁻¹ := by
    calc (w₁ * w₁) * (w₂ * w₂) = ε⁻¹ * (ε * (w₁ * w₁) * (w₂ * w₂)) := by group
      _ = ε⁻¹ := by rw [hu2']; group
  have hw₁sq : w₁ * w₁ ∈ W₂ := by
    have : w₁ * w₁ = ε⁻¹ * (w₂ * w₂)⁻¹ := by
      calc w₁ * w₁ = ((w₁ * w₁) * (w₂ * w₂)) * (w₂ * w₂)⁻¹ := by group
        _ = ε⁻¹ * (w₂ * w₂)⁻¹ := by rw [h1]
    rw [this]
    exact mul_mem (inv_mem hεW₂) (inv_mem (mul_mem hw₂W hw₂W))
  have hw₂sq : w₂ * w₂ ∈ W₁ := by
    have : w₂ * w₂ = (w₁ * w₁)⁻¹ * ε⁻¹ := by
      calc w₂ * w₂ = (w₁ * w₁)⁻¹ * ((w₁ * w₁) * (w₂ * w₂)) := by group
        _ = (w₁ * w₁)⁻¹ * ε⁻¹ := by rw [h1]
    rw [this]
    exact mul_mem (inv_mem (mul_mem hw₁W hw₁W)) (inv_mem hεW₁)
  have hw₁4 : w₁ ^ 4 = 1 := by
    rw [pow_four_eq]
    rcases hinter _ (mul_mem hw₁W hw₁W) hw₁sq with h | h
    · rw [h]; simp
    · rw [h]; exact hz2
  have hw₂4 : w₂ ^ 4 = 1 := by
    rw [pow_four_eq]
    rcases hinter _ hw₂sq (mul_mem hw₂W hw₂W) with h | h
    · rw [h]; simp
    · rw [h]; exact hz2
  have hw₁V : w₁ ∈ V₂ := mem_of_pow_four_eq_one hW₁c hV₂W₁ hV₂p hV₂4 hw₁W hw₁4
  have hw₂V : w₂ ∈ V₁ := mem_of_pow_four_eq_one hW₂c hV₁W₂ hV₁p hV₁4 hw₂W hw₂4
  constructor
  · intro c hc
    have h1 : w₁ * c = c * w₁ := hV₂c w₁ hw₁V c hc
    have h2 : c * w₂ = w₂ * c := cyclic_comm hW₂c c hc w₂ hw₂W
    rw [huw]
    calc c * (w₁ * w₂) = (c * w₁) * w₂ := by group
      _ = (w₁ * c) * w₂ := by rw [h1]
      _ = w₁ * (c * w₂) := by group
      _ = w₁ * (w₂ * c) := by rw [h2]
      _ = w₁ * w₂ * c := by group
  · intro c hc
    have h1 : c * w₁ = w₁ * c := cyclic_comm hW₁c c hc w₁ hw₁W
    have h2 : w₂ * c = c * w₂ := hV₁c w₂ hw₂V c hc
    rw [huw]
    calc c * (w₁ * w₂) = (c * w₁) * w₂ := by group
      _ = (w₁ * c) * w₂ := by rw [h1]
      _ = w₁ * (c * w₂) := by group
      _ = w₁ * (w₂ * c) := by rw [h2]
      _ = w₁ * w₂ * c := by group

theorem conj_inf_bot {G : Type*} [Group G] {z h : G} {P Q V₁ V : Subgroup G}
    (hP : ∀ x ∈ P, x * x = 1 → x = 1 ∨ x = z) (hQ : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z)
    (hV₁ : V₁ ≤ P) (hmove : h⁻¹ * z * h ≠ z) (hV : ∀ x, x ∈ V ↔ h * x * h⁻¹ ∈ V₁)
    (hV2 : IsPGroup 2 ↥(V ⊓ Q)) : V ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  have hxV : x ∈ V := hx.1
  have hxQ : x ∈ Q := hx.2
  rw [Subgroup.mem_bot]
  by_contra hx1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hV2) ⟨x, hx⟩
  have hoj : orderOf x = 2 ^ j := by
    have := Subgroup.orderOf_mk x hx
    rw [← this]; exact hj
  have hj1 : j ≠ 0 := by
    rintro rfl
    simp at hoj
    exact hx1 hoj
  set y := x ^ (2 ^ (j - 1)) with hy
  have hyV : y ∈ V := pow_mem hxV _
  have hyQ : y ∈ Q := pow_mem hxQ _
  have hy1 : y ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hoj]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hy2 : y * y = 1 := by
    have : y * y = x ^ (2 ^ j) := by
      rw [hy, ← pow_add, ← two_mul, ← pow_succ']
      congr 2; omega
    rw [this, ← hoj]
    exact pow_orderOf_eq_one x
  have hyz : y = z := (hQ y hyQ hy2).resolve_left hy1
  have hhy : h * y * h⁻¹ ∈ V₁ := (hV y).1 hyV
  have hhy2 : (h * y * h⁻¹) * (h * y * h⁻¹) = 1 := by
    calc (h * y * h⁻¹) * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hhy1 : h * y * h⁻¹ ≠ 1 := by
    intro h1
    apply hy1
    have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [this, h1]; group
  have hhz : h * y * h⁻¹ = z := (hP _ (hV₁ hhy) hhy2).resolve_left hhy1
  apply hmove
  rw [hyz] at hhz
  have hcomm : h * z = z * h := by
    calc h * z = (h * z * h⁻¹) * h := by group
      _ = z * h := by rw [hhz]
  calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
    _ = h⁻¹ * (h * z) := by rw [hcomm]
    _ = z := by group

theorem GQ.eight_le_card {G : Type*} [Group G] {Q : Subgroup G} {z : G} (hQ : GQ Q z) :
    8 ≤ Nat.card ↥Q := by
  obtain ⟨M, hMQ, hMc, hzM, hM4, hMi, hM⟩ := hQ.ex
  have := card_mul_relIndex_of_le hMQ
  rw [hMi] at this
  omega

theorem four_elems {G : Type*} [Group G] [Finite G] {U : Subgroup G} {z u : G}
    (hz2 : z * z = 1) (hcard : Nat.card ↥U = 4)
    (hz : z ∈ U) (hu : u ∈ U) (hz1 : z ≠ 1) (huz : u ∉ Subgroup.zpowers z) :
    ∀ y ∈ U, y = 1 ∨ y = z ∨ y = u ∨ y = u * z := by
  have hu1 : u ≠ 1 := fun h => huz (h ▸ one_mem _)
  have huzne : u ≠ z := fun h => huz (h ▸ Subgroup.mem_zpowers z)
  have huz1 : u * z ≠ 1 := by
    intro h
    apply huzne
    calc u = u * z * z := by rw [mul_assoc, hz2, mul_one]
      _ = z := by rw [h, one_mul]
  have huz2 : u * z ≠ z := fun h => hu1 (by simpa using h)
  have huz3 : u * z ≠ u := fun h => hz1 (by simpa using h)
  intro y hy
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have : Fintype ↥U := Fintype.ofFinite _
  have hc : Fintype.card ↥U = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  let f : Fin 5 → ↥U := ![1, ⟨z, hz⟩, ⟨u, hu⟩, ⟨u * z, mul_mem hu hz⟩, ⟨y, hy⟩]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f, Subtype.ext_iff] at hab ⊢ <;>
      first | exact absurd hab.symm ‹_› | exact absurd hab ‹_›
  have := Fintype.card_le_of_injective f hf
  simp at this
  omega

theorem cyclic_comap_conj {G : Type*} [Group G] (H : Subgroup G) (hH : IsCyclic ↥H) (g : G) :
    IsCyclic ↥(H.comap (MulAut.conj g).toMonoidHom) := by
  obtain ⟨a, haH, hgen⟩ := exists_generator_of_cyclic hH
  have hpow : ∀ k : ℤ, (g⁻¹ * a * g) ^ k = g⁻¹ * a ^ k * g := by
    intro k
    have := map_zpow (MulAut.conj g⁻¹) a k
    simpa [MulAut.conj_apply, mul_assoc] using this.symm
  have : H.comap (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g⁻¹ * a * g) := by
    ext x
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgen,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hpow k, hk]; group
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hpow k] at hk
      have : g * x * g⁻¹ = a ^ k := by
        rw [← hk]; group
      exact this.symm
  rw [this]
  infer_instance

theorem card_comap_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card ↥(H.comap (MulAut.conj g).toMonoidHom) = Nat.card ↥H :=
  Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv (by intro a; simp))

theorem numeric82 {N₁ N₂ q₂ s₁ p e₂ a : ℕ} (hN : N₂ ≤ N₁) (hN₂ : 0 < N₂) (hp : 2 * p = N₁ * N₂)
    (hq₂ : q₂ = e₂ * N₁) (hs₁ : s₁ = a * p) (he₂ : e₂ = 1 ∨ e₂ = 2)
    (ha : a = 1 ∨ a = 2 ∨ a = 4) (ha4 : a = 4 → e₂ = 2) (hemb : N₁ * q₂ ≤ s₁) :
    a = 2 * e₂ ∧ N₁ = N₂ := by
  have hN₁ : 0 < N₁ := lt_of_lt_of_le hN₂ hN
  subst hq₂ hs₁
  have key : 2 * e₂ * N₁ ≤ a * N₂ := by
    have h1 : 2 * (N₁ * (e₂ * N₁)) ≤ 2 * (a * p) := by omega
    have h2 : 2 * (a * p) = a * (N₁ * N₂) := by rw [← hp]; ring
    have h3 : N₁ * (2 * e₂ * N₁) ≤ N₁ * (a * N₂) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h3 hN₁
  rcases he₂ with rfl | rfl <;> rcases ha with rfl | rfl | rfl
  · omega
  · exact ⟨rfl, by omega⟩
  · exact absurd (ha4 rfl) (by norm_num)
  · omega
  · omega
  · exact ⟨rfl, by omega⟩

theorem numeric82c {N₁ N₂ q₂ s₁ p a : ℕ} (hN : N₂ ≤ N₁) (hN₂ : 0 < N₂) (hp : 2 * p = N₁ * N₂)
    (hq₂ : q₂ = 2 * N₁) (hs₁ : s₁ = a * p) (ha : a = 1 ∨ a = 2 ∨ a = 4)
    (hemb : 2 * N₁ * q₂ ≤ s₁) : False := by
  have hN₁ : 0 < N₁ := lt_of_lt_of_le hN₂ hN
  subst hq₂ hs₁
  have key : 8 * N₁ ≤ a * N₂ := by
    have h1 : 2 * (2 * N₁ * (2 * N₁)) ≤ 2 * (a * p) := by omega
    have h2 : 2 * (a * p) = a * (N₁ * N₂) := by rw [← hp]; ring
    have h3 : N₁ * (8 * N₁) ≤ N₁ * (a * N₂) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h3 hN₁
  rcases ha with rfl | rfl | rfl <;> omega

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
