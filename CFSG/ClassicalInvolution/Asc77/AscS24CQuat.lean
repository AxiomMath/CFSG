module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega
public import CFSG.ClassicalInvolution.Asc77.AscS24BQ
public import CFSG.ClassicalInvolution.Asc77.AscT7CSetup25

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24

variable {G : Type} [Group G]

@[expose] def InnerOn (y : G) (Q : Subgroup G) : Prop :=
  ∃ q ∈ Q, ∀ v ∈ Q, y * v * y⁻¹ = q * v * q⁻¹

theorem isPGroup_zpowers_of_mul_self [Finite G] {y : G} (h : y * y = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card, Nat.card_zpowers]
  have h2 : orderOf y ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact h)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact ⟨j, hj⟩

theorem orderOf_conj' (h x : G) : orderOf (h * x * h⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq h (show h * x = h * x * h⁻¹ * h by group)).symm

theorem inv_conj_zpow_mem {x y : G} (hyx : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) (j : ℤ) :
    y⁻¹ * x ^ j * y ∈ Subgroup.zpowers x := by
  have h1 : y⁻¹ * x * y = x ∨ y⁻¹ * x * y = x⁻¹ := by
    rcases hyx with h | h
    · left
      calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹) * y := by rw [h]
        _ = x := by group
    · right
      have e : y * x⁻¹ * y⁻¹ = x := by
        rw [show y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ by group, h, inv_inv]
      calc y⁻¹ * x * y = y⁻¹ * (y * x⁻¹ * y⁻¹) * y := by rw [e]
        _ = x⁻¹ := by group
  have e : y⁻¹ * x ^ j * y = (y⁻¹ * x * y) ^ j := by
    rw [show y⁻¹ * x * y = y⁻¹ * x * y⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
  rw [e]
  rcases h1 with h | h <;> rw [h]
  · exact Subgroup.zpow_mem_zpowers _ _
  · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _

theorem exists_conj_s [Finite G] {Q : Subgroup G} {x s y : G} (hU : Subgroup.zpowers x ≤ Q)
    (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs : s ∈ Q)
    (hsU : s ∉ Subgroup.zpowers x) (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hyx : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) : ∃ k : ℤ, y * s * y⁻¹ = s * x ^ k := by
  have hys : y * s * y⁻¹ ∈ Q := hyQ s hs
  have hysU : y * s * y⁻¹ ∉ Subgroup.zpowers x := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hsU
    have e : s = y⁻¹ * (y * s * y⁻¹) * y := by group
    rw [e, ← hj]
    exact inv_conj_zpow_mem hyx j
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (Thompson.inv_mul_mem_of_card_eq_two_mul hU hcard hs hys hsU hysU)
  exact ⟨k, by rw [hk]; group⟩

theorem conj_s_mul {x s y₁ y₂ : G} (hy₁x : y₁ * x * y₁⁻¹ = x ∨ y₁ * x * y₁⁻¹ = x⁻¹) {k₁ k₂ : ℤ}
    (h₁ : y₁ * s * y₁⁻¹ = s * x ^ k₁) (h₂ : y₂ * s * y₂⁻¹ = s * x ^ k₂) :
    ∃ k : ℤ, (Even k ↔ (Even k₁ ↔ Even k₂)) ∧ (y₁ * y₂) * s * (y₁ * y₂)⁻¹ = s * x ^ k := by
  have e : (y₁ * y₂) * s * (y₁ * y₂)⁻¹ = (y₁ * s * y₁⁻¹) * (y₁ * x * y₁⁻¹) ^ k₂ := by
    rw [conj_zpow]
    calc (y₁ * y₂) * s * (y₁ * y₂)⁻¹ = y₁ * (y₂ * s * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * (s * x ^ k₂) * y₁⁻¹ := by rw [h₂]
      _ = y₁ * s * y₁⁻¹ * (y₁ * x ^ k₂ * y₁⁻¹) := by group
  rcases hy₁x with h | h
  · refine ⟨k₁ + k₂, Int.even_add, ?_⟩
    rw [e, h₁, h, mul_assoc, ← zpow_add]
  · refine ⟨k₁ - k₂, Int.even_sub, ?_⟩
    rw [e, h₁, h, inv_zpow', mul_assoc, ← zpow_add, sub_eq_add_neg]

theorem even_iff_of_mul_eq {x s : G} (hx : orderOf x = 4) {k k' : ℤ}
    (h : s * x ^ k = s * x ^ k') : Even k ↔ Even k' := by
  have e : x ^ k = x ^ k' := mul_left_cancel h
  have h1 : x ^ (k - k') = 1 := by rw [zpow_sub, e, mul_inv_cancel]
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hx] at h2
  have h3 : (4 : ℤ) ∣ k - k' := by exact_mod_cast h2
  obtain ⟨c, hc⟩ := h3
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a - 2 * c, by omega⟩
  · rintro ⟨a, ha⟩
    exact ⟨a + 2 * c, by omega⟩

theorem conj_eq_of_gens [Finite G] {Q : Subgroup G} {x s y q : G} (hU : Subgroup.zpowers x ≤ Q)
    (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs : s ∈ Q)
    (hsU : s ∉ Subgroup.zpowers x) (h1 : y * x * y⁻¹ = q * x * q⁻¹)
    (h2 : y * s * y⁻¹ = q * s * q⁻¹) : ∀ v ∈ Q, y * v * y⁻¹ = q * v * q⁻¹ := by
  have hz : ∀ j : ℤ, y * x ^ j * y⁻¹ = q * x ^ j * q⁻¹ := fun j => by
    rw [← conj_zpow, h1, conj_zpow]
  intro v hv
  rcases S24B.mem_or_inv_mul_mem hU hcard hs hsU hv with h | h
  · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    exact hz j
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    have e : v = s * x ^ j := by rw [hj]; group
    rw [e]
    calc y * (s * x ^ j) * y⁻¹ = (y * s * y⁻¹) * (y * x ^ j * y⁻¹) := by group
      _ = (q * s * q⁻¹) * (q * x ^ j * q⁻¹) := by rw [h2, hz]
      _ = q * (s * x ^ j) * q⁻¹ := by group

theorem conj_zpow_of_inv {x s : G} (hsx : s * x * s⁻¹ = x⁻¹) (j : ℤ) :
    s * x ^ j * s⁻¹ = x ^ (-j) ∧ s⁻¹ * x ^ j * s = x ^ (-j) := by
  have h1 : ∀ i : ℤ, s * x ^ i * s⁻¹ = x ^ (-i) := fun i => by
    rw [← conj_zpow, hsx, inv_zpow']
  refine ⟨h1 j, ?_⟩
  have e := h1 (-j)
  rw [neg_neg] at e
  calc s⁻¹ * x ^ j * s = s⁻¹ * (s * x ^ (-j) * s⁻¹) * s := by rw [e]
    _ = x ^ (-j) := by group

theorem zpow_conj_s {x s : G} (hsx : s * x * s⁻¹ = x⁻¹) (j : ℤ) :
    x ^ j * s * (x ^ j)⁻¹ = s * x ^ (-2 * j) := by
  calc x ^ j * s * (x ^ j)⁻¹ = s * (s⁻¹ * x ^ j * s) * (x ^ j)⁻¹ := by group
    _ = s * x ^ (-j) * x ^ (-j) := by rw [(conj_zpow_of_inv hsx j).2, ← zpow_neg]
    _ = s * x ^ (-2 * j) := by rw [mul_assoc, ← zpow_add, show -j + -j = -2 * j by ring]

theorem mul_zpow_conj_s {x s : G} (hsx : s * x * s⁻¹ = x⁻¹) (j : ℤ) :
    (s * x ^ j) * s * (s * x ^ j)⁻¹ = s * x ^ (2 * j) := by
  calc (s * x ^ j) * s * (s * x ^ j)⁻¹ = s * (x ^ j * s * (x ^ j)⁻¹) * s⁻¹ := by group
    _ = s * (s * x ^ (-2 * j)) * s⁻¹ := by rw [zpow_conj_s hsx]
    _ = s * (s * x ^ (-2 * j) * s⁻¹) := by group
    _ = s * x ^ (2 * j) := by rw [(conj_zpow_of_inv hsx _).1, show -(-2 * j) = 2 * j by ring]

theorem innerOn_iff_even [Finite G] {Q : Subgroup G} {x s y : G} (hU : Subgroup.zpowers x ≤ Q)
    (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x)) (hx : orderOf x = 4) (hs : s ∈ Q)
    (hsU : s ∉ Subgroup.zpowers x) (hsx : s * x * s⁻¹ = x⁻¹)
    (hyx : y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) {k : ℤ} (hk : y * s * y⁻¹ = s * x ^ k) :
    InnerOn y Q ↔ Even k := by
  constructor
  · rintro ⟨q, hq, hqv⟩
    have e : q * s * q⁻¹ = s * x ^ k := (hqv s hs).symm.trans hk
    rcases S24B.mem_or_inv_mul_mem hU hcard hs hsU hq with h | h
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
      rw [zpow_conj_s hsx] at e
      exact (even_iff_of_mul_eq hx e).mp ⟨-j, by ring⟩
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
      have hq' : q = s * x ^ j := by rw [hj]; group
      rw [hq', mul_zpow_conj_s hsx] at e
      exact (even_iff_of_mul_eq hx e).mp ⟨j, by ring⟩
  · rintro ⟨i, hi⟩
    rcases hyx with h | h
    · refine ⟨x ^ (-i), hU (Subgroup.zpow_mem_zpowers _ _),
        conj_eq_of_gens hU hcard hs hsU ?_ ?_⟩
      · rw [h, (Commute.zpow_self x (-i)).eq, mul_inv_cancel_right]
      · rw [hk, zpow_conj_s hsx, hi, show -2 * -i = i + i by ring]
    · refine ⟨s * x ^ i, Subgroup.mul_mem _ hs (hU (Subgroup.zpow_mem_zpowers _ _)),
        conj_eq_of_gens hU hcard hs hsU ?_ ?_⟩
      · rw [h]
        calc x⁻¹ = s * x * s⁻¹ := hsx.symm
          _ = s * (x ^ i * x * (x ^ i)⁻¹) * s⁻¹ := by
              rw [(Commute.zpow_self x i).eq, mul_inv_cancel_right]
          _ = s * x ^ i * x * (s * x ^ i)⁻¹ := by group
      · rw [hk, mul_zpow_conj_s hsx, hi, show 2 * i = i + i by ring]

theorem innerOn_of_fix [Finite G] {Q : Subgroup G} {b y : G} (hbQ : b ∈ Q) (hb : orderOf b = 4)
    (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers b))
    (hinvQ : ∀ g ∈ Q, g ∉ Subgroup.zpowers b → g * b * g⁻¹ = b⁻¹)
    (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) (hyy : y * y = 1) (hyb : y * b * y⁻¹ = b) :
    InnerOn y Q := by
  have hU : Subgroup.zpowers b ≤ Q := Subgroup.zpowers_le.mpr hbQ
  obtain ⟨s, hs, hsU⟩ : ∃ s ∈ Q, s ∉ Subgroup.zpowers b := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (fun v hv => hcon v hv : Q ≤ Subgroup.zpowers b)
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers b) := Nat.card_pos
    omega
  obtain ⟨k, hk⟩ := exists_conj_s hU hcard hs hsU hyQ (Or.inl hyb)
  refine (innerOn_iff_even hU hcard hb hs hsU (hinvQ s hs hsU) (Or.inl hyb) hk).mpr ?_
  have hbk : y * b ^ k * y⁻¹ = b ^ k := by rw [← conj_zpow, hyb]
  have e : s * b ^ (k + k) = s * 1 := by
    calc s * b ^ (k + k) = (s * b ^ k) * b ^ k := by rw [zpow_add, mul_assoc]
      _ = (y * s * y⁻¹) * (y * b ^ k * y⁻¹) := by rw [hk, hbk]
      _ = y * (s * b ^ k) * y⁻¹ := by group
      _ = y * (y * s * y⁻¹) * y⁻¹ := by rw [hk]
      _ = (y * y) * s * (y * y)⁻¹ := by group
      _ = s * 1 := by rw [hyy]; group
  have h1 : b ^ (k + k) = 1 := mul_left_cancel e
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hb] at h2
  have h3 : (4 : ℤ) ∣ k + k := by exact_mod_cast h2
  obtain ⟨c, hc⟩ := h3
  exact ⟨c, by omega⟩

theorem exists_fix_of_innerOn {Q : Subgroup G} {x y : G} (hU : Subgroup.zpowers x ≤ Q)
    (hx : orderOf x = 4) (hord : ∀ g ∈ Q, g ∉ Subgroup.zpowers x → orderOf g = 4)
    (h : InnerOn y Q) : ∃ b ∈ Q, orderOf b = 4 ∧ y * b * y⁻¹ = b := by
  obtain ⟨q, hq, hqv⟩ := h
  by_cases hqU : q ∈ Subgroup.zpowers x
  · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hqU
    refine ⟨x, hU (Subgroup.mem_zpowers x), hx, ?_⟩
    rw [hqv x (hU (Subgroup.mem_zpowers x)), (Commute.zpow_self x j).eq, mul_inv_cancel_right]
  · refine ⟨q, hq, hord q hq hqU, ?_⟩
    rw [hqv q hq, mul_inv_cancel_right]

theorem innerOn_of_commute [Finite G] {L Q : Subgroup G} (hQL : IsSylow2In Q L)
    (h8 : Nat.card ↥Q = 8)
    (hinvL : ∀ Q₁ : Subgroup G, IsSylow2In Q₁ L → ∀ b ∈ Q₁, orderOf b = 4 →
      ∀ g ∈ Q₁, g ∉ Subgroup.zpowers b → g * b * g⁻¹ = b⁻¹)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyQ : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q)
    (hyy : y * y = 1) {b : G} (hbL : b ∈ L) (hb : orderOf b = 4) (hyb : y * b = b * y) :
    InnerOn y Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : IsPGroup 2 ↥(Subgroup.zpowers b) := T7A.isPGroup_zpowers_of_orderOf_four hb
  have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) := isPGroup_zpowers_of_mul_self hyy
  have hbN : Subgroup.zpowers b ≤
      Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left hyb j)).eq
  have hX2 := hb2.to_sup_of_normal_right' hy2 hbN
  have hXL : Subgroup.zpowers b ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hbL)) (Subgroup.zpowers_le.mpr hyL)
  obtain ⟨Q₁, hQ₁, hQ₁n⟩ := T3.exists_sylow_normalized hX2 hXL
  have hQ₁N : Subgroup.zpowers b ≤ Subgroup.normalizer (Q₁ : Set G) := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mpr (hQ₁n g (Subgroup.mem_sup_left hg))
  have hbQ₁ : b ∈ Q₁ := by
    have hsup := hb2.to_sup_of_normal_right' hQ₁.2.1 hQ₁N
    have heq := hQ₁.eq_of_le hsup (sup_le (Subgroup.zpowers_le.mpr hbL) hQ₁.1) le_sup_right
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have hyQ₁ : ∀ q ∈ Q₁, y * q * y⁻¹ ∈ Q₁ := fun q hq => by
    have h := hQ₁n y (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    rw [← h]
    exact conj_mem_conjSub hq
  have hcard₁ : Nat.card ↥Q₁ = 2 * Nat.card ↥(Subgroup.zpowers b) := by
    rw [hQ₁.natCard_eq hQL, h8, Nat.card_zpowers, hb]
  have hyb' : y * b * y⁻¹ = b := by rw [hyb, mul_inv_cancel_right]
  obtain ⟨q₁, hq₁, hq₁v⟩ :=
    innerOn_of_fix hbQ₁ hb hcard₁ (hinvL Q₁ hQ₁ b hbQ₁ hb) hyQ₁ hyy hyb'
  obtain ⟨l, hl, hlQ⟩ := AschTight.S1916.IsSylow2In.exists_conj hQ₁ hQL
  obtain ⟨n, hn⟩ : ∃ n, (y * l * y⁻¹) * q₁ * l⁻¹ = n := ⟨_, rfl⟩
  have hnv : ∀ v ∈ Q, y * v * y⁻¹ = n * v * n⁻¹ := by
    intro v hv
    have hv' : l⁻¹ * v * l ∈ Q₁ := by
      rw [← hlQ, mem_conjSub_iff] at hv
      exact hv
    have e := hq₁v _ hv'
    calc y * v * y⁻¹ = (y * l * y⁻¹) * (y * (l⁻¹ * v * l) * y⁻¹) * (y * l * y⁻¹)⁻¹ := by group
      _ = (y * l * y⁻¹) * (q₁ * (l⁻¹ * v * l) * q₁⁻¹) * (y * l * y⁻¹)⁻¹ := by rw [e]
      _ = n * v * n⁻¹ := by rw [← hn]; group
  have hnL : n ∈ L := by
    rw [← hn]
    exact L.mul_mem (L.mul_mem ((Subgroup.mem_normalizer_iff.mp hyL l).mp hl) (hQ₁.1 hq₁))
      (L.inv_mem hl)
  have hnN : n ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      rw [← hnv v hv]
      exact hyQ v hv
    · intro hv
      have h1 : y * (n * v * n⁻¹) * y⁻¹ ∈ Q := hyQ _ hv
      have h2 : n * (y * (n * v * n⁻¹) * y⁻¹) * n⁻¹ = n * v * n⁻¹ := by
        rw [← hnv _ h1]
        calc y * (y * (n * v * n⁻¹) * y⁻¹) * y⁻¹ = (y * y) * (n * v * n⁻¹) * (y * y)⁻¹ := by
              group
          _ = n * v * n⁻¹ := by rw [hyy]; group
      have h3 : y * (n * v * n⁻¹) * y⁻¹ = v := mul_left_cancel (mul_right_cancel h2)
      rw [← h3]
      exact h1
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Subgroup G, L ⊓ Subgroup.normalizer (Q : Set G) = H₁ := ⟨_, rfl⟩
  have hQH₁ : Q ≤ H₁ := hH₁ ▸ le_inf hQL.1 Subgroup.le_normalizer
  have hH₁L : H₁ ≤ L := hH₁ ▸ inf_le_left
  have hH₁N : H₁ ≤ Subgroup.normalizer (Q : Set G) := hH₁ ▸ inf_le_right
  have hnH₁ : n ∈ H₁ := hH₁ ▸ (⟨hnL, hnN⟩ : n ∈ L ⊓ Subgroup.normalizer (Q : Set G))
  have hQS : IsSylow2In Q H₁ := AschTight.S1916.IsSylow2In.of_le hQL hQH₁ hH₁L
  have hNn : (Q.subgroupOf H₁).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hH₁N g.2) a).mp ha⟩
  let P : Sylow 2 ↥H₁ :=
    { toSubgroup := Q.subgroupOf H₁
      isPGroup' := hQS.2.1.comap_subtype
      is_maximal' := by
        intro Q' hQ' hle
        have hVQ : Q ≤ Q'.map H₁.subtype := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hQS.1]
          exact Subgroup.map_mono hle
        have := hQS.2.2 (Q'.map H₁.subtype) (Subgroup.map_subtype_le _) (hQ'.map _) hVQ
        rw [← Subgroup.comap_map_eq_self_of_injective H₁.subtype_injective Q', this]
        rfl }
  have hodd : ¬ 2 ∣ (Q.subgroupOf H₁).index := Sylow.not_dvd_index P
  obtain ⟨j, hj⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hpow := Subgroup.pow_index_mem (Q.subgroupOf H₁) (⟨n, hnH₁⟩ : ↥H₁)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hpow
  have hn2 : ∀ v ∈ Q, n * n * v * (n * n)⁻¹ = v := fun v hv => by
    have h1 : n * v * n⁻¹ ∈ Q := (hnv v hv) ▸ hyQ v hv
    calc n * n * v * (n * n)⁻¹ = n * (n * v * n⁻¹) * n⁻¹ := by group
      _ = y * (n * v * n⁻¹) * y⁻¹ := (hnv _ h1).symm
      _ = y * (y * v * y⁻¹) * y⁻¹ := by rw [hnv v hv]
      _ = (y * y) * v * (y * y)⁻¹ := by group
      _ = v := by rw [hyy]; group
  have hn2k : ∀ m : ℕ, ∀ v ∈ Q, n ^ (2 * m) * v * (n ^ (2 * m))⁻¹ = v := by
    intro m
    induction m with
    | zero => intro v _; simp
    | succ m ih =>
      intro v hv
      have e : n ^ (2 * (m + 1)) = n ^ (2 * m) * (n * n) := by
        rw [Nat.mul_succ, pow_add, pow_two]
      rw [e]
      calc n ^ (2 * m) * (n * n) * v * (n ^ (2 * m) * (n * n))⁻¹
          = n ^ (2 * m) * (n * n * v * (n * n)⁻¹) * (n ^ (2 * m))⁻¹ := by group
        _ = v := by rw [hn2 v hv, ih v hv]
  refine ⟨_, hpow, fun v hv => ?_⟩
  have hv' : n * v * n⁻¹ ∈ Q := (hnv v hv) ▸ hyQ v hv
  rw [hj, pow_succ, hnv v hv]
  calc n * v * n⁻¹ = n ^ (2 * j) * (n * v * n⁻¹) * (n ^ (2 * j))⁻¹ := (hn2k j _ hv').symm
    _ = n ^ (2 * j) * n * v * (n ^ (2 * j) * n)⁻¹ := by group

section Member

variable [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem inv_of_member (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {zL : G} (hzL : IsUniqueInvolution L zL) {Q : Subgroup G} (hQ : IsSylow2In Q L)
    (h8 : Nat.card ↥Q = 8) :
    ∀ Q₁ : Subgroup G, IsSylow2In Q₁ L → ∀ b ∈ Q₁, orderOf b = 4 →
      ∀ g ∈ Q₁, g ∉ Subgroup.zpowers b → g * b * g⁻¹ = b⁻¹ := by
  intro Q₁ hQ₁ b hb ob g hg hgU
  have hquat := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hL hQ₁)
  have hz₁ := AscL62.isUniqueInvolution_of_le hzL hQ₁.1 (T7C.mem_of_isSylow2In hp hΩ hL hQ₁ hzL)
  have hcard : Nat.card ↥Q₁ = 2 * Nat.card ↥(Subgroup.zpowers b) := by
    rw [hQ₁.natCard_eq hQ, h8, Nat.card_zpowers, ob]
  exact AscL62.conj_eq_inv_of_not_mem hquat hz₁ (Subgroup.zpowers_le.mpr hb) inferInstance hcard
    hg hgU (Subgroup.mem_zpowers b)

theorem orderOf_of_member (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {L : Subgroup G} (hL : L ∈ Ω)
    {zL : G} (hzL : IsUniqueInvolution L zL) {Q : Subgroup G} (hQ : IsSylow2In Q L)
    {x : G} (hxQ : x ∈ Q) (hcard : Nat.card ↥Q = 2 * Nat.card ↥(Subgroup.zpowers x)) :
    ∀ g ∈ Q, g ∉ Subgroup.zpowers x → orderOf g = 4 := by
  intro g hg hgU
  have hquat := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hL hQ)
  have hz := AscL62.isUniqueInvolution_of_le hzL hQ.1 (T7C.mem_of_isSylow2In hp hΩ hL hQ hzL)
  have hgg : g * g = zL := AscL62.sq_eq_of_not_mem hquat hz (Subgroup.zpowers_le.mpr hxQ)
    inferInstance hcard hg hgU
  have h4 : orderOf g = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hgg]
      exact hzL.ne_one
    · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hgg]
      exact hzL.sq
  rw [h4]
  norm_num

end Member

end S24

end CFSG.ClassicalInvolution.Asc77
