module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

section Presentation

variable {G : Type*} [Group G] [Finite G] {P : Subgroup G} {p r : G}

theorem not_mem_zpowers_of_presentation (hp : p ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P) : r ∉ zpowers p := by
  intro hr
  have hle : P ≤ zpowers p := by
    rw [← hcl, closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact mem_zpowers _
    · exact hr
  have h1 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, ← hc] at h1
  have h2 : 0 < orderOf p := by
    have := hc ▸ (Nat.card_pos : 0 < Nat.card P)
    omega
  omega

theorem mem_presentation_cases (hp : p ∈ P) (hrP : r ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P) {y : G} (hy : y ∈ P) :
    y ∈ zpowers p ∨ r⁻¹ * y ∈ zpowers p := by
  have hidx : ((zpowers p).subgroupOf P).index = 2 := by
    have h1 := Subgroup.card_mul_index ((zpowers p).subgroupOf P)
    have h2 : Nat.card ((zpowers p).subgroupOf P) = orderOf p := by
      rw [← Subgroup.card_map_of_injective P.subtype_injective, subgroupOf_map_subtype,
        inf_of_le_left (zpowers_le.mpr hp), Nat.card_zpowers]
    have h3 : 0 < orderOf p := by
      have := hc ▸ (Nat.card_pos : 0 < Nat.card P)
      omega
    rw [h2, ← hc] at h1
    have : orderOf p * ((zpowers p).subgroupOf P).index = orderOf p * 2 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left h3 this
  by_cases hyp : y ∈ zpowers p
  · exact Or.inl hyp
  · right
    have hr' : (⟨r⁻¹, inv_mem hrP⟩ : P) ∉ (zpowers p).subgroupOf P := by
      intro h
      apply not_mem_zpowers_of_presentation hp hcl hc
      have := inv_mem (mem_subgroupOf.mp h)
      simpa using this
    have hy' : (⟨y, hy⟩ : P) ∉ (zpowers p).subgroupOf P := fun h => hyp (mem_subgroupOf.mp h)
    have := (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false hr' hy')
    exact mem_subgroupOf.mp this

omit [Finite G] in
theorem sq_r_mul_zpow (hr2 : r ^ 2 = 1) (k : ℤ) :
    (r * p ^ k) ^ 2 = (r * p * r⁻¹) ^ k * p ^ k := by
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hr2])
  rw [conj_zpow, pow_two, hri]
  group

theorem pow_four_r_mul_zpow (hr2 : r ^ 2 = 1)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (h2 : 2 ∣ orderOf p) (k : ℤ) : (r * p ^ k) ^ 4 = 1 := by
  have hsq := sq_r_mul_zpow hr2 (p := p) k
  have h4 : (r * p ^ k) ^ 4 = ((r * p ^ k) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, hsq]
  rcases hrel with h1 | h1
  · rw [h1, inv_zpow, inv_mul_cancel, one_pow]
  · rw [h1]
    obtain ⟨m, hm⟩ := h2
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        rw [mul_zero] at hm
        exact absurd hm (orderOf_pos p).ne'
      · exact h0
    have e1 : (p ^ (orderOf p / 2 - 1)) ^ k * p ^ k = p ^ ((m : ℤ) * k) := by
      rw [← zpow_natCast p, ← zpow_mul, ← zpow_add, hm, show 2 * m / 2 = m by omega]
      congr 1
      push_cast [Nat.cast_sub hm0]
      ring
    rw [e1, ← zpow_natCast, ← zpow_mul]
    have e2 : (m : ℤ) * k * ((2 : ℕ) : ℤ) = (orderOf p : ℤ) * k := by
      rw [hm]; push_cast; ring
    rw [e2, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem orderOf_r_mul_zpow_lt (hr2 : r ^ 2 = 1)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (h4 : 4 ≤ orderOf p) (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) (hnab : r * p * r⁻¹ ≠ p) (k : ℤ) :
    orderOf (r * p ^ k) < orderOf p := by
  obtain ⟨n, hn⟩ := hpow
  have h2 : 2 ∣ orderOf p := by
    rw [hn]
    refine dvd_pow_self 2 ?_
    rintro rfl
    rw [pow_zero] at hn
    omega
  have hdvd : orderOf (r * p ^ k) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one (pow_four_r_mul_zpow hr2 hrel h2 k)
  have hle4 : orderOf (r * p ^ k) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  rcases Nat.lt_or_ge 4 (orderOf p) with h8 | h8
  · omega
  ·
    have hp4 : orderOf p = 4 := le_antisymm h8 h4
    rcases hrel with h1 | h1
    · have hsq := sq_r_mul_zpow hr2 (p := p) k
      rw [h1, inv_zpow, inv_mul_cancel] at hsq
      have : orderOf (r * p ^ k) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · exfalso
      apply hnab
      rw [h1, hp4]
      norm_num

theorem mem_zpowers_of_orderOf_eq (hp : p ∈ P) (hrP : r ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P) (hr2 : r ^ 2 = 1)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (h4 : 4 ≤ orderOf p) (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) (hnab : r * p * r⁻¹ ≠ p)
    {y : G} (hy : y ∈ P) (hyo : orderOf y = orderOf p) : y ∈ zpowers p := by
  rcases mem_presentation_cases hp hrP hcl hc hy with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hy' : y = r * p ^ k := by rw [hk]; group
    have := orderOf_r_mul_zpow_lt hr2 hrel h4 hpow hnab k
    rw [← hy', hyo] at this
    exact lt_irrefl _ this

theorem inf_centralizer_eq_zpowers (hp : p ∈ P) (hrP : r ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P) (hnab : r * p * r⁻¹ ≠ p) :
    P ⊓ centralizer ({p} : Set G) = zpowers p := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyP, hyc⟩ := mem_inf.mp hy
    rcases mem_presentation_cases hp hrP hcl hc hyP with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      have hy' : y = r * p ^ k := by rw [hk]; group
      apply hnab
      have hyp := mem_centralizer_singleton_iff.mp hyc
      rw [hy'] at hyp
      have hpk : p ^ k * p = p * p ^ k := (Commute.zpow_left (Commute.refl p) k).eq
      have hrp : r * p = p * r := by
        have : r * (p ^ k * p) = p * r * p ^ k := by rw [← mul_assoc, hyp]; group
        rw [hpk, ← mul_assoc] at this
        exact mul_right_cancel this
      rw [hrp, mul_inv_cancel_right]
  · rw [zpowers_le]
    exact mem_inf.mpr ⟨hp, mem_centralizer_singleton_iff.mpr rfl⟩

omit [Finite G] in
theorem involution_mem_center (hcl : closure {p, r} = P)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (h4 : 4 ≤ orderOf p) (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) :
    ∀ y ∈ P, y * p ^ (orderOf p / 2) = p ^ (orderOf p / 2) * y := by
  obtain ⟨n, hn⟩ := hpow
  have h2 : 2 ∣ orderOf p := by
    rw [hn]
    refine dvd_pow_self 2 ?_
    rintro rfl
    rw [pow_zero] at hn
    omega
  obtain ⟨m, hm⟩ := h2
  set p₀ := p ^ (orderOf p / 2) with hp₀
  have hp0sq : p₀ * p₀ = 1 := by
    rw [hp₀, ← pow_add, show orderOf p / 2 + orderOf p / 2 = orderOf p by omega,
      pow_orderOf_eq_one]
  have hp0inv : p₀⁻¹ = p₀ := inv_eq_of_mul_eq_one_right hp0sq
  have hr : r * p₀ * r⁻¹ = p₀ := by
    rw [hp₀, ← conj_pow]
    rcases hrel with h1 | h1
    · rw [h1, inv_pow, ← hp₀, hp0inv]
    · rw [h1, ← pow_mul, mul_comm, pow_mul, ← hp₀]
      have hodd : Odd (orderOf p / 2 - 1) := by
        have h1 : 2 * m = 2 ^ n := hm ▸ hn
        have hn2 : 2 ≤ n := by
          by_contra hlt
          push Not at hlt
          interval_cases n <;> omega
        have hm2 : m = 2 * 2 ^ (n - 2) := by
          have : 2 ^ n = 2 * (2 * 2 ^ (n - 2)) := by
            rw [← pow_succ', ← pow_succ']
            congr 1
            omega
          omega
        rw [show orderOf p / 2 = m by omega, hm2]
        exact Nat.Even.sub_odd (by have := Nat.one_le_two_pow (n := n - 2); omega)
          (even_two_mul _) odd_one
      obtain ⟨j, hj⟩ := hodd
      rw [hj, pow_succ, pow_mul, show p₀ ^ 2 = 1 by rw [pow_two, hp0sq], one_pow, one_mul]
  have hle : P ≤ centralizer ({p₀} : Set G) := by
    rw [← hcl, closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff, hp₀, ← pow_succ, ← pow_succ']
    · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      calc y * p₀ = (y * p₀ * y⁻¹) * y := by group
        _ = p₀ * y := by rw [hr]
  intro y hy
  exact mem_centralizer_singleton_iff.mp (hle hy)

end Presentation

theorem commutator_mem_centralizer_of_normalizes {G : Type*} [Group G] {p s t : G}
    (hs : ∀ y : G, y ∈ ({s, s⁻¹} : Set G) → y * p * y⁻¹ ∈ zpowers p)
    (ht : ∀ y : G, y ∈ ({t, t⁻¹} : Set G) → y * p * y⁻¹ ∈ zpowers p) :
    ⁅s, t⁆ ∈ centralizer ({p} : Set G) := by
  obtain ⟨δ, hδ⟩ := mem_zpowers_iff.mp (hs s (Set.mem_insert _ _))
  obtain ⟨β, hβ⟩ := mem_zpowers_iff.mp (hs s⁻¹ (Set.mem_insert_of_mem _ rfl))
  obtain ⟨γ, hγ⟩ := mem_zpowers_iff.mp (ht t (Set.mem_insert _ _))
  obtain ⟨α, hα⟩ := mem_zpowers_iff.mp (ht t⁻¹ (Set.mem_insert_of_mem _ rfl))
  rw [inv_inv] at hβ hα
  have hs' : p ^ (β * δ) = p := by
    calc p ^ (β * δ) = (p ^ δ) ^ β := by rw [← zpow_mul, mul_comm]
      _ = (s * p * s⁻¹) ^ β := by rw [hδ]
      _ = s * p ^ β * s⁻¹ := by rw [conj_zpow]
      _ = s * (s⁻¹ * p * s) * s⁻¹ := by rw [hβ]
      _ = p := by group
  have ht' : p ^ (α * γ) = p := by
    calc p ^ (α * γ) = (p ^ γ) ^ α := by rw [← zpow_mul, mul_comm]
      _ = (t * p * t⁻¹) ^ α := by rw [hγ]
      _ = t * p ^ α * t⁻¹ := by rw [conj_zpow]
      _ = t * (t⁻¹ * p * t) * t⁻¹ := by rw [hα]
      _ = p := by group
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  have key : (s * t * s⁻¹ * t⁻¹) * p * (s * t * s⁻¹ * t⁻¹)⁻¹ = p := by
    calc (s * t * s⁻¹ * t⁻¹) * p * (s * t * s⁻¹ * t⁻¹)⁻¹
        = s * (t * (s⁻¹ * (t⁻¹ * p * t) * s) * t⁻¹) * s⁻¹ := by group
      _ = s * (t * (s⁻¹ * p ^ α * s) * t⁻¹) * s⁻¹ := by rw [← hα]
      _ = s * (t * (s⁻¹ * p * s) ^ α * t⁻¹) * s⁻¹ := by
          rw [show s⁻¹ * p ^ α * s = (s⁻¹ * p * s⁻¹⁻¹) ^ α by rw [conj_zpow, inv_inv]]
          rw [inv_inv]
      _ = s * (t * (p ^ β) ^ α * t⁻¹) * s⁻¹ := by rw [← hβ]
      _ = s * (t * p * t⁻¹) ^ (β * α) * s⁻¹ := by rw [← zpow_mul, conj_zpow]
      _ = s * (p ^ γ) ^ (β * α) * s⁻¹ := by rw [hγ]
      _ = (s * p * s⁻¹) ^ (γ * (β * α)) := by rw [← zpow_mul, conj_zpow]
      _ = (p ^ δ) ^ (γ * (β * α)) := by rw [hδ]
      _ = (p ^ (β * δ)) ^ (α * γ) := by rw [← zpow_mul, ← zpow_mul]; ring_nf
      _ = p := by rw [hs', ht']
  calc s * t * s⁻¹ * t⁻¹ * p = ((s * t * s⁻¹ * t⁻¹) * p * (s * t * s⁻¹ * t⁻¹)⁻¹) *
        (s * t * s⁻¹ * t⁻¹) := by group
    _ = p * (s * t * s⁻¹ * t⁻¹) := by rw [key]

theorem mem_zpowers_half_of_sq_eq_one {G : Type*} [Group G] {c u : G} (hc2 : 2 ∣ orderOf c)
    (hu : u ∈ zpowers c) (hu2 : u ^ 2 = 1) :
    u ∈ zpowers (c ^ (orderOf c / 2)) := by
  obtain ⟨m, hm⟩ := hc2
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
  have h1 : c ^ (2 * k) = 1 := by rw [mul_comm, zpow_mul]; exact_mod_cast hu2
  rw [← orderOf_dvd_iff_zpow_eq_one, hm] at h1
  push_cast at h1
  obtain ⟨j, hj⟩ := (mul_dvd_mul_iff_left (show (2 : ℤ) ≠ 0 by norm_num)).mp h1
  rw [hm, show 2 * m / 2 = m by omega, hj, zpow_mul, zpow_natCast]
  exact zpow_mem (mem_zpowers _) j

theorem eq_of_orderOf_eq_two_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {w w' : C} (hw : orderOf w = 2) (hw' : orderOf w' = 2) : w = w' := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have h1 : w ≠ 1 := fun h => by rw [h, orderOf_one] at hw; exact absurd hw (by norm_num)
  have h1' : w' ≠ 1 := fun h => by rw [h, orderOf_one] at hw'; exact absurd hw' (by norm_num)
  have hsub : ({1, w, w'} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · exact one_pow 2
    · rw [← hw, pow_orderOf_eq_one]
    · rw [← hw', pow_orderOf_eq_one]
  have hcard : ({1, w, w'} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm h1, Ne.symm h1']),
      Finset.card_pair hne]
  have := Finset.card_le_card hsub
  omega

theorem isCyclic_of_not_mem_involution {m : ℕ}
    {Y : Subgroup (Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m)))}
    {u : Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m))} (hu : orderOf u = 2)
    (huY : u ∉ Y) : IsCyclic Y := by
  set e₁ : Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m)) :=
    (Multiplicative.ofAdd 1, 1) with he₁
  have hZ2 : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by
    intro x
    have : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases this (Multiplicative.toAdd x) with h | h
    · left; rw [← ofAdd_toAdd x, h, ofAdd_zero]
    · right; rw [← ofAdd_toAdd x, h]
  have hfst : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod (2 ^ m)), y.2 = 1 →
      y = 1 ∨ y = e₁ := by
    intro y hy2
    rcases hZ2 y.1 with h | h
    · left; ext <;> simp [h, hy2]
    · right; ext <;> simp [h, hy2, he₁]
  by_cases he : e₁ ∈ Y
  ·
    refine isCyclic_of_injective ((MonoidHom.fst _ _).comp Y.subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨y, hy⟩ hker
    have hy1 : y.1 = 1 := hker
    by_contra hne
    have hy2 : y.2 ≠ 1 := by
      intro h2
      apply hne
      rw [mem_bot]
      apply Subtype.ext
      ext <;> simp [hy1, h2]
    have hu2 : orderOf u.2 = 2 := by
      have hsq : u.2 ^ 2 = 1 := by
        have h1 := pow_orderOf_eq_one u
        rw [hu] at h1
        have := congrArg Prod.snd h1
        simpa using this
      apply orderOf_eq_prime hsq
      intro h2
      rcases hfst u h2 with h | h
      · rw [h, orderOf_one] at hu; exact absurd hu (by norm_num)
      · exact huY (h ▸ he)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, orderOf y.2 = 2 ^ j := by
      have hd : orderOf y.2 ∣ 2 ^ m := by
        have := orderOf_dvd_natCard y.2
        rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
      exact (Nat.dvd_prime_pow Nat.prime_two).mp hd |>.imp fun _ h => h.2
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hy2 hj
    have hw : orderOf (y.2 ^ 2 ^ (j - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (by positivity) (hj ▸ pow_dvd_pow 2 (Nat.sub_le j 1)), hj,
        Nat.pow_div (Nat.sub_le j 1) (by norm_num), show j - (j - 1) = 1 by omega, pow_one]
    have hw' : y.2 ^ 2 ^ (j - 1) = u.2 := eq_of_orderOf_eq_two_of_isCyclic hw hu2
    have hwY : y ^ 2 ^ (j - 1) ∈ Y := pow_mem hy _
    rcases hZ2 u.1 with h1 | h1
    · apply huY
      have : u = y ^ 2 ^ (j - 1) := by
        ext
        · simp [h1, hy1]
        · simp [← hw']
      rw [this]
      exact hwY
    · apply huY
      have : u = e₁ * y ^ 2 ^ (j - 1) := by
        ext
        · simp [h1, hy1, he₁]
        · simp [he₁, ← hw']
      rw [this]
      exact mul_mem he hwY
  ·
    refine isCyclic_of_injective ((MonoidHom.snd _ _).comp Y.subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨y, hy⟩ hker
    have hy2 : y.2 = 1 := hker
    rcases hfst y hy2 with h | h
    · rw [mem_bot]; exact Subtype.ext h
    · exact absurd (h ▸ hy) he

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem presentation_of_index_two (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (h8 : 8 ≤ Nat.card h.P) :
    ∃ p r : H, p ∈ h.P ∧ r ∈ h.P ∧ closure {p, r} = h.P ∧ 2 * orderOf p = Nat.card h.P ∧
      r ^ 2 = 1 ∧ (r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1)) ∧
      (∀ s ∈ h.S, s * p * s⁻¹ ∈ zpowers p) ∧ h.P ⊓ centralizer ({p} : Set H) = zpowers p ∧
      p ^ (orderOf p / 2) = h.a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hBb, hb, hT4, hTab, hTC⟩ := h.index_two_structure hB7 hT
  obtain ⟨p, r, hp, hrP, hcl, hc, hr2, hrel⟩ := h.dihedral_of_index_two hB7 hST hT h8
  have hbP : b ∈ h.P := h.toHyp52.B_le_P (hBb ▸ mem_zpowers b)
  have hbS : b ∈ h.S := h.toHyp52.P_le_S hbP
  have hab : h.a * b = b * h.a := (h.toHyp52.comm_a hbS).symm
  have hP2 : IsPGroup 2 ↥h.P := h.toHyp52.isPGroup_S.to_le h.toHyp52.P_le_S
  have hbZ : ¬ ∀ y ∈ h.P, y * b = b * y := by
    intro hall
    have : h.P ≤ h.T := by
      rw [hTC]
      exact fun y hy => mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr (hall y hy)⟩
    have := Subgroup.card_le_of_le this
    omega
  have hnab : r * p * r⁻¹ ≠ p := by
    intro he
    have hrp : r * p = p * r := by
      calc r * p = (r * p * r⁻¹) * r := by group
        _ = p * r := by rw [he]
    apply hbZ
    intro y hy
    have hpair : ({p, r} : Set H).Pairwise Commute := by
      intro x hx z hz _
      rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
      · exact Commute.refl _
      · exact hrp.symm
      · exact hrp
      · exact Commute.refl _
    have hcm := Subgroup.isMulCommutative_closure hpair
    rw [← hcl] at hy hbP
    have := hcm.is_comm.comm (⟨y, hy⟩ : closure ({p, r} : Set H)) ⟨b, hbP⟩
    exact congrArg Subtype.val this
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨p, hp⟩
  rw [Subgroup.orderOf_mk] at hn
  have h4 : 4 ≤ orderOf p := by omega
  have hpow : ∃ n : ℕ, orderOf p = 2 ^ n := ⟨n, hn⟩
  refine ⟨p, r, hp, hrP, hcl, hc, hr2, hrel, fun s hs => ?_,
    inf_centralizer_eq_zpowers hp hrP hcl hc hnab, ?_⟩
  ·
    have hsp : s * p * s⁻¹ ∈ h.P := h.toHyp52.conj_mem_P hs hp
    have ho : orderOf (s * p * s⁻¹) = orderOf p := by
      rw [show s * p * s⁻¹ = (MulAut.conj s) p by rw [MulAut.conj_apply], MulEquiv.orderOf_eq]
    exact mem_zpowers_of_orderOf_eq hp hrP hcl hc hr2 hrel h4 hpow hnab hsp ho
  ·
    set p₀ := p ^ (orderOf p / 2) with hp₀
    have hcen := involution_mem_center hcl hrel h4 hpow
    have hp₀T : p₀ ∈ h.T := by
      rw [hTC]
      exact mem_inf.mpr ⟨pow_mem hp _, mem_centralizer_singleton_iff.mpr (hcen b hbP).symm⟩
    have hp₀1 : p₀ ≠ 1 := by
      rw [hp₀]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    rcases h.mem_T_cases hb hTab hab hp₀T with h1 | h1 | h1 | h1
    · exact absurd h1 hp₀1
    · exact h1
    · exfalso
      apply hbZ
      intro y hy
      rw [← h1]
      exact hcen y hy
    · exfalso
      apply hbZ
      intro y hy
      have h2 := hcen y hy
      rw [← hp₀, h1] at h2
      have h3 : y * h.a = h.a * y := h.toHyp52.comm_a (h.toHyp52.P_le_S hy)
      have h4 : h.a * (y * b) = h.a * (b * y) := by
        calc h.a * (y * b) = (y * h.a) * b := by rw [h3]; group
          _ = y * (h.a * b) := by group
          _ = (h.a * b) * y := h2
          _ = h.a * (b * y) := by group
      exact mul_left_cancel h4

theorem commutator_conclusions {d c : H} (hd : d ∈ h.D) (hdn : ∀ s ∈ h.S, s * d * s⁻¹ ∈ zpowers d)
    (hc : c ∈ h.P) (hc2 : 2 ∣ orderOf c) (hca : c ^ (orderOf c / 2) = h.a)
    (hDP : h.D ⊓ h.P = ⊥) (hle : ⁅h.S, h.S⁆ ≤ zpowers d ⊔ zpowers c) :
    (∀ u ∈ ⁅h.S, h.S⁆, ∀ v ∈ ⁅h.S, h.S⁆, u * v = v * u) ∧ ⁅h.S, h.S⁆ ≤ h.D ⊔ h.P ∧
      ∃ z : H, orderOf z = 2 ∧ z ∈ h.D ∧ z ∈ centralizer (h.S : Set H) ∧
        ∀ u ∈ ⁅h.S, h.S⁆, orderOf u = 2 → u ∈ closure {z, h.a} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdc : d * c = c * d := h.toHyp52.D_comm_P hd hc
  have hX : zpowers d ⊔ zpowers c = closure {d, c} := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
  have hpair : ({d, c} : Set H).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hdc
    · exact hdc.symm
    · exact Commute.refl _
  have hcm := Subgroup.isMulCommutative_closure hpair
  refine ⟨fun u hu v hv => ?_, hle.trans (sup_le (zpowers_le.mpr (mem_sup_left hd))
    (zpowers_le.mpr (mem_sup_right hc))), ?_⟩
  · have hu' := hX ▸ hle hu
    have hv' := hX ▸ hle hv
    exact congrArg Subtype.val (hcm.is_comm.comm (⟨u, hu'⟩ : closure ({d, c} : Set H)) ⟨v, hv'⟩)
  ·
    have hdS : d ∈ h.S := h.toHyp52.D_le_S hd
    obtain ⟨z, hzD, hzS, hz2, hzd⟩ : ∃ z : H, z ∈ h.D ∧ (∀ s ∈ h.S, s * z = z * s) ∧
        orderOf z = 2 ∧ ∀ w ∈ zpowers d, w ^ 2 = 1 → w ∈ zpowers z := by
      by_cases hd1 : d = 1
      · obtain ⟨z, hzD, hzS, hz2⟩ := h.toHyp52.exists_involution_D_center
        refine ⟨z, hzD, hzS, hz2, fun w hw _ => ?_⟩
        rw [hd1, zpowers_one_eq_bot, mem_bot] at hw
        rw [hw]
        exact one_mem _
      · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.toHyp52.isPGroup_S) ⟨d, hdS⟩
        rw [Subgroup.orderOf_mk] at hn
        have hn0 : n ≠ 0 := by
          rintro rfl
          rw [pow_zero, orderOf_eq_one_iff] at hn
          exact hd1 hn
        have hd2 : 2 ∣ orderOf d := by rw [hn]; exact dvd_pow_self 2 hn0
        set z := d ^ (orderOf d / 2) with hz
        have hz2 : orderOf z = 2 := by
          obtain ⟨m, hm⟩ := hd2
          have hm0 : m ≠ 0 := by
            rintro rfl
            rw [mul_zero] at hm
            exact absurd hm (orderOf_pos d).ne'
          rw [hz, hm, show 2 * m / 2 = m by omega, orderOf_pow' _ hm0, hm,
            Nat.gcd_eq_right (dvd_mul_left m 2), Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
        refine ⟨z, pow_mem hd _, fun s hs => ?_, hz2,
          fun w hw hw2 => mem_zpowers_half_of_sq_eq_one hd2 hw hw2⟩
        have h1 : s * z * s⁻¹ ∈ zpowers d := by
          rw [hz, ← conj_pow]
          exact pow_mem (hdn s hs) _
        have h2 : (s * z * s⁻¹) ^ 2 = 1 := by
          rw [conj_pow, ← hz2, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
        have h3 := mem_zpowers_half_of_sq_eq_one hd2 h1 h2
        rw [← hz] at h3
        have h4 : s * z * s⁻¹ ≠ 1 := by
          intro he
          have : z = 1 := by
            calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
              _ = 1 := by rw [he]; group
          rw [this, orderOf_one] at hz2
          exact absurd hz2 (by norm_num)
        have h5 := eq_of_mem_zpowers_of_orderOf_eq_two hz2 h3 h4
        calc s * z = (s * z * s⁻¹) * s := by group
          _ = z * s := by rw [h5]
    refine ⟨z, hz2, hzD, mem_centralizer_iff.mpr fun s hs => hzS s hs, fun u hu hu2 => ?_⟩
    have hu' := hle hu
    have hmem : u ∈ (zpowers d : Set H) * (zpowers c : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (zpowers_le.mpr
        (centralizer_le_normalizer _ (by
          rw [mem_centralizer_iff]
          intro y hy
          obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
          exact (Commute.zpow_left (show Commute c d from hdc.symm) k).eq)))]
      exact hu'
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Set.mem_mul.mp hmem
    have hcomm : u₁ * u₂ = u₂ * u₁ := by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu₁
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hu₂
      exact ((Commute.zpow_left hdc i).zpow_right j).eq
    have hsq : (u₁ * u₂) ^ 2 = 1 := by rw [← hu2, pow_orderOf_eq_one]
    have hu12 : u₁ ^ 2 = (u₂ ^ 2)⁻¹ := by
      rw [(show Commute u₁ u₂ from hcomm).mul_pow] at hsq
      exact eq_inv_of_mul_eq_one_left hsq
    have hint : u₁ ^ 2 ∈ h.D ⊓ h.P := mem_inf.mpr ⟨pow_mem ((zpowers_le.mpr hd) hu₁) _, by
      rw [hu12]; exact inv_mem (pow_mem ((zpowers_le.mpr hc) hu₂) _)⟩
    rw [hDP, mem_bot] at hint
    have hu22 : u₂ ^ 2 = 1 := by
      rw [hint] at hu12
      exact inv_eq_one.mp hu12.symm
    have h1 := hzd u₁ hu₁ hint
    have h2 := mem_zpowers_half_of_sq_eq_one hc2 hu₂ hu22
    rw [hca] at h2
    have hcl : zpowers z ⊔ zpowers h.a ≤ closure {z, h.a} := by
      rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union, Set.singleton_union]
    exact hcl (mul_mem (mem_sup_left h1) (mem_sup_right h2))

theorem commutator_le_of_card_ge {d p : H} (hd : d ∈ h.D)
    (hdle : ⁅h.S, h.S⁆ ≤ zpowers d ⊔ h.P) (hp : p ∈ h.P)
    (hpn : ∀ s ∈ h.S, s * p * s⁻¹ ∈ zpowers p) (hpc : h.P ⊓ centralizer ({p} : Set H) = zpowers p) :
    ⁅h.S, h.S⁆ ≤ zpowers d ⊔ zpowers p := by
  have hcen : ⁅h.S, h.S⁆ ≤ centralizer ({p} : Set H) := by
    rw [commutator_le]
    intro s hs t ht
    refine commutator_mem_centralizer_of_normalizes (fun y hy => ?_) (fun y hy => ?_)
    · rcases hy with rfl | rfl
      · exact hpn _ hs
      · exact hpn _ (inv_mem hs)
    · rcases hy with rfl | rfl
      · exact hpn _ ht
      · exact hpn _ (inv_mem ht)
  intro y hy
  have hy1 := hdle hy
  have hdN : zpowers d ≤ normalizer (h.P : Set H) := zpowers_le.mpr (by
    apply mem_normalizer_of_conj_mem
    · intro x hx; exact h.toHyp52.conj_mem_P (h.toHyp52.D_le_S hd) hx
    · intro x hx
      have := h.toHyp52.conj_mem_P (inv_mem (h.toHyp52.D_le_S hd)) hx
      rwa [inv_inv] at this)
  have hmem : y ∈ (zpowers d : Set H) * (h.P : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hdN]
    exact hy1
  obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hmem
  have hup : u ∈ centralizer ({p} : Set H) := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    rw [mem_centralizer_singleton_iff]
    exact ((Commute.zpow_left (show Commute d p from h.toHyp52.D_comm_P hd hp) k)).eq
  have hqp : q ∈ h.P ⊓ centralizer ({p} : Set H) := by
    refine mem_inf.mpr ⟨hq, ?_⟩
    have := mul_mem (inv_mem hup) (hcen hy)
    rwa [inv_mul_cancel_left] at this
  rw [hpc] at hqp
  exact mul_mem (mem_sup_left hu) (mem_sup_right hqp)

end Hyp59

end CFSG.ComponentClassification.GSThmB
