module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic2

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

section Elementary

variable {G : Type*} [Group G]

theorem cyc_inv_unique [Finite G] {C : Subgroup G} (hC : IsCyclic ↥C) {b b' : G}
    (hb : b ∈ C) (hb' : b' ∈ C) (h2 : b * b = 1) (h2' : b' * b' = 1) (h1 : b ≠ 1) (h1' : b' ≠ 1) :
    b = b' := by
  classical
  have : Fintype ↥C := Fintype.ofFinite _
  by_contra hne
  have hcard := IsCyclic.card_pow_eq_one_le (α := ↥C) (n := 2) (by norm_num)
  have hsub : ({1, (⟨b, hb⟩ : ↥C), (⟨b', hb'⟩ : ↥C)} : Finset ↥C) ⊆
      (Finset.univ.filter (fun a : ↥C => a ^ 2 = 1)) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · apply Subtype.ext
      simpa [pow_two] using h2
    · apply Subtype.ext
      simpa [pow_two] using h2'
  have h3 : ({1, (⟨b, hb⟩ : ↥C), (⟨b', hb'⟩ : ↥C)} : Finset ↥C).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, ⟨b, hb⟩, ⟨b', hb'⟩, ?_, ?_, ?_, rfl⟩
    · intro h; apply h1; simpa using (congrArg Subtype.val h).symm
    · intro h; apply h1'; simpa using (congrArg Subtype.val h).symm
    · intro h; apply hne; simpa using congrArg Subtype.val h
  have := Finset.card_le_card hsub
  omega

theorem relIndex_eq_two_of_mul {H T : Subgroup G} {s₀ : G} (hs₀ : s₀ ∈ T) (hs₀H : s₀ ∉ H)
    (hdich : ∀ b ∈ T, b ∉ H → b * s₀ ∈ H) : H.relIndex T = 2 := by
  have hidx : (H.subgroupOf T).index = 2 := by
    refine Subgroup.index_eq_two_iff.2 ⟨⟨s₀, hs₀⟩, fun b => ?_⟩
    have hbT : (b : G) ∈ T := b.2
    by_cases hb : (b : G) ∈ H
    · right
      refine ⟨hb, fun hba => ?_⟩
      have hba' : (b : G) * s₀ ∈ H := hba
      apply hs₀H
      have e : s₀ = (b : G)⁻¹ * ((b : G) * s₀) := by group
      rw [e]
      exact mul_mem (inv_mem hb) hba'
    · left
      exact ⟨hdich b hbT hb, hb⟩
  exact hidx

theorem mul_self_mem_of_relIndex_two {H T : Subgroup G} (hi : H.relIndex T = 2) {a : G} (ha : a ∈ T) :
    a * a ∈ H := by
  by_cases haH : a ∈ H
  · exact mul_mem haH haH
  · have h1 := mul_inv_mem_of_relIndex_two hi ha (inv_mem ha) haH (fun h => haH (by simpa using inv_mem h))
    simpa using h1

theorem le_normalizer_of_commute' {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h : b * x * b⁻¹ = x := by rw [← hc x hx b hb]; group
    rwa [h]
  · intro hx
    have hcomm := hc _ hx b hb
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hcomm]
        _ = b * x * b⁻¹ := by group
    rwa [this]

theorem card_sup_mul_card_inf' {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  set M := B ⊔ A with hM
  have hBM : B ≤ M := le_sup_left
  have hAM : A ≤ M := le_sup_right
  have : (A.subgroupOf M).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have hsup : B.subgroupOf M ⊔ A.subgroupOf M = ⊤ :=
    codisjoint_iff.1 (Subgroup.codisjoint_subgroupOf_sup B A)
  have h1 := Subgroup.relIndex_sup_right (H := B.subgroupOf M) (K := A.subgroupOf M)
  rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hBM] at h1
  have h2 := Subgroup.card_mul_index (A.subgroupOf M)
  have h3 : Nat.card ↥(A.subgroupOf M) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [h1, h3] at h2
  have h4 := Subgroup.relIndex_mul_card A B
  rw [sup_comm] at hM
  rw [← hM, ← h2, mul_assoc, h4]

theorem relIndex_two_pigeon {X H : Subgroup G} (hH : H.relIndex X = 2) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) : x ∈ H ∨ y ∈ H ∨ x⁻¹ * y ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hH
  have hN : (H.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
  by_contra hcon
  push Not at hcon
  obtain ⟨hxH, hyH, hxy⟩ := hcon
  have hx' : (⟨x, hx⟩ : ↥X) ∉ H.subgroupOf X := hxH
  have hy' : (⟨y, hy⟩ : ↥X) ∉ H.subgroupOf X := hyH
  have hxy' : (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ ∉ H.subgroupOf X := hxy
  have h3 : (⟨x, hx⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases ha ⟨x, hx⟩ with h | h
    · exact h.1
    · exact absurd h.1 hx'
  have h4 : (⟨y, hy⟩ : ↥X) * a ∈ H.subgroupOf X := by
    rcases ha ⟨y, hy⟩ with h | h
    · exact h.1
    · exact absurd h.1 hy'
  have h5 : ((⟨x, hx⟩ : ↥X) * a)⁻¹ * ((⟨y, hy⟩ : ↥X) * a) ∈ H.subgroupOf X :=
    (H.subgroupOf X).mul_mem ((H.subgroupOf X).inv_mem h3) h4
  have h6 : a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹ ∈ H.subgroupOf X := by
    have e : ((⟨x, hx⟩ : ↥X) * a)⁻¹ * ((⟨y, hy⟩ : ↥X) * a) =
        a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹ := by group
    rw [← e]; exact h5
  have h7 := hN.conj_mem _ h6 a
  have e2 : a * (a⁻¹ * ((⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩) * a⁻¹⁻¹) * a⁻¹ =
      (⟨x, hx⟩ : ↥X)⁻¹ * ⟨y, hy⟩ := by group
  rw [e2] at h7
  exact hxy' h7

theorem conj_mem_of_relIndex_two {X H : Subgroup G} (hH : H.relIndex X = 2) {x h : G} (hx : x ∈ X)
    (hh : h ∈ H) (hHX : H ≤ X) : x * h * x⁻¹ ∈ H := by
  have h2 : (H.subgroupOf X).index = 2 := hH
  have hN : (H.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
  have h1 : (⟨h, hHX hh⟩ : ↥X) ∈ H.subgroupOf X := hh
  exact hN.conj_mem _ h1 ⟨x, hx⟩

theorem mem_normalizer_of_invol {A : Subgroup G} {g : G} (hg : g * g = 1)
    (hN : ∀ p ∈ A, g * p * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set G) := by
  have hg1 : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [Subgroup.mem_normalizer_iff]
  intro p
  refine ⟨hN p, fun hp => ?_⟩
  have := hN _ hp
  have e : g * (g * p * g⁻¹) * g⁻¹ = p := by
    calc g * (g * p * g⁻¹) * g⁻¹ = (g * g) * p * (g⁻¹ * g⁻¹) := by group
      _ = p := by rw [hg1, hg]; group
  rwa [e] at this

theorem mem_zpowers_of_sq' {x y : G} (hx : x * x = 1) :
    y ∈ Subgroup.zpowers x ↔ y = 1 ∨ y = x := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk2 with h0 | h1
    · left
      rw [hk, h0, add_zero, zpow_mul, hx2, one_zpow]
    · right
      rw [hk, h1, zpow_add, zpow_mul, hx2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

theorem g2shape_abstract [Finite G] {A S : Subgroup G} {a t y z u : G} {m : ℕ}
    (hAc : ∀ p ∈ A, ∀ q ∈ A, p * q = q * p)
    (haA : a ∈ A) (hord : orderOf a = 2 ^ (m + 1))
    (ht2 : t * t = 1) (hy2 : y * y = 1) (hty : t * y = y * t)
    (htN : ∀ p ∈ A, t * p * t⁻¹ ∈ A) (hyN : ∀ p ∈ A, y * p * y⁻¹ ∈ A)
    (hyinv : ∀ p ∈ A, y * p * y = p⁻¹)
    (hu : u = a ^ (2 ^ m)) (htu : t⁻¹ * u * t = u * z) (hz : z ≠ 1)
    (hAcard : Nat.card ↥A = 2 ^ (m + 1) * 2 ^ (m + 1)) (hAS : A ≤ S)
    (hSc : Nat.card ↥S = 4 * Nat.card ↥A)
    (htS : t ∈ S) (hyS : y ∈ S) (htA : t ∉ A) (hyA : y ∉ A) (htyA : t * y ∉ A) :
    orderOf a = 2 ^ (m + 1) ∧ A = Subgroup.zpowers a ⊔ Subgroup.zpowers (t⁻¹ * a * t) ∧
      Subgroup.zpowers a ⊓ Subgroup.zpowers (t⁻¹ * a * t) = ⊥ ∧
      a * (t⁻¹ * a * t) = (t⁻¹ * a * t) * a ∧
      t * t = 1 ∧ y * y = 1 ∧ t * y = y * t ∧ t ≠ 1 ∧ y ≠ 1 ∧ t ≠ y ∧
      A ⊓ (Subgroup.zpowers t ⊔ Subgroup.zpowers y) = ⊥ ∧ (∀ x ∈ A, y * x * y = x⁻¹) ∧
      S = A ⊔ Subgroup.zpowers t ⊔ Subgroup.zpowers y := by
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hat : t⁻¹ * a * t ∈ A := by
    have := htN a haA
    rw [ht1] at this ⊢
    exact this
  have hcomm : a * (t⁻¹ * a * t) = (t⁻¹ * a * t) * a := hAc a haA _ hat
  have hord' : orderOf (t⁻¹ * a * t) = 2 ^ (m + 1) := by
    have h1 := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective a
    have e : (MulAut.conj t⁻¹).toMonoidHom a = t⁻¹ * a * t := by simp
    rw [e] at h1
    rw [h1, hord]
  have hcpow : ∀ n : ℕ, (t⁻¹ * a * t) ^ n = t⁻¹ * a ^ n * t := by
    intro n
    have := conj_pow (a := t⁻¹) (b := a) (i := n)
    rwa [inv_inv] at this
  have hu2 : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, ← pow_succ']
    exact hord ▸ pow_orderOf_eq_one a
  have hu1 : u ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one (hu ▸ h)
    rw [hord] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hu'2 : (t⁻¹ * u * t) * (t⁻¹ * u * t) = 1 := by
    calc (t⁻¹ * u * t) * (t⁻¹ * u * t) = t⁻¹ * (u * u) * t := by group
      _ = 1 := by rw [hu2]; group
  have hu'1 : t⁻¹ * u * t ≠ 1 := by
    intro h
    apply hu1
    have e : u = t * (t⁻¹ * u * t) * t⁻¹ := by group
    rw [e, h]; group
  have hua : u ∈ Subgroup.zpowers a := by rw [hu]; exact Subgroup.npow_mem_zpowers a _
  have hua' : t⁻¹ * u * t ∈ Subgroup.zpowers (t⁻¹ * a * t) := by
    rw [hu, ← hcpow]; exact Subgroup.npow_mem_zpowers _ _
  have hbot : Subgroup.zpowers a ⊓ Subgroup.zpowers (t⁻¹ * a * t) = ⊥ := by
    by_contra hne
    set H := Subgroup.zpowers a ⊓ Subgroup.zpowers (t⁻¹ * a * t) with hH
    have hcardA : Nat.card ↥(Subgroup.zpowers a) = 2 ^ (m + 1) := by rw [Nat.card_zpowers, hord]
    have hdvd : Nat.card ↥H ∣ 2 ^ (m + 1) := by
      rw [← hcardA]; exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, -, hHj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hHj
      exact hne (Subgroup.card_eq_one.1 hHj)
    have h2dvd : 2 ∣ Nat.card ↥H := by rw [hHj]; exact dvd_pow_self 2 hj0
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hb2 : (x : G) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    have hb1 : (x : G) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      omega
    have hbH : (x : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers (t⁻¹ * a * t) := x.2
    have e1 : (x : G) = u :=
      cyc_inv_unique (Subgroup.isCyclic_zpowers a) hbH.1 hua hb2 hu2 hb1 hu1
    have e2 : (x : G) = t⁻¹ * u * t :=
      cyc_inv_unique (Subgroup.isCyclic_zpowers _) hbH.2 hua' hb2 hu'2 hb1 hu'1
    rw [e1, htu] at e2
    apply hz
    have : u * 1 = u * z := by rw [mul_one]; exact e2
    exact (mul_left_cancel this).symm
  have hgen : A = Subgroup.zpowers a ⊔ Subgroup.zpowers (t⁻¹ * a * t) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le (Subgroup.zpowers_le.2 haA) (Subgroup.zpowers_le.2 hat)
    · have hcc : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers (t⁻¹ * a * t), p * q = q * p := by
        intro p hp q hq
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
        exact (Commute.zpow_zpow (show Commute a (t⁻¹ * a * t) from hcomm) i j).eq
      have h1 := card_sup_mul_card_inf' (le_normalizer_of_commute' hcc)
      rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hord, hord'] at h1
      rw [h1, hAcard]
  have ht1' : t ≠ 1 := fun h => htA (h ▸ one_mem _)
  have hy1' : y ≠ 1 := fun h => hyA (h ▸ one_mem _)
  have hty' : t ≠ y := fun h => htyA (by rw [← h, ht2]; exact one_mem _)
  have ht2' : t ^ 2 = 1 := by rw [pow_two]; exact ht2
  have hy2' : y ^ 2 = 1 := by rw [pow_two]; exact hy2
  have hcty : ∀ p ∈ Subgroup.zpowers t, ∀ q ∈ Subgroup.zpowers y, p * q = q * p := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact (Commute.zpow_zpow (show Commute t y from hty) i j).eq
  have htS1 : (Subgroup.zpowers t) ⊓ (Subgroup.zpowers y) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases (mem_zpowers_of_sq' ht2).1 hg.1 with h | h
    · rw [h]; exact one_mem _
    · exfalso
      rcases (mem_zpowers_of_sq' hy2).1 hg.2 with h' | h'
      · exact ht1' (h.symm.trans h')
      · exact hty' (h.symm.trans h')
  have hAB : A ⊓ (Subgroup.zpowers t ⊔ Subgroup.zpowers y) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_sup_of_commute' hcty hg.2
    rcases (mem_zpowers_of_sq' ht2).1 hp with hp1 | hp1 <;>
      rcases (mem_zpowers_of_sq' hy2).1 hq with hq1 | hq1
    · rw [hp1, hq1, one_mul]; exact one_mem _
    · exfalso; apply hyA; have := hg.1; rwa [hp1, hq1, one_mul] at this
    · exfalso; apply htA; have := hg.1; rwa [hp1, hq1, mul_one] at this
    · exfalso; apply htyA; have := hg.1; rwa [hp1, hq1] at this
  have hBcard : Nat.card ↥(Subgroup.zpowers t ⊔ Subgroup.zpowers y) = 4 := by
    have h1 := card_sup_mul_card_inf' (A := Subgroup.zpowers t) (B := Subgroup.zpowers y)
      (le_normalizer_of_commute' hcty)
    rw [htS1, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime ht2' ht1', orderOf_eq_prime hy2' hy1'] at h1
    omega
  have hBN : Subgroup.zpowers t ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (A : Set G) := by
    apply sup_le
    · rw [Subgroup.zpowers_le]; exact mem_normalizer_of_invol ht2 htN
    · rw [Subgroup.zpowers_le]; exact mem_normalizer_of_invol hy2 hyN
  have hS : S = A ⊔ (Subgroup.zpowers t ⊔ Subgroup.zpowers y) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact sup_le hAS (sup_le (Subgroup.zpowers_le.2 htS) (Subgroup.zpowers_le.2 hyS))
    · have h1 := card_sup_mul_card_inf' hBN
      rw [hAB, Subgroup.card_bot, mul_one, hBcard] at h1
      rw [hSc, h1]
      omega
  refine ⟨hord, hgen, hbot, hcomm, ht2, hy2, hty, ht1', hy1', hty', hAB, hyinv, ?_⟩
  rw [hS, sup_assoc]

theorem coord_arith {k : ℕ} (hk : 3 ≤ k) {α β : ℤ} (hα : α % 2 = 1) (hβ : β % 4 = 2) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hd : ((2 ^ k : ℕ) : ℤ) ∣ α * α - β * β - ε) : False := by
  have h8 : (8 : ℤ) ∣ ((2 ^ k : ℕ) : ℤ) := by
    have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hk
    exact_mod_cast this
  have hd8 := dvd_trans h8 hd
  obtain ⟨a, ha⟩ : ∃ a, α = 2 * a + 1 := ⟨α / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, β = 4 * b + 2 := ⟨β / 4, by omega⟩
  have h1 : α * α = 4 * (a * (a + 1)) + 1 := by rw [ha]; ring
  have h2 : β * β = 16 * (b * (b + 1)) + 4 := by rw [hb]; ring
  obtain ⟨c, hc⟩ := Int.even_mul_succ_self a
  rw [h1, h2] at hd8
  rcases hε with rfl | rfl <;> omega

theorem exp_contradiction {k : ℕ} (hk : 3 ≤ k) {x x' z : G}
    (hxo : orderOf x = 2 ^ k) (hx'o : orderOf x' = 2 ^ k)
    (hbot : Subgroup.zpowers x ⊓ Subgroup.zpowers x' = ⊥) (hcomm : x * x' = x' * x)
    (hz : z = x ^ (2 ^ (k - 1))) (φ ψ : MulAut G)
    (hψx : ψ x = x') (hψrel : x * x' * ψ x' = 1) (hφψ : φ x' = ψ (φ x))
    (hφz : φ z = z) (hc : φ x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers x')
    (hV : ∀ g ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers (φ x), g * g = 1)
    (hφφ : φ (φ x) = x ∨ φ (φ x) = x⁻¹) : False := by
  have hxx' : Commute x x' := hcomm
  obtain ⟨E, hE⟩ : ∃ E : ℤ → ℤ → G, ∀ a b, E a b = x ^ a * x' ^ b :=
    ⟨fun a b => x ^ a * x' ^ b, fun _ _ => rfl⟩
  have E_mul : ∀ a b c d, E a b * E c d = E (a + c) (b + d) := by
    intro a b c d
    rw [hE, hE, hE]
    have h1 : x' ^ b * x ^ c = x ^ c * x' ^ b := (Commute.zpow_zpow hxx' c b).eq.symm
    calc x ^ a * x' ^ b * (x ^ c * x' ^ d) = x ^ a * (x' ^ b * x ^ c) * x' ^ d := by group
      _ = x ^ a * (x ^ c * x' ^ b) * x' ^ d := by rw [h1]
      _ = x ^ a * x ^ c * (x' ^ b * x' ^ d) := by group
      _ = x ^ (a + c) * x' ^ (b + d) := by rw [← zpow_add, ← zpow_add]
  have E_zero : E 0 0 = 1 := by rw [hE]; simp
  have E_pow : ∀ a b (m : ℤ), (E a b) ^ m = E (a * m) (b * m) := by
    intro a b m
    rw [hE, hE]
    have hcm : Commute (x ^ a) (x' ^ b) := Commute.zpow_zpow hxx' a b
    rw [hcm.mul_zpow, ← zpow_mul, ← zpow_mul]
  have hint : ∀ a b c d, E a b = E c d → ((2 ^ k : ℕ) : ℤ) ∣ a - c ∧ ((2 ^ k : ℕ) : ℤ) ∣ b - d := by
    intro a b c d h
    have h1 : E a b * E (-c) (-d) = 1 := by
      rw [h, E_mul, add_neg_cancel, add_neg_cancel, E_zero]
    rw [E_mul, hE] at h1
    have h2 : x ^ (a + -c) = (x' ^ (b + -d))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : x ^ (a + -c) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers x' := by
      refine ⟨Subgroup.zpow_mem_zpowers _ _, ?_⟩
      rw [h2, ← zpow_neg]
      exact Subgroup.zpow_mem_zpowers _ _
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : x' ^ (b + -d) = 1 := by
      rw [h3, one_mul] at h1
      exact h1
    have e1 := (orderOf_dvd_iff_zpow_eq_one.2 h3)
    have e2 := (orderOf_dvd_iff_zpow_eq_one.2 h4)
    rw [hxo] at e1
    rw [hx'o] at e2
    exact ⟨by simpa [sub_eq_add_neg] using e1, by simpa [sub_eq_add_neg] using e2⟩
  have hcc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x', a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hxx' i j).eq
  obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_of_commute' hcc hc
  obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨β, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  have hφx : φ x = E α β := by rw [hE, hpq]
  have hψx' : ψ x' = E (-1) (-1) := by
    have h1 : ψ x' = (x * x')⁻¹ := eq_inv_of_mul_eq_one_right hψrel
    rw [h1, hE, zpow_neg_one, zpow_neg_one, mul_inv_rev]
    exact hxx'.inv_inv.eq.symm
  have hψE : ∀ a b : ℤ, ψ (E a b) = E (-b) (a - b) := by
    intro a b
    rw [hE a b, map_mul, map_zpow, map_zpow, hψx, hψx', E_pow]
    have h0 : x' ^ a = E 0 a := by rw [hE]; simp
    rw [h0, E_mul]
    congr 1 <;> ring
  have hφx' : φ x' = E (-β) (α - β) := by rw [hφψ, hφx, hψE]
  have hφE : ∀ a b : ℤ, φ (E a b) = E (a * α - b * β) (a * β + b * (α - β)) := by
    intro a b
    rw [hE a b, map_mul, map_zpow, map_zpow, hφx, hφx', E_pow, E_pow, E_mul]
    congr 1 <;> ring
  have hMpos : (0 : ℤ) < ((2 ^ (k - 1) : ℕ) : ℤ) := by positivity
  have hM : ((2 ^ k : ℕ) : ℤ) = 2 * ((2 ^ (k - 1) : ℕ) : ℤ) := by
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact_mod_cast this
  have hzE : z = E ((2 ^ (k - 1) : ℕ) : ℤ) 0 := by
    rw [hz, hE, zpow_zero, mul_one, zpow_natCast]
  have hφzE : φ z = E (α * ((2 ^ (k - 1) : ℕ) : ℤ)) (β * ((2 ^ (k - 1) : ℕ) : ℤ)) := by
    rw [hz, map_pow, hφx, ← zpow_natCast, E_pow]
  have key := hint _ _ _ _ (hφzE.symm.trans (hφz.trans hzE))
  have hα : α % 2 = 1 := by
    have h1 : (2 : ℤ) * ((2 ^ (k - 1) : ℕ) : ℤ) ∣ (α - 1) * ((2 ^ (k - 1) : ℕ) : ℤ) := by
      have := key.1
      rw [hM] at this
      convert this using 1
      ring
    have h2 := (mul_dvd_mul_iff_right hMpos.ne').1 h1
    omega
  have hβ2 : β % 2 = 0 := by
    have h1 : (2 : ℤ) * ((2 ^ (k - 1) : ℕ) : ℤ) ∣ β * ((2 ^ (k - 1) : ℕ) : ℤ) := by
      have := key.2
      rw [hM] at this
      simpa using this
    have h2 : (2 : ℤ) ∣ β := (mul_dvd_mul_iff_right hMpos.ne').1 (by simpa using h1)
    omega
  have hβ4 : β % 4 = 2 := by
    by_contra hne
    have hβ0 : β % 4 = 0 := by omega
    obtain ⟨β₁, hβ₁⟩ : ∃ β₁, β = 4 * β₁ := ⟨β / 4, by omega⟩
    have hk2 : 2 ^ k = 4 * 2 ^ (k - 2) := by
      have : k = (k - 2) + 2 := by omega
      conv_lhs => rw [this]
      rw [pow_add]; ring
    have hc₀ : (φ x) ^ (2 ^ (k - 2)) = E (α * ((2 ^ (k - 2) : ℕ) : ℤ)) 0 := by
      rw [hφx, ← zpow_natCast, E_pow]
      have hb : x' ^ (β * ((2 ^ (k - 2) : ℕ) : ℤ)) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hx'o, hk2]
        exact ⟨β₁, by push_cast; rw [hβ₁]; ring⟩
      rw [hE, hE, hb]; simp
    have hmem1 : (φ x) ^ (2 ^ (k - 2)) ∈ Subgroup.zpowers x := by
      rw [hc₀, hE]
      simp only [zpow_zero, mul_one]
      exact Subgroup.zpow_mem_zpowers _ _
    have hmem2 : (φ x) ^ (2 ^ (k - 2)) ∈ Subgroup.zpowers (φ x) := Subgroup.npow_mem_zpowers _ _
    have hsq := hV _ ⟨hmem1, hmem2⟩
    rw [hc₀, E_mul] at hsq
    have h3 := (hint _ _ 0 0 (hsq.trans E_zero.symm)).1
    have h4 : (2 : ℤ) * ((2 ^ (k - 1) : ℕ) : ℤ) ∣ α * ((2 ^ (k - 1) : ℕ) : ℤ) := by
      rw [← hM]
      have e : ((2 ^ (k - 1) : ℕ) : ℤ) = 2 * ((2 ^ (k - 2) : ℕ) : ℤ) := by
        have : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
          rw [← pow_succ']
          congr 1
          omega
        exact_mod_cast this
      rw [e]
      convert h3 using 1
      ring
    have h5 : (2 : ℤ) ∣ α := (mul_dvd_mul_iff_right hMpos.ne').1 h4
    omega
  have hφφE : φ (φ x) = E (α * α - β * β) (α * β + β * (α - β)) := by
    rw [hφx, hφE]
  rcases hφφ with h | h
  · have hx1 : x = E 1 0 := by rw [hE]; simp
    have := hint _ _ _ _ (hφφE.symm.trans (h.trans hx1))
    exact coord_arith hk hα hβ4 1 (Or.inl rfl) this.1
  · have hx1 : x⁻¹ = E (-1) 0 := by rw [hE]; simp
    have := hint _ _ _ _ (hφφE.symm.trans (h.trans hx1))
    exact coord_arith hk hα hβ4 (-1) (Or.inr rfl) this.1

theorem phi_sq_formula {x x' : G} (hcomm : x * x' = x' * x) (φ ψ : MulAut G)
    (hψx : ψ x = x') (hψrel : x * x' * ψ x' = 1) (hφψ : φ x' = ψ (φ x))
    (hc : φ x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers x') :
    ∃ α β : ℤ, φ x = x ^ α * x' ^ β ∧
      φ (φ x) = x ^ (α * α - β * β) * x' ^ (α * β + β * (α - β)) := by
  have hxx' : Commute x x' := hcomm
  obtain ⟨E, hE⟩ : ∃ E : ℤ → ℤ → G, ∀ a b, E a b = x ^ a * x' ^ b :=
    ⟨fun a b => x ^ a * x' ^ b, fun _ _ => rfl⟩
  have E_mul : ∀ a b c d, E a b * E c d = E (a + c) (b + d) := by
    intro a b c d
    rw [hE, hE, hE]
    have h1 : x' ^ b * x ^ c = x ^ c * x' ^ b := (Commute.zpow_zpow hxx' c b).eq.symm
    calc x ^ a * x' ^ b * (x ^ c * x' ^ d) = x ^ a * (x' ^ b * x ^ c) * x' ^ d := by group
      _ = x ^ a * (x ^ c * x' ^ b) * x' ^ d := by rw [h1]
      _ = x ^ a * x ^ c * (x' ^ b * x' ^ d) := by group
      _ = x ^ (a + c) * x' ^ (b + d) := by rw [← zpow_add, ← zpow_add]
  have E_pow : ∀ a b (m : ℤ), (E a b) ^ m = E (a * m) (b * m) := by
    intro a b m
    rw [hE, hE]
    have hcm : Commute (x ^ a) (x' ^ b) := Commute.zpow_zpow hxx' a b
    rw [hcm.mul_zpow, ← zpow_mul, ← zpow_mul]
  have hcc : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers x', a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hxx' i j).eq
  obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_of_commute' hcc hc
  obtain ⟨α, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨β, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
  have hφx : φ x = E α β := by rw [hE, hpq]
  have hψx' : ψ x' = E (-1) (-1) := by
    have h1 : ψ x' = (x * x')⁻¹ := eq_inv_of_mul_eq_one_right hψrel
    rw [h1, hE, zpow_neg_one, zpow_neg_one, mul_inv_rev]
    exact hxx'.inv_inv.eq.symm
  have hψE : ∀ a b : ℤ, ψ (E a b) = E (-b) (a - b) := by
    intro a b
    rw [hE a b, map_mul, map_zpow, map_zpow, hψx, hψx', E_pow]
    have h0 : x' ^ a = E 0 a := by rw [hE]; simp
    rw [h0, E_mul]
    congr 1 <;> ring
  have hφx' : φ x' = E (-β) (α - β) := by rw [hφψ, hφx, hψE]
  have hφE : ∀ a b : ℤ, φ (E a b) = E (a * α - b * β) (a * β + b * (α - β)) := by
    intro a b
    rw [hE a b, map_mul, map_zpow, map_zpow, hφx, hφx', E_pow, E_pow, E_mul]
    congr 1 <;> ring
  refine ⟨α, β, hφx.trans (hE α β), ?_⟩
  rw [hφx, hφE, hE]

theorem coord_mul {x x' : G} (hxx' : Commute x x') (a b c d : ℤ) :
    (x ^ a * x' ^ b) * (x ^ c * x' ^ d) = x ^ (a + c) * x' ^ (b + d) := by
  have h1 : x' ^ b * x ^ c = x ^ c * x' ^ b := (Commute.zpow_zpow hxx' c b).eq.symm
  calc x ^ a * x' ^ b * (x ^ c * x' ^ d) = x ^ a * (x' ^ b * x ^ c) * x' ^ d := by group
    _ = x ^ a * (x ^ c * x' ^ b) * x' ^ d := by rw [h1]
    _ = x ^ a * x ^ c * (x' ^ b * x' ^ d) := by group
    _ = x ^ (a + c) * x' ^ (b + d) := by rw [← zpow_add, ← zpow_add]

theorem coord_inj {m : ℕ} {x x' : G} (hxo : orderOf x = m) (hx'o : orderOf x' = m)
    (hbot : Subgroup.zpowers x ⊓ Subgroup.zpowers x' = ⊥) (hxx' : Commute x x') (a b c d : ℤ)
    (h : x ^ a * x' ^ b = x ^ c * x' ^ d) : (m : ℤ) ∣ a - c ∧ (m : ℤ) ∣ b - d := by
  have h0 : (x ^ c * x' ^ d) * (x ^ (-c) * x' ^ (-d)) = 1 := by
    rw [coord_mul hxx', add_neg_cancel, add_neg_cancel]
    simp
  have h1 : (x ^ a * x' ^ b) * (x ^ (-c) * x' ^ (-d)) = 1 := by rw [h]; exact h0
  rw [coord_mul hxx'] at h1
  have h2 : x ^ (a + -c) = (x' ^ (b + -d))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : x ^ (a + -c) ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers x' := by
    refine ⟨Subgroup.zpow_mem_zpowers _ _, ?_⟩
    rw [h2, ← zpow_neg]
    exact Subgroup.zpow_mem_zpowers _ _
  rw [hbot, Subgroup.mem_bot] at h3
  have h4 : x' ^ (b + -d) = 1 := by
    rw [h3, one_mul] at h1
    exact h1
  have e1 := orderOf_dvd_iff_zpow_eq_one.2 h3
  have e2 := orderOf_dvd_iff_zpow_eq_one.2 h4
  rw [hxo] at e1
  rw [hx'o] at e2
  exact ⟨by simpa [sub_eq_add_neg] using e1, by simpa [sub_eq_add_neg] using e2⟩

theorem phi_sq_trivial {x x' z : G} (hxo : orderOf x = 4) (hx'o : orderOf x' = 4)
    (hbot : Subgroup.zpowers x ⊓ Subgroup.zpowers x' = ⊥) (hcomm : x * x' = x' * x)
    (hz : z = x * x) (φ ψ : MulAut G)
    (hψx : ψ x = x') (hψrel : x * x' * ψ x' = 1) (hφψ : φ x' = ψ (φ x))
    (hφz : φ z = z) (hc : φ x ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers x') :
    φ (φ x) = x := by
  obtain ⟨α, β, hφx, hφφ⟩ := phi_sq_formula hcomm φ ψ hψx hψrel hφψ hc
  have hxx' : Commute x x' := hcomm
  have h1 : (x ^ α * x' ^ β) * (x ^ α * x' ^ β) = x * x := by
    rw [hz, map_mul, hφx] at hφz
    exact hφz
  rw [coord_mul hxx'] at h1
  have h1' : x * x = x ^ (1 + 1 : ℤ) * x' ^ (0 + 0 : ℤ) := by
    rw [zpow_add, zpow_one]
    simp
  have hab := coord_inj hxo hx'o hbot hxx' _ _ _ _ (h1.trans h1')
  have hα : α % 2 = 1 := by
    have h := hab.1
    simp only [Nat.cast_ofNat] at h
    omega
  have hβ : β % 2 = 0 := by
    have h := hab.2
    simp only [Nat.cast_ofNat] at h
    omega
  obtain ⟨a, ha⟩ : ∃ a, α = 2 * a + 1 := ⟨α / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, β = 2 * b := ⟨β / 2, by omega⟩
  have e1 : α * α - β * β = 1 + 4 * (a * a + a - b * b) := by rw [ha, hb]; ring
  have e2 : α * β + β * (α - β) = 4 * (2 * a * b + b - b * b) := by rw [ha, hb]; ring
  have hx4 : x ^ (4 : ℤ) = 1 := by
    have := pow_orderOf_eq_one x
    rw [hxo] at this
    exact_mod_cast this
  have hx'4 : x' ^ (4 : ℤ) = 1 := by
    have := pow_orderOf_eq_one x'
    rw [hx'o] at this
    exact_mod_cast this
  rw [hφφ, e1, e2, zpow_add, zpow_mul, zpow_mul, hx4, hx'4, one_zpow, one_zpow, mul_one, mul_one,
    zpow_one]

end Elementary

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
