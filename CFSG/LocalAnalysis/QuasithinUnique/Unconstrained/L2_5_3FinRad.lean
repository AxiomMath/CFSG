module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinPair

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

section Pure

variable {X : Type} [Group X]

theorem exists_order_four_or_klein {B : Subgroup X} (hB : Nat.card ↥B = 4) :
    (∃ u ∈ B, orderOf u = 4) ∨
      ∃ t ∈ B, ∃ s ∈ B, t ≠ 1 ∧ s ≠ 1 ∧ t ≠ s ∧ t * t = 1 ∧ s * s = 1 ∧ t * s = s * t := by
  by_cases h4 : ∃ u ∈ B, orderOf u = 4
  · exact Or.inl h4
  right
  have h4' : ∀ u ∈ B, orderOf u ≠ 4 := fun u hu h => h4 ⟨u, hu, h⟩
  have hsq : ∀ u ∈ B, u * u = 1 := by
    intro u hu
    have hdvd : orderOf u ∣ 4 := by
      rw [← hB, ← Subgroup.orderOf_mk u hu]
      exact orderOf_dvd_natCard (⟨u, hu⟩ : ↥B)
    have hd : orderOf u ∈ Nat.divisors 4 := by simpa using hdvd
    have hd4 : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hd4] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h
    · rw [orderOf_eq_one_iff] at h
      rw [h, one_mul]
    · rw [← pow_two]
      exact h ▸ pow_orderOf_eq_one u
    · exact absurd h (h4' u hu)
  obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
    have hB1 : B ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hB
      omega
    obtain ⟨⟨t, htB⟩, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
    exact ⟨t, htB, fun h => ht (Subtype.ext h)⟩
  have hto : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq t htB) ht1
  have hlt : Subgroup.zpowers t < B := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr htB) fun h => ?_
    have : Nat.card (Subgroup.zpowers t) = 4 := h ▸ hB
    rw [Nat.card_zpowers, hto] at this
    omega
  obtain ⟨s, hsB, hs⟩ := IsConcreteLE.exists_of_lt hlt
  have hs1 : s ≠ 1 := fun h => hs (h ▸ one_mem _)
  have hst : s ≠ t := fun h => hs (h ▸ Subgroup.mem_zpowers t)
  refine ⟨t, htB, s, hsB, ht1, hs1, hst.symm, hsq t htB, hsq s hsB, ?_⟩
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hsq t htB)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hsq s hsB)
  have hts' : (t * s)⁻¹ = t * s := inv_eq_of_mul_eq_one_right (hsq (t * s) (B.mul_mem htB hsB))
  rw [mul_inv_rev, hsi, hti] at hts'
  exact hts'.symm

variable [Finite X]

theorem exists_odd_prime_dvd_card_of_not_isPGroup {C : Subgroup X} (hC : ¬ IsPGroup 2 ↥C) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Nat.card ↥C := by
  by_contra hcon
  apply hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hpow : Nat.card ↥C = 2 ^ (Nat.card ↥C).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hpos fun {d} hd hdvd => by
      by_contra hne
      exact hcon ⟨d, hd, hne, hdvd⟩
  exact IsPGroup.of_card hpow

theorem exists_odd_orderOf_of_not_isPGroup {C : Subgroup X} (hC : ¬ IsPGroup 2 ↥C) :
    ∃ x ∈ C, x ≠ 1 ∧ Odd (orderOf x) := by
  obtain ⟨r, hr, hr2, hdvd⟩ := exists_odd_prime_dvd_card_of_not_isPGroup hC
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  refine ⟨(x : X), x.2, ?_, ?_⟩
  · intro h1
    have : orderOf x = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext h1
    rw [hx] at this
    exact hr.one_lt.ne' this
  · rw [← Subgroup.orderOf_coe x] at hx
    exact hx ▸ hr.odd_of_ne_two hr2

theorem mem_normalizer_of_conj_mem {F : Subgroup X} {w : X}
    (h : ∀ f ∈ F, w * f * w⁻¹ ∈ F) : w ∈ Subgroup.normalizer (F : Set X) := by
  have hle : F.map (MulAut.conj w).toMonoidHom ≤ F := by
    rintro _ ⟨f, hf, rfl⟩
    exact h f hf
  have hcard : Nat.card (F.map (MulAut.conj w).toMonoidHom) = Nat.card F :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  have heq : F.map (MulAut.conj w).toMonoidHom = F :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [Subgroup.mem_normalizer_iff]
  intro f
  refine ⟨h f, fun hf => ?_⟩
  have hf' : w * f * w⁻¹ ∈ F.map (MulAut.conj w).toMonoidHom := by
    rw [heq]
    exact hf
  obtain ⟨f', hf'F, hf'f⟩ := hf'
  have : f' = f := (MulAut.conj w).injective hf'f
  rwa [← this]

theorem exists_order_four_or_klein_of_pGroup {A : Subgroup X} (hA : IsPGroup 2 ↥A)
    (h4 : 4 ≤ Nat.card ↥A) :
    (∃ u ∈ A, orderOf u = 4) ∨
      ∃ t ∈ A, ∃ s ∈ A, t ≠ 1 ∧ s ≠ 1 ∧ t ≠ s ∧ t * t = 1 ∧ s * s = 1 ∧ t * s = s * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card ↥A := by
    rw [hn]
    exact pow_dvd_pow 2 hn2
  obtain ⟨B₀, hB₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) 2 hdvd
  have hB : Nat.card ↥(B₀.map A.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hB₀]
    norm_num
  have hle : B₀.map A.subtype ≤ A := Subgroup.map_subtype_le _
  rcases exists_order_four_or_klein hB with ⟨u, hu, hu4⟩ | ⟨t, ht, s, hs, h⟩
  · exact Or.inl ⟨u, hle hu, hu4⟩
  · exact Or.inr ⟨t, hle ht, s, hle hs, h⟩

theorem card_dvd_sixteen_of_isPGroup {A : Subgroup X} (hA : IsPGroup 2 ↥A) {m : ℕ} (hm : Odd m)
    (hdvd : Nat.card ↥A ∣ 16 * m) : Nat.card ↥A ∣ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
  rw [hn] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ n) m := Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hm)
  exact hcop.dvd_of_dvd_mul_right hdvd

theorem card_mul_le_of_inf_eq_bot {Q Q' R : Subgroup X} (hQ : Q ≤ R) (hQ' : Q' ≤ R)
    (h : Q ⊓ Q' = ⊥) : Nat.card Q * Nat.card Q' ≤ Nat.card R := by
  let f : Q × Q' → R := fun p => ⟨p.1 * p.2, R.mul_mem (hQ p.1.2) (hQ' p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : (a : X) * (b : X) = (a' : X) * (b' : X) := congrArg Subtype.val hab
    have h2 : (a' : X)⁻¹ * (a : X) = (b' : X) * (b : X)⁻¹ := by
      calc (a' : X)⁻¹ * (a : X) = (a' : X)⁻¹ * ((a : X) * (b : X)) * (b : X)⁻¹ := by group
        _ = (a' : X)⁻¹ * ((a' : X) * (b' : X)) * (b : X)⁻¹ := by rw [h1]
        _ = (b' : X) * (b : X)⁻¹ := by group
    have hmemQ : (a' : X)⁻¹ * (a : X) ∈ Q := Q.mul_mem (Q.inv_mem a'.2) a.2
    have hmemQ' : (a' : X)⁻¹ * (a : X) ∈ Q' := h2 ▸ Q'.mul_mem b'.2 (Q'.inv_mem b.2)
    have hbot : (a' : X)⁻¹ * (a : X) ∈ (⊥ : Subgroup X) :=
      h ▸ Subgroup.mem_inf.mpr ⟨hmemQ, hmemQ'⟩
    rw [Subgroup.mem_bot, inv_mul_eq_one] at hbot
    have haa : (a : X) = a' := hbot.symm
    have hbb : (b : X) = b' := by
      rw [haa] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem conj_eq_of_card_sq {R Q : Subgroup X} {t g : X} (hR : Nat.card R ≤ 16) (hQR : Q ≤ R)
    (hQc : 5 ≤ Nat.card Q) (ht1 : t ≠ 1) (htt : t * t = 1)
    (hQ : ∀ y ∈ Q, y = 1 ∨ y = t ∨ y * y = t)
    (hg : g ∈ Subgroup.normalizer (R : Set X)) : g * t * g⁻¹ = t := by
  set Q' : Subgroup X := Q.map (MulAut.conj g).toMonoidHom with hQ'
  have hQ'c : Nat.card Q' = Nat.card Q := Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hQ'R : Q' ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hQR hy)
  have hne : Q ⊓ Q' ≠ ⊥ := by
    intro h
    have := card_mul_le_of_inf_eq_bot hQR hQ'R h
    rw [hQ'c] at this
    nlinarith
  obtain ⟨y, ⟨hyQ, hyQ'⟩, hy1⟩ : ∃ y : X, (y ∈ Q ∧ y ∈ Q') ∧ y ≠ 1 := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨y, Subgroup.mem_inf.mp hy, fun h => hy1 (Subtype.ext h)⟩
  obtain ⟨y₀, hy₀, hy₀y⟩ := hyQ'
  have hy : y = g * y₀ * g⁻¹ := hy₀y.symm
  have ht'tt : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have ht'1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have h2 := congrArg (fun z => g⁻¹ * z * g) h
    have h3 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [h3]
    simpa using h2
  have hsq : ∀ z : X, (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := fun z => by group
  rcases hQ y hyQ with h | h | h
  · exact absurd h hy1
  · rcases hQ y₀ hy₀ with h0 | h0 | h0
    · exact absurd (by rw [hy, h0]; group) hy1
    · rw [hy, h0] at h
      exact h
    · exfalso
      have h1 : y * y = g * t * g⁻¹ := by rw [hy, hsq, h0]
      rw [h, htt] at h1
      exact ht'1 h1.symm
  · rcases hQ y₀ hy₀ with h0 | h0 | h0
    · exact absurd (by rw [hy, h0]; group) hy1
    · exfalso
      have h1 : y = g * t * g⁻¹ := by rw [hy, h0]
      rw [h1, ht'tt] at h
      exact ht1 h.symm
    · have h1 : y * y = g * t * g⁻¹ := by rw [hy, hsq, h0]
      rw [h] at h1
      exact h1.symm

end Pure

section NoOddCent

variable {G : Type} [Group G] [Finite G]

theorem charTwo_inf_normalizer_of_no_odd_cent {K R : Subgroup G}
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R)
    (hodd : ∀ x ∈ K, x ≠ 1 → Odd (orderOf x) → ¬ R ≤ Subgroup.centralizer ({x} : Set G)) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  refine charTwo_of_isPGroup_inf_centralizer inf_le_right hrad ?_
  by_contra hC
  obtain ⟨x, hxC, hx1, hxo⟩ := exists_odd_orderOf_of_not_isPGroup hC
  refine hodd x hxC.1.1 hx1 hxo fun r hr => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hxC.2 r hr

theorem charTwo_inf_normalizer_of_odd_cent_odd {K R : Subgroup G}
    (hodd : ∀ x : ↥K, x ≠ 1 → Odd (orderOf x) → ∀ u : ↥K, u * x = x * u → Odd (orderOf u))
    (hRK : R ≤ K) (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  refine charTwo_inf_normalizer_of_no_odd_cent hrad fun x hxK hx1 hxo hRx => ?_
  obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
  have hcomm : (⟨r, hRK hrR⟩ : ↥K) * ⟨x, hxK⟩ = ⟨x, hxK⟩ * ⟨r, hRK hrR⟩ :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hRx hrR))
  have hodd' := hodd ⟨x, hxK⟩ (fun h => hx1 (congrArg Subtype.val h))
    (by rwa [Subgroup.orderOf_mk]) ⟨r, hRK hrR⟩ hcomm
  rw [Subgroup.orderOf_mk] at hodd'
  obtain ⟨k, hk⟩ := hR2 ⟨r, hrR⟩
  have hr2k : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hr2k)
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd'
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hj0⟩)
  have hr' : r = 1 := by
    rw [← orderOf_eq_one_iff, hj, hj0, pow_zero]
  exact hr1 (Subtype.ext hr')

end NoOddCent

section Data

variable {G : Type} [Group G] [Finite G]

structure RadData (X : Type) [Group X] [Finite X] : Prop where
  center : ∀ z : X, (∀ x : X, z * x = x * z) → z = 1
  simple : IsSimpleGroup X
  card : ∃ m : ℕ, Odd m ∧ 1 < m ∧ Nat.card X = 16 * m
  odd_no4 : ∀ x : X, x ≠ 1 → Odd (orderOf x) → ∀ u : X, u * x = x * u →
    u * u * (u * u) = 1 → u * u = 1
  odd_noV : ∀ x : X, x ≠ 1 → Odd (orderOf x) → ∀ t s : X, t ≠ 1 → s ≠ 1 → t ≠ s → t * t = 1 →
    s * s = 1 → t * s = s * t → t * x = x * t → s * x = x * s → False
  quat_ex : ∀ t : X, orderOf t = 2 → ∃ y : X, y * y = t
  quat_mul : ∀ t : X, orderOf t = 2 → ∀ y y' : X, y * y = t → y' * y' = t →
    y * y' = 1 ∨ y * y' = t ∨ (y * y') * (y * y') = t
  quat_card : ∀ t : X, orderOf t = 2 → 5 ≤ Nat.card {y : X // y = 1 ∨ y = t ∨ y * y = t}
  core_cent : ∀ t : X, orderOf t = 2 → ∀ m : X, m * t = t * m → ¬ (m = 1 ∨ m = t ∨ m * m = t) →
    ∃ w : X, w * t = t * w ∧ (m⁻¹ * (w * m * w⁻¹)) ^ 16 ≠ 1

omit [Finite G] in
theorem pow_four_eq' (z : G) : z ^ 4 = z * z * (z * z) := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

omit [Finite G] in
theorem comm_of_sq {y t : G} (h : y * y = t) : t * y = y * t := by
  rw [← h]
  group

omit [Finite G] in
theorem orderOf_eq_two_of_mul_self {t : G} (htt : t * t = 1) (ht1 : t ≠ 1) : orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1

omit [Finite G] in
@[expose] def quatSubgroup (K : Subgroup G) (t : G) (htt : t * t = 1)
    (hmul : ∀ y ∈ K, ∀ y' ∈ K, y * y = t → y' * y' = t →
      y * y' = 1 ∨ y * y' = t ∨ (y * y') * (y * y') = t) : Subgroup G where
  carrier := {z | z ∈ K ∧ (z = 1 ∨ z = t ∨ z * z = t)}
  one_mem' := ⟨K.one_mem, Or.inl rfl⟩
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, ?_⟩
    rcases ha with ha | ha | ha
    · rw [ha, one_mul]
      exact hb
    · rcases hb with hb | hb | hb
      · rw [hb, mul_one]
        exact Or.inr (Or.inl ha)
      · rw [ha, hb]
        exact Or.inl htt
      · right
        right
        have hc : t * b = b * t := comm_of_sq hb
        rw [ha]
        calc t * b * (t * b) = t * (b * t) * b := by group
          _ = t * (t * b) * b := by rw [← hc]
          _ = (t * t) * (b * b) := by group
          _ = t := by rw [htt, hb, one_mul]
    · rcases hb with hb | hb | hb
      · rw [hb, mul_one]
        exact Or.inr (Or.inr ha)
      · right
        right
        have hc : t * a = a * t := comm_of_sq ha
        rw [hb]
        calc a * t * (a * t) = a * (t * a) * t := by group
          _ = a * (a * t) * t := by rw [hc]
          _ = (a * a) * (t * t) := by group
          _ = t := by rw [htt, ha, mul_one]
      · exact hmul a haK b hbK ha hb
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, ?_⟩
    rcases ha with ha | ha | ha
    · left
      rw [ha, inv_one]
    · right
      left
      rw [ha]
      exact inv_eq_of_mul_eq_one_right htt
    · right
      right
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = t := by rw [ha]; exact inv_eq_of_mul_eq_one_right htt

theorem quatSubgroup_le_pCoreOf {K N : Subgroup G} {t : G} (htt : t * t = 1)
    (hmul : ∀ y ∈ K, ∀ y' ∈ K, y * y = t → y' * y' = t →
      y * y' = 1 ∨ y * y' = t ∨ (y * y') * (y * y') = t)
    (hNK : N ≤ K) (hQN : quatSubgroup K t htt hmul ≤ N) (hNt : ∀ g ∈ N, g * t * g⁻¹ = t) :
    quatSubgroup K t htt hmul ≤ pCoreOf 2 N := by
  refine le_pCoreOf_of_normal_pGroup hQN (fun g hg => ?_) ?_
  · refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨hzK, hz⟩ := hz
    refine ⟨K.mul_mem (K.mul_mem (hNK hg) hzK) (K.inv_mem (hNK hg)), ?_⟩
    rcases hz with h | h | h
    · left
      rw [h]
      group
    · right
      left
      rw [h]
      exact hNt g hg
    · right
      right
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = t := by rw [h]; exact hNt g hg
  · refine isPGroup_of_forall_pow fun z hz => ⟨2, ?_⟩
    obtain ⟨-, hz⟩ := hz
    have h4 : z ^ 2 ^ 2 = z * z * (z * z) := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact pow_four_eq' z
    rw [h4]
    rcases hz with h | h | h
    · rw [h, one_mul, one_mul]
    · rw [h, htt, one_mul]
    · rw [h, htt]

theorem RadData.quat_mul_mem {K : Subgroup G} (hD : RadData ↥K) {t : G} (htK : t ∈ K)
    (hto : orderOf (⟨t, htK⟩ : ↥K) = 2) :
    ∀ y ∈ K, ∀ y' ∈ K, y * y = t → y' * y' = t →
      y * y' = 1 ∨ y * y' = t ∨ (y * y') * (y * y') = t := by
  intro y hy y' hy' h h'
  rcases hD.quat_mul ⟨t, htK⟩ hto ⟨y, hy⟩ ⟨y', hy'⟩ (Subtype.ext h) (Subtype.ext h') with
    h1 | h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (Or.inl (congrArg Subtype.val h1))
  · exact Or.inr (Or.inr (congrArg Subtype.val h1))

theorem eq_bot_of_normal_pGroup {X : Type} [Group X] [Finite X] (hS : IsSimpleGroup X) {m : ℕ}
    (hm : Odd m) (hm1 : 1 < m) (hX : Nat.card X = 16 * m) {M : Subgroup X} (hMn : M.Normal)
    (hM : IsPGroup 2 ↥M) : M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · exact h
  · exfalso
    have hdvd := card_dvd_sixteen_of_isPGroup hM hm (hX ▸ Subgroup.card_subgroup_dvd_card M)
    rw [h, Subgroup.card_top, hX] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem charTwo_inf_normalizer_of_radData {K R : Subgroup G} (hD : RadData ↥K) (hRK : R ≤ K)
    (hR2 : IsPGroup 2 ↥R) (hR : R ≠ ⊥)
    (hrad : pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R) :
    CharTwo (K ⊓ Subgroup.normalizer (R : Set G)) := by
  by_cases h : ∃ x ∈ K, x ≠ 1 ∧ Odd (orderOf x) ∧ R ≤ Subgroup.centralizer ({x} : Set G)
  swap
  · exact charTwo_inf_normalizer_of_no_odd_cent hrad fun x hxK hx1 hxo hRx =>
      h ⟨x, hxK, hx1, hxo, hRx⟩
  exfalso
  obtain ⟨x, hxK, hx1, hxo, hRx⟩ := h
  have hRcomm : ∀ r ∈ R, r * x = x * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRx hr)
  have hx'1 : (⟨x, hxK⟩ : ↥K) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx'o : Odd (orderOf (⟨x, hxK⟩ : ↥K)) := by rwa [Subgroup.orderOf_mk]
  have h4 : Nat.card ↥R < 4 := by
    by_contra h4
    rcases exists_order_four_or_klein_of_pGroup hR2 (not_lt.mp h4) with
      ⟨u, huR, hu4⟩ | ⟨a, haR, b, hbR, ha1, hb1, hab, haa, hbb, hcab⟩
    · have hu4' : u * u * (u * u) = 1 := by
        have : u ^ 4 = 1 := hu4 ▸ pow_orderOf_eq_one u
        calc u * u * (u * u) = u ^ 4 := (pow_four_eq' u).symm
          _ = 1 := this
      have h := hD.odd_no4 ⟨x, hxK⟩ hx'1 hx'o ⟨u, hRK huR⟩ (Subtype.ext (hRcomm u huR))
        (Subtype.ext hu4')
      have huu : u * u = 1 := congrArg Subtype.val h
      have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact huu)
      rw [hu4] at this
      omega
    · exact hD.odd_noV ⟨x, hxK⟩ hx'1 hx'o ⟨a, hRK haR⟩ ⟨b, hRK hbR⟩
        (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
        (fun h => hab (congrArg Subtype.val h)) (Subtype.ext haa) (Subtype.ext hbb)
        (Subtype.ext hcab) (Subtype.ext (hRcomm a haR)) (Subtype.ext (hRcomm b hbR))
  have hcard : Nat.card ↥R = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    have hk1 : k ≠ 0 := by
      rintro rfl
      exact hR (Subgroup.eq_bot_of_card_eq R (by rw [hk]; rfl))
    have hk2 : k < 2 := by
      by_contra hk2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk2)
      omega
    have hk3 : k = 1 := by omega
    rw [hk, hk3]
    norm_num
  obtain ⟨t, htR, ht1⟩ : ∃ t ∈ R, t ≠ 1 := by
    obtain ⟨⟨t, htR⟩, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
    exact ⟨t, htR, fun h => ht (Subtype.ext h)⟩
  have hto : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := by
      rw [← hcard, ← Subgroup.orderOf_mk t htR]
      exact orderOf_dvd_natCard (⟨t, htR⟩ : ↥R)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ht1
    · exact h
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [hto, pow_two] at this
    exact this
  have hRel : ∀ r ∈ R, r = 1 ∨ r = t := by
    have hzp : Subgroup.zpowers t = R :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htR)
        (by rw [Nat.card_zpowers, hto, hcard])
    intro r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ hr)
    have hmod := zpow_mod_orderOf t k
    rw [hto] at hmod
    simp only [Nat.cast_ofNat] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hmod, h]
      simp
    · right
      rw [← hmod, h]
      simp
  have htK : t ∈ K := hRK htR
  have hto' : orderOf (⟨t, htK⟩ : ↥K) = 2 := by rwa [Subgroup.orderOf_mk]
  obtain ⟨y, hy⟩ := hD.quat_ex ⟨t, htK⟩ hto'
  have hmul := hD.quat_mul_mem htK hto'
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hN
  have hQN : quatSubgroup K t htt hmul ≤ N := by
    intro z hz
    obtain ⟨hzK, hz⟩ := hz
    refine ⟨hzK, mem_normalizer_of_conj_mem fun f hf => ?_⟩
    have hzt : z * t = t * z := by
      rcases hz with h | h | h
      · rw [h, one_mul, mul_one]
      · rw [h]
      · exact (comm_of_sq h).symm
    have hzf : z * f = f * z := by
      rcases hRel f hf with h | h
      · rw [h, mul_one, one_mul]
      · rw [h]
        exact hzt
    have : z * f * z⁻¹ = f := by
      rw [hzf]
      group
    rw [this]
    exact hf
  have hNt : ∀ g ∈ N, g * t * g⁻¹ = t := by
    intro g hg
    have hgt : g * t * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg.2 t).mp htR
    rcases hRel _ hgt with h | h
    · exfalso
      apply ht1
      have h2 := congrArg (fun z => g⁻¹ * z * g) h
      have h3 : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [h3]
      simpa using h2
    · exact h
  have hle := quatSubgroup_le_pCoreOf htt hmul inf_le_left hQN hNt
  rw [hrad] at hle
  have hyQ : (y : G) ∈ quatSubgroup K t htt hmul :=
    ⟨y.2, Or.inr (Or.inr (congrArg Subtype.val hy))⟩
  have hyt : (y : G) * y = t := congrArg Subtype.val hy
  rcases hRel _ (hle hyQ) with h | h
  · rw [h, one_mul] at hyt
    exact ht1 hyt.symm
  · rw [h, htt] at hyt
    exact ht1 hyt.symm

theorem normalizer_le_normalizer_pCoreOf_of_radData {K R : Subgroup G} {t : G} (hD : RadData ↥K)
    (htK : t ∈ K) (hcen : ∀ x ∈ K, (t * t) * x = x * (t * t)) (hR2 : IsPGroup 2 ↥R)
    (hRK : R ≤ K) (hle : pCoreOf 2 (K ⊓ Subgroup.centralizer ({t} : Set G)) ≤ R) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (K ⊓ Subgroup.centralizer ({t} : Set G)) : Set G) := by
  obtain ⟨m, hmodd, hm1, hKcard⟩ := hD.card
  have htt : t * t = 1 := by
    have := hD.center ⟨t * t, K.mul_mem htK htK⟩ (fun x => Subtype.ext (hcen x x.2))
    exact congrArg Subtype.val this
  set N₀ : Subgroup G := K ⊓ Subgroup.centralizer ({t} : Set G) with hN₀
  have hN₀K : N₀ ≤ K := inf_le_left
  have hMN : pCoreOf 2 N₀ ≤ N₀ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N₀
  have hM2 : IsPGroup 2 ↥(pCoreOf 2 N₀) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N₀
  have hNn : N₀ ≤ Subgroup.normalizer (pCoreOf 2 N₀ : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N₀
  by_cases ht1 : t = 1
  ·
    have hKN : K ≤ N₀ := fun g hg =>
      Subgroup.mem_inf.mpr ⟨hg, by rw [Subgroup.mem_centralizer_singleton_iff, ht1, mul_one, one_mul]⟩
    have hMK : pCoreOf 2 N₀ ≤ K := hMN.trans hN₀K
    have hnormal : ((pCoreOf 2 N₀).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMK).mpr (hKN.trans hNn)
    have hM2' : IsPGroup 2 ↥((pCoreOf 2 N₀).subgroupOf K) :=
      hM2.of_equiv (Subgroup.subgroupOfEquivOfLe hMK).symm
    have hbot := eq_bot_of_normal_pGroup hD.simple hmodd hm1 hKcard hnormal hM2'
    have hMbot : pCoreOf 2 N₀ = ⊥ :=
      (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hMK
    rw [hMbot]
    intro g _
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  · have hto : orderOf t = 2 := orderOf_eq_two_of_mul_self htt ht1
    have hto' : orderOf (⟨t, htK⟩ : ↥K) = 2 := by rwa [Subgroup.orderOf_mk]
    have hmul := hD.quat_mul_mem htK hto'
    have hQtN : quatSubgroup K t htt hmul ≤ N₀ := by
      intro z hz
      obtain ⟨hzK, hz⟩ := hz
      refine Subgroup.mem_inf.mpr ⟨hzK, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hz with h | h | h
      · rw [h, one_mul, mul_one]
      · rw [h]
      · exact (comm_of_sq h).symm
    have hN₀t : ∀ g ∈ N₀, g * t * g⁻¹ = t := by
      intro g hg
      have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
      rw [this]
      group
    have hQtle : quatSubgroup K t htt hmul ≤ pCoreOf 2 N₀ :=
      quatSubgroup_le_pCoreOf htt hmul hN₀K hQtN hN₀t
    have hdesc : ∀ y ∈ pCoreOf 2 N₀, y = 1 ∨ y = t ∨ y * y = t := by
      intro y hy
      by_contra hcon
      have hyN : y ∈ N₀ := hMN hy
      have hyc : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyN.2
      obtain ⟨w, hwt, hw16⟩ := hD.core_cent ⟨t, htK⟩ hto' ⟨y, hyN.1⟩ (Subtype.ext hyc)
        (fun h => hcon (h.imp (congrArg Subtype.val) fun h =>
          h.imp (congrArg Subtype.val) (congrArg Subtype.val)))
      have hwN : (w : G) ∈ N₀ :=
        Subgroup.mem_inf.mpr ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hwt)⟩
      have hwy : (w : G) * y * (w : G)⁻¹ ∈ pCoreOf 2 N₀ :=
        (Subgroup.mem_normalizer_iff.mp (hNn hwN) y).mp hy
      have hc : (y : G)⁻¹ * ((w : G) * y * (w : G)⁻¹) ∈ pCoreOf 2 N₀ :=
        (pCoreOf 2 N₀).mul_mem ((pCoreOf 2 N₀).inv_mem hy) hwy
      have hAK : pCoreOf 2 N₀ ≤ K := hMN.trans hN₀K
      have hdvd16 : Nat.card ↥(pCoreOf 2 N₀) ∣ 16 :=
        card_dvd_sixteen_of_isPGroup hM2 hmodd (hKcard ▸ Subgroup.card_dvd_of_le hAK)
      have h2 : orderOf ((y : G)⁻¹ * ((w : G) * y * (w : G)⁻¹)) ∣ 16 := by
        rw [← Subgroup.orderOf_mk _ hc]
        exact (orderOf_dvd_natCard (⟨_, hc⟩ : ↥(pCoreOf 2 N₀))).trans hdvd16
      have h16 : ((y : G)⁻¹ * ((w : G) * y * (w : G)⁻¹)) ^ 16 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp h2
      apply hw16
      apply Subtype.ext
      simpa using h16
    have hQtcard : 5 ≤ Nat.card ↥(quatSubgroup K t htt hmul) := by
      refine (hD.quat_card ⟨t, htK⟩ hto').trans ?_
      let f : {y : ↥K // y = 1 ∨ y = (⟨t, htK⟩ : ↥K) ∨ y * y = ⟨t, htK⟩} →
          ↥(quatSubgroup K t htt hmul) := fun y =>
        ⟨(y.1 : G), y.1.2, y.2.imp (congrArg Subtype.val) fun h =>
          h.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩
      refine Nat.card_le_card_of_injective f (fun a b h => ?_)
      have h' := congrArg (fun z : ↥(quatSubgroup K t htt hmul) => (z : G)) h
      exact Subtype.ext (Subtype.ext h')
    have hQcard : 5 ≤ Nat.card ↥(pCoreOf 2 N₀) :=
      hQtcard.trans (Subgroup.card_le_of_le hQtle)
    have hRcard : Nat.card ↥R ≤ 16 :=
      Nat.le_of_dvd (by norm_num)
        (card_dvd_sixteen_of_isPGroup hR2 hmodd (hKcard ▸ Subgroup.card_dvd_of_le hRK))
    intro g hg
    have hgt : g * t * g⁻¹ = t := conj_eq_of_card_sq hRcard hle hQcard ht1 htt hdesc hg
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hgyR : g * y * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg y).mp (hle hy)
    refine hQtle ⟨hRK hgyR, ?_⟩
    rcases hdesc y hy with h | h | h
    · left
      rw [h]
      group
    · right
      left
      rw [h]
      exact hgt
    · right
      right
      calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
        _ = t := by rw [h]; exact hgt

end Data

end CFSG.QuasithinUnique.Fin253
