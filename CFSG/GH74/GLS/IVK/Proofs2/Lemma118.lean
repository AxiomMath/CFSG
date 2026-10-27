module

public import CFSG.GH74.GLS.IVK.L2.Lemma13
public import CFSG.GH74.GLS.IVK.A7.Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK

namespace Lemma118

theorem odd_dvd_two_pow {c a : ℕ} (hc : Odd c) (h : c ∣ 2 ^ a) : c = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hc)) h

theorem pow_odd_decomp {P n : ℕ} (hP : 2 ≤ P) (hn : Odd n) (hn3 : 3 ≤ n) :
    ∃ w, 1 ≤ w ∧ (P + 1) ^ n = (P + 1) + P * (P + 2) * w := by
  obtain ⟨m, rfl⟩ := hn
  have hm : 1 ≤ m := by omega
  have hsq : (P + 1) ^ 2 - 1 = P * (P + 2) := by
    have : (P + 1) ^ 2 = P * (P + 2) + 1 := by ring
    omega
  have hd : P * (P + 2) ∣ ((P + 1) ^ 2) ^ m - 1 := by
    have := Nat.sub_dvd_pow_sub_pow ((P + 1) ^ 2) 1 m
    simpa [hsq] using this
  obtain ⟨w₀, hw₀⟩ := hd
  have hpm : 1 < ((P + 1) ^ 2) ^ m := Nat.one_lt_pow (by omega) (by nlinarith)
  have hw₀pos : 1 ≤ w₀ := by
    rcases Nat.eq_zero_or_pos w₀ with h | h
    · subst h
      simp at hw₀
      omega
    · exact h
  refine ⟨(P + 1) * w₀, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  have h1 : ((P + 1) ^ 2) ^ m = 1 + P * (P + 2) * w₀ := by omega
  calc (P + 1) ^ (2 * m + 1) = (P + 1) * ((P + 1) ^ 2) ^ m := by
        rw [pow_succ, pow_mul, mul_comm]
    _ = (P + 1) * (1 + P * (P + 2) * w₀) := by rw [h1]
    _ = (P + 1) + P * (P + 2) * ((P + 1) * w₀) := by ring

theorem no_odd_pow_add_one {P n a : ℕ} (hP : 2 ≤ P) (hPe : Even P) (hn : Odd n) (hn3 : 3 ≤ n)
    (h : (P + 1) ^ n + 1 = 2 ^ a) : False := by
  obtain ⟨w, hw, hdec⟩ := pow_odd_decomp hP hn hn3
  have h1 : (P + 2) * (1 + P * w) = 2 ^ a := by rw [← h, hdec]; ring
  have hodd : Odd (1 + P * w) := by
    obtain ⟨t, ht⟩ := hPe
    exact ⟨t * w, by rw [ht]; ring⟩
  have h2 := odd_dvd_two_pow hodd (Dvd.intro_left _ h1)
  have h3 : P * w = 0 := by omega
  rcases Nat.mul_eq_zero.mp h3 with h | h <;> omega

theorem no_odd_pow_sub_one {P n a : ℕ} (hP : 2 ≤ P) (hPe : Even P) (hn : Odd n) (hn3 : 3 ≤ n)
    (h : (P + 1) ^ n = 2 ^ a + 1) : False := by
  obtain ⟨w, hw, hdec⟩ := pow_odd_decomp hP hn hn3
  have h1 : P * (1 + (P + 2) * w) = 2 ^ a := by
    have : (P + 1) ^ n = P * (1 + (P + 2) * w) + 1 := by rw [hdec]; ring
    omega
  have hodd : Odd (1 + (P + 2) * w) := by
    obtain ⟨t, ht⟩ := hPe
    exact ⟨(t + 1) * w, by rw [ht]; ring⟩
  have h2 := odd_dvd_two_pow hodd (Dvd.intro_left _ h1)
  have h3 : (P + 2) * w = 0 := by omega
  rcases Nat.mul_eq_zero.mp h3 with h | h <;> omega

theorem no_sq_add_one {x a : ℕ} (hx : Odd x) (hx3 : 3 ≤ x) (h : x ^ 2 + 1 = 2 ^ a) : False := by
  have h8 := Nat.eight_dvd_sq_sub_one_of_odd hx
  by_cases ha : 3 ≤ a
  · have h8a : 8 ∣ 2 ^ a := by
      have : (2 : ℕ) ^ 3 ∣ 2 ^ a := pow_dvd_pow 2 ha
      simpa using this
    have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · interval_cases a <;> nlinarith

theorem sq_sub_one_eq {x a : ℕ} (hx : Odd x) (hx3 : 3 ≤ x) (h : x ^ 2 = 2 ^ a + 1) : x = 3 := by
  have h1 : (x - 1) * (x + 1) = 2 ^ a := by
    have : x ^ 2 = (x - 1) * (x + 1) + 1 := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      simp
      ring
    omega
  obtain ⟨u, hu, hu'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h1 : x - 1 ∣ 2 ^ a)
  obtain ⟨v, hv, hv'⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro_left _ h1 : x + 1 ∣ 2 ^ a)
  have h2 : 2 ^ v = 2 ^ u + 2 := by omega
  obtain ⟨y, hy⟩ := hx
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · interval_cases u <;> simp at hu' <;> omega
  · have h4u : 4 ∣ 2 ^ u := by
      have := pow_dvd_pow 2 hu2
      simpa using this
    rcases Nat.lt_or_ge v 2 with hv2 | hv2
    · interval_cases v <;> simp at h2
    · have h4v : 4 ∣ 2 ^ v := by
        have := pow_dvd_pow 2 hv2
        simpa using this
      omega

theorem isFM9_of_pow {p n a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n) (h5 : 5 ≤ p ^ n)
    (h : p ^ n = 2 ^ a + 1 ∨ p ^ n + 1 = 2 ^ a) : IsFM9 (p ^ n) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨t, ht⟩ := hpodd
    omega
  obtain ⟨P, rfl⟩ : ∃ P, p = P + 1 := ⟨p - 1, by omega⟩
  have hPe : Even P := by
    obtain ⟨t, ht⟩ := hpodd
    exact ⟨t, by omega⟩
  have hP2 : 2 ≤ P := by omega
  rcases Nat.even_or_odd n with hne | hno
  · obtain ⟨s, hs⟩ := hne
    have hxodd : Odd ((P + 1) ^ s) := hpodd.pow
    have hq : (P + 1) ^ n = ((P + 1) ^ s) ^ 2 := by
      rw [hs, ← two_mul, pow_mul']
    have hx3 : 3 ≤ (P + 1) ^ s := by
      by_contra hlt
      have hle : (P + 1) ^ s ≤ 2 := by omega
      have := Nat.pow_le_pow_left hle 2
      omega
    rcases h with h | h
    · have := sq_sub_one_eq hxodd hx3 (hq ▸ h)
      left
      rw [hq, this]
      norm_num
    · exfalso
      exact no_sq_add_one hxodd hx3 (hq ▸ h)
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have h1 : n = 1 := by
        obtain ⟨t, ht⟩ := hno
        omega
      subst h1
      simp only [pow_one] at *
      rcases h with h | h
      · right
        refine ⟨hp, Or.inl ?_⟩
        have ha : a ≠ 0 := by
          rintro rfl
          omega
        have hp' : (2 ^ a + 1).Prime := h ▸ hp
        obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num) ha hp'
        exact ⟨m, by rw [h, hm]⟩
      · right
        exact ⟨hp, Or.inr ⟨a, h⟩⟩
    · exfalso
      rcases h with h | h
      · exact no_odd_pow_sub_one hP2 hPe hno hn3 h
      · exact no_odd_pow_add_one hP2 hPe hno hn3 h

section Dihedral

open DihedralGroup

theorem le_pPrimeCore_of_normal {C : Type*} [Group C] (M : Subgroup C) [M.Normal]
    (hM : Odd (Nat.card M)) : M ≤ pPrimeCore 2 C :=
  le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hM⟩

theorem conj_r {k : ℕ} (g : DihedralGroup k) (b : ZMod k) :
    g * r b * g⁻¹ = r b ∨ g * r b * g⁻¹ = (r b)⁻¹ := by
  rcases g with i | i
  · left
    simp only [inv_r, r_mul_r]
    congr 1
    ring
  · right
    simp only [inv_r, inv_sr, sr_mul_r, sr_mul_sr]
    congr 1
    ring

theorem exists_r_of_odd_orderOf {k : ℕ} {g : DihedralGroup k} (h : Odd (orderOf g)) :
    ∃ i, g = r i := by
  rcases g with i | i
  · exact ⟨i, rfl⟩
  · rw [orderOf_sr] at h
    exact absurd h (by decide)

theorem r_mem_zpowers {k : ℕ} [NeZero k] (i : ZMod k) :
    r i ∈ Subgroup.zpowers (r (1 : ZMod k)) := by
  refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
  rw [r_one_zpow]
  simp

variable {C : Type*} [Group C] {k : ℕ}

theorem odd_orderOf_pPrimeCore [Finite C] (c : pPrimeCore 2 C) : Odd (orderOf (c : C)) := by
  have h1 : orderOf c ∣ Nat.card (pPrimeCore 2 C) := orderOf_dvd_natCard c
  rw [Subgroup.orderOf_coe]
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right h1 (pPrimeCore_coprime_card (p := 2) (G := C)))

theorem isCyclic_pPrimeCore_dihedral [Finite C] [NeZero k] (φ : C ≃* DihedralGroup k) :
    IsCyclic ↥(pPrimeCore 2 C) := by
  have hrot : ∀ c : pPrimeCore 2 C, φ (c : C) ∈ Subgroup.zpowers (r (1 : ZMod k)) := by
    intro c
    have hodd : Odd (orderOf (φ (c : C))) := by
      rw [MulEquiv.orderOf_eq]
      exact odd_orderOf_pPrimeCore c
    obtain ⟨i, hi⟩ := exists_r_of_odd_orderOf hodd
    rw [hi]
    exact r_mem_zpowers i
  let ρ : pPrimeCore 2 C →* Subgroup.zpowers (r (1 : ZMod k)) :=
    ((φ.toMonoidHom).comp (pPrimeCore 2 C).subtype).codRestrict _ hrot
  refine isCyclic_of_injective ρ ?_
  intro a b hab
  have h1 : φ (a : C) = φ (b : C) := congrArg Subtype.val hab
  exact Subtype.ext (φ.injective h1)

theorem pPrimeCore_ne_bot_dihedral [NeZero k] (φ : C ≃* DihedralGroup k) {m : ℕ} (hm : Odd m)
    (hm1 : m ≠ 1) (hmk : m ∣ k) : pPrimeCore 2 C ≠ ⊥ := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  set g₁ : DihedralGroup k := (r (1 : ZMod k)) ^ (k / m) with hg₁
  have hdiv : k / m ≠ 0 := by
    have : 0 < k / m := Nat.div_pos (Nat.le_of_dvd hk0 hmk) (Nat.pos_of_ne_zero hm0)
    omega
  have hord : orderOf g₁ = m := by
    rw [hg₁, orderOf_pow_of_dvd hdiv (by rw [orderOf_r_one]; exact Nat.div_dvd_of_dvd hmk),
      orderOf_r_one, Nat.div_div_self hmk (by omega)]
  have hnormD : (Subgroup.zpowers g₁).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hg₁r : g₁ = r ((k / m : ℕ) : ZMod k) := by rw [hg₁, r_one_pow]
    have hconj : g * g₁ ^ j * g⁻¹ = (g * g₁ * g⁻¹) ^ j := (conj_zpow).symm
    rw [hconj]
    rcases conj_r g ((k / m : ℕ) : ZMod k) with h | h
    · rw [← hg₁r] at h
      rw [h]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [← hg₁r] at h
      rw [h, inv_zpow']
      exact Subgroup.zpow_mem_zpowers _ _
  have hcardD : Nat.card (Subgroup.zpowers g₁) = m := by rw [Nat.card_zpowers, hord]
  set M : Subgroup C := (Subgroup.zpowers g₁).map φ.symm.toMonoidHom with hM
  have hMn : M.Normal := hnormD.map _ φ.symm.surjective
  have hcardM : Nat.card M = m := by
    rw [hM, Subgroup.card_map_of_injective φ.symm.injective, hcardD]
  have hle : M ≤ pPrimeCore 2 C := by
    have : Odd (Nat.card M) := hcardM ▸ hm
    exact le_pPrimeCore_of_normal M this
  intro hbot
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hcardM
  exact hm1 hcardM.symm

end Dihedral

section Xu

variable {K : Type} [Group K]

theorem fixedSubgroup_conj (u : K) :
    fixedSubgroup K (MulAut.conj u) = Subgroup.centralizer {u} := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  show u * y * u⁻¹ = y ↔ y * u = u * y
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem xu_of_dihedral [Finite K] (x : MulAut K) {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (hm1 : m ≠ 1) (hmk : m ∣ k) (φ : ↥(fixedSubgroup K x) ≃* DihedralGroup k) :
    xu x ≠ ⊥ ∧ IsCyclic ↥(xu x) := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨fun h => ?_, ?_⟩
  · refine pPrimeCore_ne_bot_dihedral φ hm hm1 hmk ?_
    exact (Subgroup.map_eq_bot_iff_of_injective _ (fixedSubgroup K x).subtype_injective).mp h
  · exact isCyclic_of_surjective
      ((pPrimeCore 2 ↥(fixedSubgroup K x)).equivMapOfInjective _
        (fixedSubgroup K x).subtype_injective).toMonoidHom (MulEquiv.surjective _)
      (hH := isCyclic_pPrimeCore_dihedral φ)

end Xu

section L2

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

theorem exists_dihedral_data (hF : L2Field F) (hnfm : ¬ IsFM9 (Nat.card F)) (e : K ≃* L2 F)
    (x : MulAut K) (hx : x ∈ innDiagSub e) (hx2 : orderOf x = 2) :
    ∃ k m : ℕ, 2 ≤ k ∧ Odd m ∧ m ≠ 1 ∧ m ∣ k ∧
      Nonempty (↥(fixedSubgroup K x) ≃* DihedralGroup k) := by
  have hq5 : 5 ≤ Nat.card F := by
    obtain ⟨⟨t, ht⟩, h3⟩ := hF
    omega
  obtain ⟨ε, hε1, hε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hF.1
    by_cases h : t % 2 = 0
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  by_cases hin : x ∈ innAut K
  · obtain ⟨u, rfl⟩ := hin
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_conj_eq e u]
      exact hx2
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3a F hF K e ε hε1 hε d hd u hu2).2.1
    have φ' : ↥(fixedSubgroup K (MulAut.conj u)) ≃* DihedralGroup k :=
      (MulEquiv.subgroupCongr (fixedSubgroup_conj u)).trans ψ
    obtain ⟨j, m, hm, hkjm⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
    refine ⟨k, m, hk2, hm, ?_, ⟨2 ^ j, by rw [hkjm]; ring⟩, ⟨φ'⟩⟩
    intro hm1
    subst hm1
    apply hnfm
    obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact absurd hpodd (by decide)
    have hdp : d = 2 ^ (j + 1) := by rw [hkd, hkjm]; ring
    rw [hq]
    refine isFM9_of_pow hp hp2 hn (hq ▸ hq5) (a := j + 1) ?_
    rw [hq] at hd
    rw [← hdp]
    rcases hε1 with rfl | rfl
    · left
      omega
    · right
      omega
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
      ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨k, hkd, hk2, ⟨ψ⟩⟩ := (ivk_1_3b F hF K e ε hε1 hε d hd x hx hin hx2).2.1
    have hkodd : Odd k := by
      refine Nat.odd_iff.mpr ?_
      rcases hε1 with rfl | rfl <;> unfold Int.ModEq at hε <;> omega
    exact ⟨k, k, hk2, hkodd, by omega, dvd_rfl, ⟨ψ⟩⟩

end L2

section A7

variable {K : Type} [Group K]

theorem zpowers_le_xu [Finite K] (x k₀ : K) (h3 : orderOf k₀ = 3) (hc : k₀ * x = x * k₀)
    (hn : ∀ g : K, g * x = x * g → g * k₀ * g⁻¹ = k₀ ∨ g * k₀ * g⁻¹ = k₀ * k₀) :
    Subgroup.zpowers k₀ ≤ xu (MulAut.conj x) := by
  set C := fixedSubgroup K (MulAut.conj x) with hCdef
  have hmemC : ∀ g : K, g ∈ C ↔ g * x = x * g := fun g => by
    rw [hCdef, fixedSubgroup_conj, Subgroup.mem_centralizer_singleton_iff]
  have hMC : Subgroup.zpowers k₀ ≤ C := Subgroup.zpowers_le.mpr ((hmemC k₀).mpr hc)
  have hnorm : ((Subgroup.zpowers k₀).subgroupOf C).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn'
    show (g : K) * (n : K) * (g : K)⁻¹ ∈ Subgroup.zpowers k₀
    rw [← hj, ← conj_zpow]
    rcases hn (g : K) ((hmemC g).mp g.2) with h | h
    · rw [h]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [h]
      exact Subgroup.zpow_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_zpowers k₀) (Subgroup.mem_zpowers k₀)) j
  have hcard : Nat.card ↥((Subgroup.zpowers k₀).subgroupOf C) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMC).toEquiv, Nat.card_zpowers, h3]
  have hle := le_pPrimeCore_of_normal ((Subgroup.zpowers k₀).subgroupOf C)
    (by rw [hcard]; decide)
  calc Subgroup.zpowers k₀ = ((Subgroup.zpowers k₀).subgroupOf C).map C.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hMC).symm
    _ ≤ (pPrimeCore 2 ↥C).map C.subtype := Subgroup.map_mono hle

theorem isCyclic_xu_of_card_dvd [Finite K] (u : MulAut K)
    (h : Nat.card ↥(fixedSubgroup K u) ∣ 24) : IsCyclic ↥(xu u) := by
  have h1 : Nat.card ↥(xu u) = Nat.card ↥(pPrimeCore 2 ↥(fixedSubgroup K u)) :=
    Subgroup.card_map_of_injective (fixedSubgroup K u).subtype_injective
  have h2 : Nat.card ↥(pPrimeCore 2 ↥(fixedSubgroup K u)) ∣ 24 :=
    (Subgroup.card_subgroup_dvd_card _).trans h
  have h3 : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥(fixedSubgroup K u))) :=
    pPrimeCore_coprime_card
  have h4 : Nat.card ↥(xu u) ∣ 3 := by
    rw [h1]
    have h5 : Nat.Coprime (Nat.card ↥(pPrimeCore 2 ↥(fixedSubgroup K u))) 8 := by
      have := Nat.Coprime.pow_right 3 h3.symm
      simpa using this
    exact h5.dvd_of_dvd_mul_right (by simpa using h2)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_card_dvd_prime h4

theorem c3_normalized : ∀ x ∈ A7.C48list,
    x * (Equiv.swap 4 5 * Equiv.swap 5 6 : A7.S7) * x⁻¹ = (Equiv.swap 4 5 * Equiv.swap 5 6 : A7.S7) ∨
    x * (Equiv.swap 4 5 * Equiv.swap 5 6 : A7.S7) * x⁻¹ =
      (Equiv.swap 4 5 * Equiv.swap 5 6 : A7.S7) * (Equiv.swap 4 5 * Equiv.swap 5 6 : A7.S7) := by
  intro x hx
  obtain ⟨d, hd, e, he, rfl⟩ := A7.mem_C48list_iff.mp hx
  rw [A7.mem_D8list_iff] at hd
  rw [A7.mem_S3list_iff] at he
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem exists_threeCycle_of {t₀ : A7.S7} (h3 : orderOf t₀ = 3) (hs : Equiv.Perm.sign t₀ = 1)
    (hc : t₀ * A7.r ^ 2 = A7.r ^ 2 * t₀)
    (hn : ∀ x ∈ A7.C48list, x * t₀ * x⁻¹ = t₀ ∨ x * t₀ * x⁻¹ = t₀ * t₀) {y : A7.S7}
    (hy : ∃ c : A7.S7, c * A7.r ^ 2 * c⁻¹ = y) :
    ∃ t : A7.S7, orderOf t = 3 ∧ Equiv.Perm.sign t = 1 ∧ t * y = y * t ∧
      ∀ g : A7.S7, g * y = y * g → g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * t := by
  obtain ⟨c, rfl⟩ := hy
  refine ⟨c * t₀ * c⁻¹, ?_, ?_, ?_, ?_⟩
  · have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective t₀
    simpa [MulAut.conj_apply, h3] using this
  · simp [hs]
  · calc c * t₀ * c⁻¹ * (c * A7.r ^ 2 * c⁻¹) = c * (t₀ * A7.r ^ 2) * c⁻¹ := by group
      _ = c * (A7.r ^ 2 * t₀) * c⁻¹ := by rw [hc]
      _ = c * A7.r ^ 2 * c⁻¹ * (c * t₀ * c⁻¹) := by group
  · intro g hg
    have hg₀ : (c⁻¹ * g * c) * A7.r ^ 2 = A7.r ^ 2 * (c⁻¹ * g * c) := by
      calc (c⁻¹ * g * c) * A7.r ^ 2 = c⁻¹ * (g * (c * A7.r ^ 2 * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * A7.r ^ 2 * c⁻¹) * g) * c := by rw [hg]
        _ = A7.r ^ 2 * (c⁻¹ * g * c) := by group
    have key : g * (c * t₀ * c⁻¹) * g⁻¹ = c * ((c⁻¹ * g * c) * t₀ * (c⁻¹ * g * c)⁻¹) * c⁻¹ := by
      group
    rcases hn _ (A7.mem_C48list_of_commute hg₀) with h | h
    · left
      rw [key, h]
    · right
      rw [key, h]
      group

theorem exists_threeCycle {y : A7.S7} (hy : ∃ c : A7.S7, c * A7.r ^ 2 * c⁻¹ = y) :
    ∃ t : A7.S7, orderOf t = 3 ∧ Equiv.Perm.sign t = 1 ∧ t * y = y * t ∧
      ∀ g : A7.S7, g * y = y * g → g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * t :=
  exists_threeCycle_of A7.c3_order (by decide +kernel) A7.c3_comm_rsq c3_normalized hy

theorem xu_A7 [Finite K] (φ : K ≃* alternatingGroup (Fin 7)) (x : K) (hx : orderOf x = 2) :
    xu (MulAut.conj x) ≠ ⊥ ∧ IsCyclic ↥(xu (MulAut.conj x)) := by
  let ψ : K →* A7.S7 := (alternatingGroup (Fin 7)).subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := (alternatingGroup (Fin 7)).subtype_injective.comp φ.injective
  have hψmem : ∀ k : K, ψ k ∈ alternatingGroup (Fin 7) := fun k => (φ k).2
  have hψx : ∀ k : K, ψ k = (φ k : A7.S7) := fun k => rfl
  have hy2 : orderOf (ψ x) = 2 := by rw [orderOf_injective ψ hψ x]; exact hx
  have hyy : ψ x ^ 2 = 1 := by
    have := pow_orderOf_eq_one (ψ x)
    rwa [hy2] at this
  have hy1 : ψ x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2A : A7.r ^ 2 ∈ alternatingGroup (Fin 7) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hr2o : orderOf (A7.r ^ 2) = 2 := orderOf_eq_prime (by decide +kernel) A7.rsq_ne_one
  obtain ⟨c, -, hc⟩ := A7.involutions_conj_alternating hr2A (hψmem x) hr2o hy2
  obtain ⟨t, ht3, hts, htc, htn⟩ := exists_threeCycle ⟨c, hc⟩
  have hts' : t ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr hts
  set k₀ : K := φ.symm ⟨t, hts'⟩ with hk₀
  have hψk₀ : ψ k₀ = t := by simp [hψx, hk₀]
  have hk₀3 : orderOf k₀ = 3 := by rw [← orderOf_injective ψ hψ k₀, hψk₀, ht3]
  have hk₀c : k₀ * x = x * k₀ := hψ (by rw [map_mul, map_mul, hψk₀]; exact htc)
  have hk₀n : ∀ g : K, g * x = x * g → g * k₀ * g⁻¹ = k₀ ∨ g * k₀ * g⁻¹ = k₀ * k₀ := by
    intro g hg
    have hg' : ψ g * ψ x = ψ x * ψ g := by rw [← map_mul, ← map_mul, hg]
    rcases htn (ψ g) hg' with h | h
    · left
      apply hψ
      rw [map_mul, map_mul, map_inv, hψk₀]
      exact h
    · right
      apply hψ
      rw [map_mul, map_mul, map_inv, map_mul, hψk₀]
      exact h
  have hle := zpowers_le_xu x k₀ hk₀3 hk₀c hk₀n
  have hne : xu (MulAut.conj x) ≠ ⊥ := by
    intro hbot
    have h1 : k₀ ∈ xu (MulAut.conj x) := hle (Subgroup.mem_zpowers k₀)
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hk₀3
    omega
  refine ⟨hne, isCyclic_xu_of_card_dvd _ ?_⟩
  have hmap : (fixedSubgroup K (MulAut.conj x)).map ψ =
      Subgroup.centralizer {ψ x} ⊓ alternatingGroup (Fin 7) := by
    ext s
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk' : k * x = x * k := by
        rw [fixedSubgroup_conj] at hk
        exact Subgroup.mem_centralizer_singleton_iff.mp hk
      exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hk']),
        hψmem k⟩
    · intro hs
      obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.mp hs
      have hψs : ψ (φ.symm ⟨s, hs2⟩) = s := by simp [hψx]
      refine ⟨φ.symm ⟨s, hs2⟩, ?_, hψs⟩
      rw [SetLike.mem_coe, fixedSubgroup_conj, Subgroup.mem_centralizer_singleton_iff]
      apply hψ
      rw [map_mul, map_mul, hψs]
      exact Subgroup.mem_centralizer_singleton_iff.mp hs1
  have hcyc : (ψ x).cycleType = {2, 2} := by
    rw [← hc, Equiv.Perm.cycleType_conj, A7.rsq_cycleType]
  have hcard : Nat.card ↥(fixedSubgroup K (MulAut.conj x)) = 24 := by
    rw [← Subgroup.card_map_of_injective hψ, hmap]
    exact A7.card_centralizer_A7_two_two hcyc hyy hy1
  rw [hcard]

end A7

end Lemma118

open Lemma118 in
theorem ivk_1_18 :
    (∀ (F : Type) [Field F] [Finite F], L2Field F → ¬ IsFM9 (Nat.card F) →
      ∀ (K : Type) [Group K] [Finite K] (e : K ≃* L2 F), ∀ x : MulAut K, x ∈ innDiagSub e →
        orderOf x = 2 → xu x ≠ ⊥ ∧ IsCyclic ↥(xu x)) ∧
    (∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* alternatingGroup (Fin 7)) →
      ∀ x : K, orderOf x = 2 → xu (MulAut.conj x) ≠ ⊥ ∧ IsCyclic ↥(xu (MulAut.conj x))) := by
  refine ⟨?_, ?_⟩
  · intro F _ _ hF hnfm K _ _ e x hx hx2
    obtain ⟨k, m, hk, hm, hm1, hmk, ⟨φ⟩⟩ := exists_dihedral_data hF hnfm e x hx hx2
    exact xu_of_dihedral x hk hm hm1 hmk φ
  · intro K _ _ ⟨φ⟩ x hx
    exact xu_A7 φ x hx

end CFSG.GH74.GLS.IVK.Proofs2
