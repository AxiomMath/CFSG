module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymSub

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym

open CFSG.Open Subgroup

variable {R : Type*} [Group R]

theorem eq_one_of_pow_two_pow_three {z : R} (h2 : ∃ i : ℕ, z ^ 2 ^ i = 1)
    (h3 : ∃ j : ℕ, z ^ 3 ^ j = 1) : z = 1 := by
  obtain ⟨i, hi⟩ := h2
  obtain ⟨j, hj⟩ := h3
  have h4 : z ^ Nat.gcd (2 ^ i) (3 ^ j) = 1 := pow_gcd_eq_one.2 ⟨hi, hj⟩
  have hcop : Nat.gcd (2 ^ i) (3 ^ j) = 1 :=
    Nat.Coprime.pow i j (by norm_num : Nat.Coprime 2 3)
  rwa [hcop, pow_one] at h4

section Core

theorem zpowers_sup_eq_of_card_nine {M : Type*} [Group M] [Finite M] (hcard : Nat.card M = 9)
    {u v : M} (hu3 : orderOf u = 3) (hv3 : orderOf v = 3) (hne : v ∉ zpowers u) :
    zpowers u ⊔ zpowers v = ⊤ := by
  have h1 : Nat.card (zpowers u) = 3 := by rw [Nat.card_zpowers, hu3]
  have hdvd : Nat.card (zpowers u ⊔ zpowers v : Subgroup M) ∣ 9 := by
    rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
  have h3 : 3 ∣ Nat.card (zpowers u ⊔ zpowers v : Subgroup M) := by
    rw [← h1]; exact Subgroup.card_dvd_of_le le_sup_left
  have hne3 : Nat.card (zpowers u ⊔ zpowers v : Subgroup M) ≠ 3 := by
    intro h
    have : zpowers u = zpowers u ⊔ zpowers v :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h1, h])
    apply hne
    rw [this]
    exact (le_sup_right : zpowers v ≤ zpowers u ⊔ zpowers v) (Subgroup.mem_zpowers v)
  have h9 : Nat.card (zpowers u ⊔ zpowers v : Subgroup M) = 9 := by
    obtain ⟨k, hk, hk'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).1 (show _ ∣ 3 ^ 2 by simpa using hdvd)
    interval_cases k
    · exact absurd h3 (by rw [hk']; norm_num)
    · exact absurd hk' hne3
    · simpa using hk'
  apply Subgroup.eq_top_of_card_eq
  rw [h9, hcard]

theorem core_comm {M : Type*} [CommGroup M] [Finite M] (hcard : Nat.card M = 9)
    (σ τ : MulAut M) {a a' c : M} (ha1 : a ≠ 1) (ha3 : a ^ 3 = 1) (ha'1 : a' ≠ 1)
    (ha'3 : a' ^ 3 = 1) (ha' : a' ∉ zpowers a) (hσa : σ a = a⁻¹) (hτa' : τ a' = a'⁻¹)
    (hσc : σ c = c) (hτc : τ c = c) (hc1 : c ≠ 1) (hw : ∃ e : ℕ, (σ * τ) ^ (2 ^ e) = 1) :
    False := by
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hoa' : orderOf a' = 3 := orderOf_eq_prime ha'3 ha'1
  have htop : zpowers a ⊔ zpowers a' = ⊤ := zpowers_sup_eq_of_card_nine hcard hoa hoa' ha'
  have hexp : ∀ x : M, x ^ 3 = 1 := by
    intro x
    have hx : x ∈ zpowers a ⊔ zpowers a' := by rw [htop]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (i : ℤ),
      mul_comm (j : ℤ), zpow_mul, zpow_mul]
    simp [← zpow_natCast, ha3, ha'3]
  have hoc : orderOf c = 3 := orderOf_eq_prime (hexp c) hc1
  have hsq : ∀ z : M, z ^ 2 = 1 → z = 1 := fun z hz => by
    have h3 := hexp z
    calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, hz]; group
  have hca : c ∉ zpowers a := by
    intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [map_zpow, hσa, inv_zpow] at hσc
    have : (a ^ k) ^ 2 = 1 := by
      have h2 : (a ^ k)⁻¹ = a ^ k := hσc
      calc (a ^ k) ^ 2 = a ^ k * a ^ k := pow_two _
        _ = a ^ k * (a ^ k)⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    exact hc1 (hsq _ this) |>.elim
  have hca' : c ∉ zpowers a' := by
    intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    rw [map_zpow, hτa', inv_zpow] at hτc
    have : (a' ^ k) ^ 2 = 1 := by
      have h2 : (a' ^ k)⁻¹ = a' ^ k := hτc
      calc (a' ^ k) ^ 2 = a' ^ k * a' ^ k := pow_two _
        _ = a' ^ k * (a' ^ k)⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    exact hc1 (hsq _ this) |>.elim
  have htopa : zpowers a ⊔ zpowers c = ⊤ := zpowers_sup_eq_of_card_nine hcard hoa hoc hca
  have htopa' : zpowers a' ⊔ zpowers c = ⊤ := zpowers_sup_eq_of_card_nine hcard hoa' hoc hca'
  have hσx : ∀ x : M, σ x * x ∈ zpowers c := by
    intro x
    have hx : x ∈ zpowers a ⊔ zpowers c := by rw [htopa]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_mul, map_zpow, map_zpow, hσa, hσc, inv_zpow]
    refine ⟨2 * j, ?_⟩
    calc c ^ (2 * j) = (a ^ i)⁻¹ * a ^ i * (c ^ j * c ^ j) := by
          rw [inv_mul_cancel, one_mul, ← zpow_add, two_mul]
      _ = (a ^ i)⁻¹ * c ^ j * (a ^ i * c ^ j) := by ac_rfl
  have hτx : ∀ x : M, τ x * x ∈ zpowers c := by
    intro x
    have hx : x ∈ zpowers a' ⊔ zpowers c := by rw [htopa']; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_mul, map_zpow, map_zpow, hτa', hτc, inv_zpow]
    refine ⟨2 * j, ?_⟩
    calc c ^ (2 * j) = (a' ^ i)⁻¹ * a' ^ i * (c ^ j * c ^ j) := by
          rw [inv_mul_cancel, one_mul, ← zpow_add, two_mul]
      _ = (a' ^ i)⁻¹ * c ^ j * (a' ^ i * c ^ j) := by ac_rfl
  set w : MulAut M := σ * τ with hwdef
  have hwx : ∀ x : M, w x * x⁻¹ ∈ zpowers c := by
    intro x
    obtain ⟨m, hm⟩ := hτx x
    obtain ⟨m', hm'⟩ := hσx (τ x)
    have hm1 : τ x * x = c ^ m := hm.symm
    have hm2 : σ (τ x) * τ x = c ^ m' := hm'.symm
    refine ⟨m' - m, ?_⟩
    show c ^ (m' - m) = σ (τ x) * x⁻¹
    have e1 : τ x = c ^ m * x⁻¹ := by rw [← hm1]; group
    have e2 : σ (τ x) = c ^ m' * (τ x)⁻¹ := by rw [← hm2]; group
    calc c ^ (m' - m) = c ^ m' * (c ^ m)⁻¹ := by rw [zpow_sub]
      _ = c ^ m' * (c ^ m)⁻¹ * (x * x⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = c ^ m' * (c ^ m * x⁻¹)⁻¹ * x⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          simp only [mul_comm, mul_left_comm, mul_assoc]
      _ = σ (τ x) * x⁻¹ := by rw [← e1, ← e2]
  have hwc : w c = c := by
    show σ (τ c) = c
    rw [hτc, hσc]
  obtain ⟨e, he⟩ := hw
  have hwtriv : ∀ x : M, w x = x := by
    intro x
    obtain ⟨k, hk⟩ := hwx x
    set y : M := w x * x⁻¹ with hy
    have hyc : y = c ^ k := hk.symm
    have hwy : w y = y := by rw [hyc, map_zpow, hwc]
    have hwx' : w x = y * x := by rw [hy]; group
    have key : ∀ n : ℕ, (w ^ n) x = y ^ n * x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hwy, hwx', pow_succ]
        group
    have h1 : y ^ (2 ^ e) = 1 := by
      have := key (2 ^ e)
      rw [he] at this
      have h2 : y ^ (2 ^ e) * x = x := by rw [← this]; rfl
      calc y ^ (2 ^ e) = y ^ (2 ^ e) * x * x⁻¹ := by group
        _ = 1 := by rw [h2]; group
    have h3 : y ^ 3 = 1 := hexp y
    have h4 : y ^ (Nat.gcd 3 (2 ^ e)) = 1 := pow_gcd_eq_one.2 ⟨h3, h1⟩
    have hcop : Nat.gcd 3 (2 ^ e) = 1 :=
      Nat.Coprime.pow_right e (by norm_num : Nat.Coprime 3 2)
    rw [hcop, pow_one] at h4
    rw [hwx', h4, one_mul]
  have hσa' : σ a' = a'⁻¹ := by
    have h1 : σ (τ a') = a' := hwtriv a'
    rw [hτa', map_inv] at h1
    exact inv_eq_iff_eq_inv.1 h1
  have hx : a' ∈ zpowers a ⊔ zpowers c := by rw [htopa]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [← hyz, map_mul, map_zpow, map_zpow, hσa, hσc, inv_zpow, mul_inv_rev] at hσa'
  have hz2 : (c ^ j) ^ 2 = 1 := by
    have h1 : (a ^ i)⁻¹ * c ^ j = (c ^ j)⁻¹ * (a ^ i)⁻¹ := hσa'
    have h2 : c ^ j = (c ^ j)⁻¹ := by
      calc c ^ j = (a ^ i) * ((a ^ i)⁻¹ * c ^ j) := by group
        _ = (a ^ i) * ((c ^ j)⁻¹ * (a ^ i)⁻¹) := by rw [h1]
        _ = (c ^ j)⁻¹ := by simp [mul_comm, mul_left_comm]
    calc (c ^ j) ^ 2 = c ^ j * c ^ j := pow_two _
      _ = c ^ j * (c ^ j)⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel _
  have hz1 : c ^ j = 1 := hsq _ hz2
  apply ha'
  rw [← hyz, hz1, mul_one]
  exact Subgroup.zpow_mem_zpowers a i

theorem false_of_two_symThree [Finite R] (hO2 : CFSG.pCore 2 R = ⊥)
    {X X' : Subgroup R} (hX : IsSymThree X) (hX' : IsSymThree X') (hne : X ≠ X')
    (hXs : IsSubnormal X ⊤) (hXs' : IsSubnormal X' ⊤)
    (h9 : ∀ U : Subgroup R, IsPGroup 3 U → Nat.card U ≤ 9) (T : Sylow 2 R) {c : R}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hcT : c ∈ normalizer ((T : Subgroup R) : Set R)) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2' := eq_bot_of_subnormal_isPGroup_two hO2
  set N : Subgroup R := CFSG.pCore 3 R with hN
  haveI hNn : N.Normal := CFSG.pCore_normal
  have hN3 : IsPGroup 3 N := CFSG.pCore_isPGroup
  obtain ⟨a, haX, ha1, ha3, hXa, -, -⟩ := symThree_data hX
  obtain ⟨a', ha'X', ha1', ha3', hXa', -, -⟩ := symThree_data hX'
  have haN : a ∈ N := mem_pCore_three hX hXs haX ha3 ha1
  have ha'N : a' ∈ N := mem_pCore_three hX' hXs' ha'X' ha3' ha1'
  have ha'not : a' ∉ zpowers a := by
    intro h
    have h1 : a' ∈ X := (Subgroup.zpowers_le.2 haX) h
    exact hne (eq_of_shared_three hO2' hX hX' hXs hXs' h1 ha'X' ha3' ha1')
  have hcardN : Nat.card N = 9 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN3
    have hle9 : 3 ^ k ≤ 9 := hk ▸ h9 N hN3
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
    have hge : 2 ≤ k := by
      by_contra hk1
      push Not at hk1
      have hk1' : k ≤ 1 := by omega
      have hN3le : Nat.card N ≤ 3 := by
        rw [hk]
        calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1'
          _ = 3 := by norm_num
      have hza : zpowers a ≤ N := Subgroup.zpowers_le.2 haN
      have hcard_a : Nat.card (zpowers a) = 3 := by
        rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
      have : zpowers a = N := Subgroup.eq_of_le_of_card_ge hza (by rw [hcard_a]; exact hN3le)
      exact ha'not (this ▸ ha'N)
    have : k = 2 := le_antisymm hk2 hge
    rw [hk, this]
    norm_num
  have hcN : c ∈ N := by
    have hzc : IsPGroup 3 (zpowers c) := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
      norm_num
    have hU3 : IsPGroup 3 ↥(zpowers c ⊔ N) := IsPGroup.to_sup_of_normal_right hzc hN3
    have hU := h9 _ hU3
    have hEq : N = zpowers c ⊔ N :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardN]; exact hU)
    rw [hEq]
    exact (le_sup_left : zpowers c ≤ zpowers c ⊔ N) (Subgroup.mem_zpowers c)
  have hcT' : ∀ t ∈ (T : Subgroup R), t * c = c * t := by
    intro t ht
    have h1 : c * t⁻¹ * c⁻¹ ∈ (T : Subgroup R) := by
      have := (Subgroup.mem_normalizer_iff.1 hcT t⁻¹).1 ((T : Subgroup R).inv_mem ht)
      exact this
    have h2 : t * c * t⁻¹ * c⁻¹ ∈ (T : Subgroup R) := by
      have := (T : Subgroup R).mul_mem ht h1
      simpa [mul_assoc] using this
    have h3 : t * c * t⁻¹ * c⁻¹ ∈ N := by
      have : t * c * t⁻¹ ∈ N := hNn.conj_mem c hcN t
      exact N.mul_mem this (N.inv_mem hcN)
    have h4 : t * c * t⁻¹ * c⁻¹ = 1 := by
      refine eq_one_of_pow_two_pow_three ?_ ?_
      · have := T.isPGroup' ⟨_, h2⟩
        obtain ⟨i, hi⟩ := this
        exact ⟨i, by simpa using congrArg Subtype.val hi⟩
      · have := hN3 ⟨_, h3⟩
        obtain ⟨j, hj⟩ := this
        exact ⟨j, by simpa using congrArg Subtype.val hj⟩
    calc t * c = (t * c * t⁻¹ * c⁻¹) * c * t := by group
      _ = c * t := by rw [h4]; group
  have hcomm : ∀ x y : N, x * y = y * x :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hcardN]; norm_num)
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
  obtain ⟨s, hsT, hsX, hs2, hs1⟩ := exists_involution_mem_sylow hX hXs T
  obtain ⟨s', hs'T, hs'X', hs'2, hs'1⟩ := exists_involution_mem_sylow hX' hXs' T
  obtain ⟨hsa, -⟩ := hXa s hsX hs2 hs1
  obtain ⟨hs'a', -⟩ := hXa' s' hs'X' hs'2 hs'1
  have hsc : s * c * s⁻¹ = c := by
    rw [hcT' s hsT]; group
  have hs'c : s' * c * s'⁻¹ = c := by
    rw [hcT' s' hs'T]; group
  have hw : ∃ e : ℕ, (MulAut.conjNormal s * MulAut.conjNormal s' : MulAut N) ^ (2 ^ e) = 1 := by
    have hmem : s * s' ∈ (T : Subgroup R) := (T : Subgroup R).mul_mem hsT hs'T
    obtain ⟨e, he⟩ := (T.isPGroup') ⟨s * s', hmem⟩
    refine ⟨e, ?_⟩
    have he' : (s * s') ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
    rw [← map_mul, ← map_pow, he', map_one]
  refine core_comm (M := ↥N) hcardN (MulAut.conjNormal s) (MulAut.conjNormal s')
    (a := ⟨a, haN⟩) (a' := ⟨a', ha'N⟩) (c := ⟨c, hcN⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw
  · exact fun h => ha1 (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using ha3)
  · exact fun h => ha1' (congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using ha3')
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    apply ha'not
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    simpa using congrArg Subtype.val hk
  · exact Subtype.ext (by simpa using hsa)
  · exact Subtype.ext (by simpa using hs'a')
  · exact Subtype.ext (by simpa using hsc)
  · exact Subtype.ext (by simpa using hs'c)
  · exact fun h => hc1 (congrArg Subtype.val h)

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym
