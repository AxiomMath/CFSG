module

public import CFSG.ClassicalInvolution.Asc77.AscL62Pair

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace ThreeTwelve

variable {G : Type} [Group G]

@[expose] def sqSub (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | ∃ x ∈ R, y = x * x}

theorem sq_mem_sqSub {R : Subgroup G} {x : G} (hx : x ∈ R) : x * x ∈ sqSub R :=
  Subgroup.subset_closure ⟨x, hx, rfl⟩

theorem conj_mem_sqSub {R : Subgroup G} {b n : G} (hb : b ∈ R) (hn : n ∈ sqSub R) :
    b * n * b⁻¹ ∈ sqSub R := by
  have : sqSub R ≤ (sqSub R).comap (MulAut.conj b).toMonoidHom := by
    rw [sqSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    show b * (x * x) * b⁻¹ ∈ sqSub R
    have : b * (x * x) * b⁻¹ = (b * x * b⁻¹) * (b * x * b⁻¹) := by group
    rw [this]
    exact sq_mem_sqSub (R.mul_mem (R.mul_mem hb hx) (R.inv_mem hb))
  exact this hn

theorem comm_mem_sqSub {R : Subgroup G} {a b : G} (hb : b ∈ R) (ha : a * a ∈ sqSub R)
    (hab : (a * b) * (a * b) ∈ sqSub R) : a * b * a⁻¹ * b⁻¹ ∈ sqSub R := by
  have e : a * b * a⁻¹ * b⁻¹ =
      ((a * b) * (a * b)) * (b⁻¹ * (a * a)⁻¹ * b⁻¹⁻¹) * (b * b)⁻¹ := by group
  rw [e]
  refine (sqSub R).mul_mem ((sqSub R).mul_mem hab ?_) ((sqSub R).inv_mem (sq_mem_sqSub hb))
  exact conj_mem_sqSub (R.inv_mem hb) ((sqSub R).inv_mem ha)

theorem exists_sq_not_mem_sqSub {S R : Subgroup G} (hRS : R ≤ S)
    (hnt : ∃ s ∈ S, ∃ x ∈ R, s * x * s⁻¹ * x⁻¹ ∉ sqSub R) :
    ∃ g ∈ S, g * g ∉ sqSub R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, x, hx, hsx⟩ := hnt
  exact hsx (comm_mem_sqSub hx (hcon s hs) (hcon (s * x) (S.mul_mem hs (hRS hx))))

variable [Finite G]

theorem conj_mem_of_card_eq_two_mul {S A : Subgroup G} (hAS : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) {s a : G} (hs : s ∈ S) (ha : a ∈ A) :
    s * a * s⁻¹ ∈ A := by
  by_cases hsA : s ∈ A
  · exact A.mul_mem (A.mul_mem hsA ha) (A.inv_mem hsA)
  by_contra hcon
  have hsa : s * a * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs (hAS ha)) (S.inv_mem hs)
  have h := AscL62.inv_mul_mem_of_index_two hAS hcard hs hsa hsA hcon
  have h2 : a * s⁻¹ ∈ A := by
    have e : s⁻¹ * (s * a * s⁻¹) = a * s⁻¹ := by group
    rwa [e] at h
  have h3 : s⁻¹ ∈ A := by
    have e : s⁻¹ = a⁻¹ * (a * s⁻¹) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem ha) h2
  exact hsA (by simpa using A.inv_mem h3)

theorem closure_eq_of_cyclic_index_two {S : Subgroup G} {g x : G} (hg : g ∈ S) (hx : x ∈ S)
    (hcard : Nat.card S = 2 * Nat.card (Subgroup.zpowers g)) (hxg : x ∉ Subgroup.zpowers g) :
    Subgroup.closure {g, x} = S := by
  have hle : Subgroup.closure ({g, x} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hg
    · exact hx
  have hA : Subgroup.zpowers g ≤ Subgroup.closure ({g, x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hxC : x ∈ Subgroup.closure ({g, x} : Set G) := Subgroup.subset_closure (by simp)
  have hne : Subgroup.closure ({g, x} : Set G) ≠ Subgroup.zpowers g := fun h => hxg (h ▸ hxC)
  have hd1 : Nat.card (Subgroup.zpowers g) ∣ Nat.card (Subgroup.closure ({g, x} : Set G)) :=
    Subgroup.card_dvd_of_le hA
  have hd2 : Nat.card (Subgroup.closure ({g, x} : Set G)) ∣ Nat.card S :=
    Subgroup.card_dvd_of_le hle
  obtain ⟨u, hu⟩ := hd1
  have hA0 : 0 < Nat.card (Subgroup.zpowers g) := Nat.card_pos
  have hu2 : u ∣ 2 := by
    rw [hu, hcard] at hd2
    have : Nat.card (Subgroup.zpowers g) * u ∣ Nat.card (Subgroup.zpowers g) * 2 := by
      rwa [mul_comm 2] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left hA0 this
  have hu1 : u ≠ 1 := by
    intro h1
    apply hne
    refine (Subgroup.eq_of_le_of_card_ge hA ?_).symm
    rw [hu, h1, mul_one]
  have hu2' : u = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hu2 with h | h
    · exact absurd h hu1
    · exact h
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, hu, hu2', mul_comm]

theorem isQuaternionSub_or_isSemidihedral_of_cyclic_index_two {S : Subgroup G} {g x : G} {m : ℕ}
    (hm : 2 ≤ m) (hg : g ∈ S) (hx : x ∈ S) (hgo : orderOf g = 2 ^ (m + 1))
    (hcard : Nat.card S = 2 * 2 ^ (m + 1)) (hxg : x ∉ Subgroup.zpowers g)
    (hxx : x * x = g ^ (2 ^ m)) (hxg2 : x * g ^ 2 * x⁻¹ = (g ^ 2)⁻¹) :
    IsQuaternionSub S ∨ IsSemidihedral S := by
  have hAcard : Nat.card (Subgroup.zpowers g) = 2 ^ (m + 1) := by rw [Nat.card_zpowers, hgo]
  have hAS : Subgroup.zpowers g ≤ S := Subgroup.zpowers_le.mpr hg
  have hcard' : Nat.card S = 2 * Nat.card (Subgroup.zpowers g) := by rw [hAcard]; exact hcard
  have hclos := closure_eq_of_cyclic_index_two hg hx hcard' hxg
  have h8 : 8 ≤ 2 ^ (m + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN : orderOf g / 2 = 2 ^ m := by rw [hgo, pow_succ]; omega
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (conj_mem_of_card_eq_two_mul hAS hcard' hx (Subgroup.mem_zpowers g))
  have h2 : g ^ (2 * j + 2) = 1 := by
    have e1 : g ^ (2 * j + 2) = (g ^ j) ^ 2 * g ^ 2 := by group
    rw [e1, hj]
    calc (x * g * x⁻¹) ^ 2 * g ^ 2 = (x * g ^ 2 * x⁻¹) * g ^ 2 := by rw [conj_pow]
      _ = 1 := by rw [hxg2]; group
  have hdvd : ((2 ^ (m + 1) : ℕ) : ℤ) ∣ 2 * j + 2 := by
    rw [← hgo]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  obtain ⟨t, ht⟩ := hdvd
  have hj1 : j = (2 ^ m : ℤ) * t - 1 := by
    push_cast at ht
    have : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [this] at ht
    linarith
  have hg2N : g ^ ((2 ^ (m + 1) : ℕ) : ℤ) = 1 := by
    rw [← hgo, zpow_natCast, pow_orderOf_eq_one]
  rcases Int.even_or_odd' t with ⟨u, rfl | rfl⟩
  ·
    have hgj : x * g * x⁻¹ = g⁻¹ := by
      rw [← hj, hj1]
      have e : g ^ ((2 ^ m : ℤ) * (2 * u) - 1) = (g ^ ((2 ^ (m + 1) : ℕ) : ℤ)) ^ u * g⁻¹ := by
        push_cast
        group
      rw [e, hg2N]
      group
    refine Or.inl ⟨g, x, by omega, by rw [hgo]; exact hcard, ?_, hgj, hclos⟩
    rw [hN, hxx]
  ·
    have hgj : x * g * x⁻¹ = g ^ (2 ^ m - 1) := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [← hj, hj1]
      have e : g ^ ((2 ^ m : ℤ) * (2 * u + 1) - 1) =
          (g ^ ((2 ^ (m + 1) : ℕ) : ℤ)) ^ u * g ^ ((2 ^ m - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub h1]
        group
      rw [e, hg2N, one_zpow, one_mul, zpow_natCast]
    have hxgg : x * g ∉ Subgroup.zpowers g := by
      intro h
      apply hxg
      have : x = (x * g) * g⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers g))
    refine Or.inr ⟨g, x * g, by omega, by rw [hgo]; exact hcard, ?_, hxgg, ?_, ?_⟩
    · calc x * g * (x * g) = (x * g * x⁻¹) * (x * x) * g := by group
        _ = g ^ (2 ^ m - 1) * g ^ (2 ^ m) * g := by rw [hgj, hxx]
        _ = g ^ (2 ^ (m + 1)) := by
            have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
            rw [← pow_add, ← pow_succ]
            have : 2 ^ m - 1 + 2 ^ m + 1 = 2 ^ (m + 1) := by rw [pow_succ]; omega
            rw [this]
        _ = 1 := by rw [← hgo]; exact pow_orderOf_eq_one g
    · calc x * g * g * (x * g)⁻¹ = x * g * x⁻¹ := by group
        _ = g ^ (orderOf g / 2 - 1) := by rw [hN, hgj]
    · have : Subgroup.closure ({g, x * g} : Set G) = Subgroup.closure ({g, x} : Set G) := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp))
        · rw [Subgroup.closure_le]
          rintro y (rfl | rfl)
          · exact Subgroup.subset_closure (by simp)
          · have e : y = (y * g) * g⁻¹ := by group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
              (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      rw [this, hclos]

theorem conjSub_eq_of_card_eq_two_mul {S R : Subgroup G} (hRS : R ≤ S)
    (hidx : Nat.card S = 2 * Nat.card R) {s : G} (hs : s ∈ S) : conjSub s R = R := by
  have hle : conjSub s R ≤ R := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := conj_mem_of_card_eq_two_mul hRS hidx hs hx
    simpa [mul_assoc] using this
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub])

theorem sq_mem_cyclic {S R Y : Subgroup G} {z y₀ : G} {m : ℕ} (hR : IsQuatSub R)
    (hz : IsUniqueInvolution R z) (hRS : R ≤ S) (hidx : Nat.card S = 2 * Nat.card R)
    (hYR : Y ≤ R) (hYc : IsCyclic ↥Y) (hYcard : Nat.card R = 2 * Nat.card Y)
    (hYinv : ∀ g ∈ S, conjSub g Y = Y) (hy₀ : Subgroup.zpowers y₀ = Y)
    (hord : orderOf y₀ = 2 ^ m) (hm : 2 ≤ m) {g : G} (hg : g ∈ S) (hgR : g ∉ R) :
    g * g ∈ Y := by
  have hgg : g * g ∈ R := by
    by_contra hcon
    have := AscL62.inv_mul_mem_of_index_two hRS hidx hg (S.mul_mem hg hg) hgR hcon
    exact hgR (by simpa using this)
  by_contra hgY
  have hy₀Y : y₀ ∈ Y := hy₀ ▸ Subgroup.mem_zpowers y₀
  have hinv := AscL62.conj_eq_inv_of_not_mem hR hz hYR hYc hYcard hgg hgY hy₀Y
  have hgy : g * y₀ * g⁻¹ ∈ Y := by
    have h1 : y₀ ∈ conjSub g⁻¹ Y := by rw [hYinv g⁻¹ (S.inv_mem hg)]; exact hy₀Y
    simpa [mem_conjSub_iff] using h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hy₀ ▸ hgy)
  have e1 : (g * g) * y₀ * (g * g)⁻¹ = y₀ ^ (k * k) := by
    calc (g * g) * y₀ * (g * g)⁻¹ = g * (g * y₀ * g⁻¹) * g⁻¹ := by group
      _ = g * y₀ ^ k * g⁻¹ := by rw [← hk]
      _ = (g * y₀ * g⁻¹) ^ k := by rw [conj_zpow]
      _ = (y₀ ^ k) ^ k := by rw [← hk]
      _ = y₀ ^ (k * k) := by rw [← zpow_mul]
  have e2 : y₀ ^ (k * k + 1) = 1 := by
    have : y₀ ^ (k * k) = y₀⁻¹ := e1.symm.trans hinv
    rw [zpow_add_one, this, inv_mul_cancel]
  have hdvd : ((2 ^ m : ℕ) : ℤ) ∣ k * k + 1 := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr e2
  have h4 : ((4 : ℕ) : ℤ) ∣ k * k + 1 := by
    refine dvd_trans ?_ hdvd
    exact_mod_cast (Nat.pow_dvd_pow 2 hm : 2 ^ 2 ∣ 2 ^ m)
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (k * k + 1) 4).mpr h4
  push_cast at h0
  revert h0
  generalize (k : ZMod 4) = a
  revert a
  decide

omit [Finite G] in
theorem orderOf_zpow_odd {y : G} {m : ℕ} (hy : orderOf y = 2 ^ m) {e : ℤ} (he : Odd e) :
    orderOf (y ^ e) = 2 ^ m := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · have hn : Odd n := Int.odd_coe_nat n |>.mp he
    rw [zpow_natCast, orderOf_pow' _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hn)).ne', hy]
    have hcop : Nat.Coprime (2 ^ m) n := (Nat.coprime_two_left.mpr hn).pow_left m
    rw [hcop.gcd_eq_one, Nat.div_one]
  · have hn : Odd n := by
      have : Odd (-(n : ℤ)) := he
      simpa using this
    rw [zpow_neg, zpow_natCast, orderOf_inv, orderOf_pow' _ (Nat.pos_of_ne_zero
      (by rintro rfl; simp at hn)).ne', hy]
    have hcop : Nat.Coprime (2 ^ m) n := (Nat.coprime_two_left.mpr hn).pow_left m
    rw [hcop.gcd_eq_one, Nat.div_one]

end ThreeTwelve

variable {G : Type} [Group G] [Finite G]

theorem l3_12 {S R : Subgroup G} {z : G} (hS2 : IsPGroup 2 ↥S) (hRS : R ≤ S)
    (hidx : Nat.card S = 2 * Nat.card R) (hR : IsQuatSub R) (hz : IsUniqueInvolution R z)
    (hnt : ∃ s ∈ S, ∃ x ∈ R, s * x * s⁻¹ * x⁻¹ ∉ ThreeTwelve.sqSub R) :
    IsQuaternionSub S ∨ IsSemidihedral S := by
  open ThreeTwelve in
  obtain ⟨Y, hYR, hYc, hYcard, hYinv⟩ := AscL62.exists_invariant_cyclic hR hz hS2
    (fun y hy => conjSub_eq_of_card_eq_two_mul hRS hidx hy)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : G, Subgroup.zpowers y₀ = Y := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Y)
    refine ⟨g, le_antisymm (Subgroup.zpowers_le.mpr g.2) fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hy₀Y : y₀ ∈ Y := hy₀ ▸ Subgroup.mem_zpowers y₀
  have hY4 : 4 ≤ Nat.card Y := AscL62.four_le_natCard_of_index_two hR hYcard
  have hycard : Nat.card Y = orderOf y₀ := by rw [← hy₀, Nat.card_zpowers]
  obtain ⟨m, hm'⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hS2 (hRS (hYR hy₀Y))
  have hm : 2 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hYm : Nat.card Y = 2 ^ m := by rw [hycard, hm']
  obtain ⟨x₀, hx₀R, hx₀Y⟩ : ∃ x ∈ R, x ∉ Y := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show R ≤ Y from hcon)
    omega
  obtain ⟨g, hgS, hgsq⟩ := exists_sq_not_mem_sqSub hRS hnt
  have hgR : g ∉ R := fun h => hgsq (sq_mem_sqSub h)
  have hgY : g * g ∈ Y := sq_mem_cyclic hR hz hRS hidx hYR hYc hYcard hYinv hy₀ hm' hm hgS hgR
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp (hy₀ ▸ hgY)
  have heodd : Odd e := by
    rcases Int.even_or_odd e with ⟨u, hu⟩ | h
    · exfalso
      apply hgsq
      have : g * g = (y₀ ^ u) * (y₀ ^ u) := by
        rw [← he, hu, ← zpow_add]
      rw [this]
      exact sq_mem_sqSub (R.zpow_mem (hYR hy₀Y) u)
    · exact h
  have hord2 : orderOf (g * g) = 2 ^ m := by rw [← he]; exact orderOf_zpow_odd hm' heodd
  have hgg2 : g ^ 2 = g * g := pow_two g
  have hgo : orderOf g = 2 ^ (m + 1) := by
    obtain ⟨j, hj⟩ := AscL62.orderOf_eq_two_pow_of_isPGroup hS2 hgS
    have hj0 : j ≠ 0 := by
      rintro rfl
      have h1 : orderOf g = 1 := by simpa using hj
      exact hgR (by rw [orderOf_eq_one_iff.mp h1]; exact R.one_mem)
    have h1 : orderOf (g ^ 2) = orderOf g / Nat.gcd (orderOf g) 2 := orderOf_pow' _ (by norm_num)
    rw [hgg2, hord2, hj] at h1
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hgcd : Nat.gcd (2 ^ (j' + 1)) 2 = 2 := by
      rw [pow_succ]
      exact Nat.gcd_eq_right (dvd_mul_left 2 _)
    rw [hgcd, pow_succ, Nat.mul_div_cancel _ (by norm_num)] at h1
    have : m = j' := Nat.pow_right_injective (le_refl 2) h1
    rw [hj, this]
  have hSc : Nat.card S = 2 * 2 ^ (m + 1) := by rw [hidx, hYcard, hYm]; ring
  have hx₀S : x₀ ∈ S := hRS hx₀R
  have hzx : x₀ * x₀ = z := AscL62.sq_eq_of_not_mem hR hz hYR hYc hYcard hx₀R hx₀Y
  refine isQuaternionSub_or_isSemidihedral_of_cyclic_index_two hm hgS hx₀S hgo hSc ?_ ?_ ?_
  ·
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases Int.even_or_odd' i with ⟨u, rfl | rfl⟩
    · apply hx₀Y
      have h2u : g ^ (2 * u) = (g * g) ^ u := by rw [zpow_mul, zpow_two]
      rw [← hi, h2u]
      exact Y.zpow_mem hgY u
    · apply hgR
      have h2u : g ^ (2 * u) = (g * g) ^ u := by rw [zpow_mul, zpow_two]
      have : g = ((g * g) ^ u)⁻¹ * x₀ := by
        rw [← hi, zpow_add_one, h2u]
        group
      rw [this]
      exact R.mul_mem (R.inv_mem (hYR (Y.zpow_mem hgY u))) hx₀R
  ·
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hwR : (g * g) ^ (2 ^ (m - 1)) ∈ R := R.pow_mem (hYR hgY) _
    have hww : (g * g) ^ (2 ^ (m - 1)) * (g * g) ^ (2 ^ (m - 1)) = 1 := by
      rw [← pow_add, ← two_mul, ← hpow, ← hord2]
      exact pow_orderOf_eq_one _
    have hw1 : (g * g) ^ (2 ^ (m - 1)) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hord2] at this
      have h3 := Nat.le_of_dvd (pow_pos (by norm_num) _) this
      have h4 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hwz : (g * g) ^ (2 ^ (m - 1)) = z := by
      rcases hz.unique _ hwR hww with h | h
      · exact absurd h hw1
      · exact h
    rw [hzx, ← hwz, ← hgg2, ← pow_mul, ← hpow]
  · rw [hgg2]
    exact AscL62.conj_eq_inv_of_not_mem hR hz hYR hYc hYcard hx₀R hx₀Y hgY

end CFSG.ClassicalInvolution.Asc77
