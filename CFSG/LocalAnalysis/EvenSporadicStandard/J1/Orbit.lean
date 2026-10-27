module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.GroupAction.Period
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

theorem orbit_of_prime_order {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (σ : MulAut E) (hσ : orderOf σ = 7) :
    (∀ x : E, x ≠ 1 → σ x ≠ x) ∧ ∀ x y : E, x ≠ 1 → y ≠ 1 → ∃ i : ℕ, (σ ^ i) x = y := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 8 := by rw [← Nat.card_eq_fintype_card, hE]
  have h7 : σ ^ 7 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hperiod : ∀ x : E, σ x ≠ x → MulAction.period σ x = 7 := by
    intro x hx
    have hdvd : MulAction.period σ x ∣ 7 := hσ ▸ MulAction.period_dvd_orderOf σ x
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
    · exact absurd (MulAction.period_eq_one_iff.mp h) hx
    · exact h
  have hlt : ∀ x : E, σ x ≠ x → ∀ i j : ℕ, i < j → j < 7 → (σ ^ i) x ≠ (σ ^ j) x := by
    intro x hx i j hij hj heq
    have hk : (σ ^ (j - i)) x = x := by
      have h1 : (σ ^ j) x = (σ ^ i) ((σ ^ (j - i)) x) := by
        rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le]
      exact (σ ^ i).injective (by rw [← h1]; exact heq.symm)
    have hdvd : MulAction.period σ x ∣ j - i :=
      MulAction.pow_smul_eq_iff_period_dvd.mp hk
    rw [hperiod x hx] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hinj : ∀ x : E, σ x ≠ x → Function.Injective (fun i : Fin 7 => (σ ^ (i : ℕ)) x) := by
    intro x hx i j hij
    by_contra hne
    have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with h | h
    · exact hlt x hx i j h j.2 hij
    · exact hlt x hx j i h i.2 hij.symm
  have hsurj : ∀ x : E, x ≠ 1 → σ x ≠ x → ∀ y : E, y ≠ 1 → ∃ i : ℕ, (σ ^ i) x = y := by
    intro x hx1 hx y hy
    set S : Finset E := Finset.univ.image (fun i : Fin 7 => (σ ^ (i : ℕ)) x) with hS
    have hSsub : S ⊆ Finset.univ.erase 1 := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h1
      apply hx1
      exact (σ ^ (i : ℕ)).injective (by rw [h1, map_one])
    have hScard : S.card = 7 := by
      rw [hS, Finset.card_image_of_injective _ (hinj x hx)]; simp
    have hEcard : (Finset.univ.erase (1 : E)).card = 7 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
    have hSeq : S = Finset.univ.erase 1 := Finset.eq_of_subset_of_card_le hSsub (by omega)
    have hy' : y ∈ S := by rw [hSeq]; exact Finset.mem_erase.mpr ⟨hy, Finset.mem_univ _⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy'
    exact ⟨i, hi⟩
  obtain ⟨x₁, hx₁, hmv⟩ : ∃ x₁ : E, x₁ ≠ 1 ∧ σ x₁ ≠ x₁ := by
    by_contra h
    push Not at h
    have h1 : σ = 1 := by
      ext x
      by_cases hx : x = 1
      · subst hx; simp
      · simpa using h x hx
    rw [h1, orderOf_one] at hσ
    omega
  have htrans := hsurj x₁ hx₁ hmv
  refine ⟨fun x hx hfix => ?_, fun x y hx hy => ?_⟩
  · obtain ⟨i, hi⟩ := htrans x hx
    apply hmv
    refine (σ ^ i).injective ?_
    calc (σ ^ i) (σ x₁) = σ ((σ ^ i) x₁) := by
          rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, ← pow_succ']
      _ = x := by rw [hi]; exact hfix
      _ = (σ ^ i) x₁ := hi.symm
  · obtain ⟨i, hi⟩ := htrans x hx
    obtain ⟨j, hj⟩ := htrans y hy
    refine ⟨j + 6 * i, ?_⟩
    rw [← hi, ← hj, ← MulAut.mul_apply, ← pow_add]
    have : j + 6 * i + i = j + 7 * i := by omega
    rw [this, pow_add, pow_mul, h7, one_pow, mul_one]

private theorem comm_of_sq_eq_one {G : Type*} [Group G] (h : ∀ x : G, x * x = 1) (x y : G) :
    x * y = y * x := by
  have hinv : ∀ z : G, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (h z)
  calc x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv x, hinv y]

theorem exponent_two_of_orbit {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (σ : MulAut E) (hσ : orderOf σ = 7) : ∀ x : E, x * x = 1 := by
  obtain ⟨-, htrans⟩ := orbit_of_prime_order hE σ hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [hE]; norm_num)
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    omega
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, pow_two] at this
  intro x
  by_cases hx : x = 1
  · simp [hx]
  · obtain ⟨i, hi⟩ := htrans a x ha1 hx
    rw [← hi, ← map_mul, haa, map_one]

theorem comm_of_orbit {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (σ : MulAut E) (hσ : orderOf σ = 7) : ∀ x y : E, x * y = y * x :=
  comm_of_sq_eq_one (exponent_two_of_orbit hE σ hσ)

private theorem exists_independent_triple {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 8) (h2 : ∀ x : Q, x * x = 1) :
    ∃ a b d : Q, a ≠ 1 ∧ b ≠ 1 ∧ d ≠ 1 ∧ a * b ≠ 1 ∧ a * d ≠ 1 ∧ b * d ≠ 1 ∧
      a * (b * d) ≠ 1 := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hcard : Fintype.card Q = 8 := by rw [← Nat.card_eq_fintype_card, hQ]
  have hcomm := comm_of_sq_eq_one h2
  have hinv : ∀ z : Q, z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (h2 z)
  have hfresh : ∀ s : Finset Q, s.card < 8 → ∃ x : Q, x ∉ s := by
    intro s hs
    by_contra h
    push Not at h
    have : s = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ, hcard] at hs
    omega
  obtain ⟨a, ha⟩ := hfresh {1} (by simp)
  obtain ⟨b, hb⟩ := hfresh {1, a} (lt_of_le_of_lt Finset.card_le_two (by norm_num))
  obtain ⟨d, hd⟩ := hfresh {1, a, b, a * b} (lt_of_le_of_lt Finset.card_le_four (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hd
  obtain ⟨hb1, hba⟩ := hb
  obtain ⟨hd1, hda, hdb, hdab⟩ := hd
  refine ⟨a, b, d, ha, hb1, hd1, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hba
    rw [eq_inv_of_mul_eq_one_right h, hinv]
  · intro h
    apply hda
    rw [eq_inv_of_mul_eq_one_right h, hinv]
  · intro h
    apply hdb
    rw [eq_inv_of_mul_eq_one_right h, hinv]
  · intro h
    apply hdab
    have h1 : b * d = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hinv] at h1
    calc d = b⁻¹ * (b * d) := by group
      _ = b * a := by rw [h1, hinv]
      _ = a * b := hcomm b a

private theorem quotient_data {U : Type*} [Group U] [Finite U] (hU : Nat.card U = 16)
    {c : U} (hc : orderOf c = 2) (hcc : ∀ u : U, u * c = c * u) (σ : MulAut U)
    (hσ : orderOf σ = 7) (hσc : σ c = c)
    (hfree : ∀ u : U, σ u * u⁻¹ ∈ zpowers c → u ∈ zpowers c) :
    (∀ u : U, u * u ∈ zpowers c) ∧ (∀ u v : U, u * v * (v * u)⁻¹ ∈ zpowers c) ∧
    (∀ u v : U, u ∉ zpowers c → v ∉ zpowers c → ∃ i : ℕ, ((σ ^ i) u)⁻¹ * v ∈ zpowers c) ∧
    ∃ u v w : U, u ∉ zpowers c ∧ v ∉ zpowers c ∧ w ∉ zpowers c ∧ u * v ∉ zpowers c ∧
      u * w ∉ zpowers c ∧ v * w ∉ zpowers c ∧ u * (v * w) ∉ zpowers c := by
  have hcenter : zpowers c ≤ Subgroup.center U :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hcc)
  have hN : (zpowers c).Normal := Subgroup.normal_of_le_center hcenter
  have h7 : σ ^ 7 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hQ : Nat.card (U ⧸ zpowers c) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers c)
    rw [Nat.card_zpowers, hc, hU] at h
    omega
  have hmap : (zpowers c).map (σ : U →* U) = zpowers c := by
    rw [MonoidHom.map_zpowers]
    exact congrArg _ hσc
  let σb : MulAut (U ⧸ zpowers c) := QuotientGroup.congr (zpowers c) (zpowers c) σ hmap
  have hσb_mk : ∀ u : U, σb (u : U ⧸ zpowers c) = ((σ u : U) : U ⧸ zpowers c) := fun u => rfl
  have hσb_pow : ∀ (n : ℕ) (u : U),
      (σb ^ n) (u : U ⧸ zpowers c) = (((σ ^ n) u : U) : U ⧸ zpowers c) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hσb_mk, ih]
  have hfixQ : ∀ q : U ⧸ zpowers c, σb q = q → q = 1 := by
    intro q hq
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hσb_mk] at hq
    have h1 := QuotientGroup.eq_iff_div_mem.mp hq
    rw [div_eq_mul_inv] at h1
    exact (QuotientGroup.eq_one_iff u).mpr (hfree u h1)
  have hσb7 : σb ^ 7 = 1 := by
    ext q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hσb_pow, h7]
    rfl
  have hσb1 : σb ≠ 1 := by
    intro h
    have : Nontrivial (U ⧸ zpowers c) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨q, hq⟩ := exists_ne (1 : U ⧸ zpowers c)
    exact hq (hfixQ q (by rw [h]; rfl))
  have hord : orderOf σb = 7 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    exact orderOf_eq_prime hσb7 hσb1
  obtain ⟨-, htransQ⟩ := orbit_of_prime_order hQ σb hord
  have hexpQ := exponent_two_of_orbit hQ σb hord
  have hcommQ := comm_of_orbit hQ σb hord
  have hmk1 : ∀ u : U, u ∉ zpowers c ↔ (u : U ⧸ zpowers c) ≠ 1 := fun u => by
    rw [Ne, QuotientGroup.eq_one_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    have h1 := hexpQ u
    rwa [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h1
  · intro u v
    have h1 := hcommQ u v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    have h2 := QuotientGroup.eq_iff_div_mem.mp h1
    rwa [div_eq_mul_inv] at h2
  · intro u v hu hv
    obtain ⟨i, hi⟩ := htransQ u v ((hmk1 u).mp hu) ((hmk1 v).mp hv)
    rw [hσb_pow] at hi
    exact ⟨i, QuotientGroup.eq.mp hi⟩
  · obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd, habd⟩ := exists_independent_triple hQ hexpQ
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective d
    refine ⟨u, v, w, (hmk1 u).mpr ha, (hmk1 v).mpr hb, (hmk1 w).mpr hd, ?_, ?_, ?_, ?_⟩
    · rw [hmk1, QuotientGroup.mk_mul]; exact hab
    · rw [hmk1, QuotientGroup.mk_mul]; exact had
    · rw [hmk1, QuotientGroup.mk_mul]; exact hbd
    · rw [hmk1, QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact habd

theorem abelian_of_central_extension {U : Type*} [Group U] [Finite U] (hU : Nat.card U = 16)
    {c : U} (hc : orderOf c = 2) (hcc : ∀ u : U, u * c = c * u) (σ : MulAut U)
    (hσ : orderOf σ = 7) (hσc : σ c = c)
    (hfree : ∀ u : U, σ u * u⁻¹ ∈ zpowers c → u ∈ zpowers c) :
    (∀ a b : U, a * b = b * a) ∧ ∀ a : U, a * a = 1 := by
  obtain ⟨hsq, hcom, htrans, u, v, w, hu, hv, hw, huv, huw, hvw, huvw⟩ :=
    quotient_data hU hc hcc σ hσ hσc hfree
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hc2 : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc, pow_two] at this
  have hZ : ∀ z ∈ zpowers c, z = 1 ∨ z = c := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_mod_orderOf, hc]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp [h]
    · right
      simp [h]
  have hσpow : ∀ i : ℕ, (σ ^ i) c = c := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, MulAut.mul_apply, hσc, ih]
  by_cases hex : ∃ x : U, x ∉ zpowers c ∧ x * x = c
  · exfalso
    obtain ⟨x₀, hx₀, hx₀c⟩ := hex
    have hall : ∀ y : U, y ∉ zpowers c → y * y = c := by
      intro y hy
      obtain ⟨i, hi⟩ := htrans x₀ y hx₀ hy
      have htt : (σ ^ i) x₀ * (σ ^ i) x₀ = c := by
        rw [← map_mul, hx₀c, hσpow]
      have hy' : y = (σ ^ i) x₀ * (((σ ^ i) x₀)⁻¹ * y) := by group
      rcases hZ _ hi with h | h
      · rw [hy', h, mul_one]
        exact htt
      · rw [hy', h]
        calc (σ ^ i) x₀ * c * ((σ ^ i) x₀ * c)
            = (σ ^ i) x₀ * (c * (σ ^ i) x₀) * c := by group
          _ = (σ ^ i) x₀ * ((σ ^ i) x₀ * c) * c := by rw [← hcc ((σ ^ i) x₀)]
          _ = (σ ^ i) x₀ * (σ ^ i) x₀ * (c * c) := by group
          _ = c := by rw [htt, hc2, mul_one]
    have hpair : ∀ x y : U, x ∉ zpowers c → y ∉ zpowers c → x * y ∉ zpowers c →
        x * y = y * x * c := by
      intro x y hx hy hxy
      have hxx := hall x hx
      have hyy := hall y hy
      have hxyxy := hall (x * y) hxy
      rcases hZ _ (hcom x y) with h | h
      · exfalso
        have hxy' : x * y = y * x := mul_inv_eq_one.mp h
        apply hc1
        calc c = x * y * (x * y) := hxyxy.symm
          _ = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [← hxy']
          _ = x * x * (y * y) := by group
          _ = c * c := by rw [hxx, hyy]
          _ = 1 := hc2
      · rw [mul_inv_eq_iff_eq_mul.mp h, ← hcc (y * x)]
    have e1 := hpair u v hu hv huv
    have e2 := hpair u w hu hw huw
    have e3 := hpair u (v * w) hu hvw huvw
    have hkey : v * w * u * c = v * w * u := by
      calc v * w * u * c = u * (v * w) := e3.symm
        _ = u * v * w := by group
        _ = v * u * c * w := by rw [e1]
        _ = v * u * (c * w) := by group
        _ = v * u * (w * c) := by rw [← hcc w]
        _ = v * (u * w) * c := by group
        _ = v * (w * u * c) * c := by rw [e2]
        _ = v * w * u * (c * c) := by group
        _ = v * w * u := by rw [hc2, mul_one]
    exact hc1 (mul_left_cancel (a := v * w * u) (by rw [hkey, mul_one]))
  · push Not at hex
    have hsq1 : ∀ x : U, x * x = 1 := by
      intro x
      by_cases hx : x ∈ zpowers c
      · rcases hZ x hx with h | h
        · rw [h, mul_one]
        · rw [h, hc2]
      · rcases hZ _ (hsq x) with h | h
        · exact h
        · exact absurd h (hex x hx)
    exact ⟨comm_of_sq_eq_one hsq1, hsq1⟩

private theorem mem_sq_of_sigma_fixed_comm {A : Type*} [CommGroup A] (σ : MulAut A)
    (hσ : σ ^ 7 = 1) (hfree : ∀ a : A, σ a = a → a = 1) {a : A}
    (ha : ∃ b : A, σ a * a⁻¹ = b * b) : ∃ c : A, a = c * c := by
  have hsq : ∀ n : ℕ, ∃ b : A, (σ ^ n) a * a⁻¹ = b * b := by
    intro n
    induction n with
    | zero => exact ⟨1, by simp⟩
    | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      obtain ⟨b', hb'⟩ := ha
      refine ⟨σ b * b', ?_⟩
      have h1 : (σ ^ (n + 1)) a * a⁻¹ = σ ((σ ^ n) a * a⁻¹) * (σ a * a⁻¹) := by
        rw [map_mul, map_inv, pow_succ', MulAut.mul_apply]
        group
      rw [h1, hb, hb', map_mul]
      ac_rfl
  have hnorm : ∀ k : ℕ, ∃ n s : A, σ n = a⁻¹ * (n * (σ ^ k) a) ∧ n = a ^ k * (s * s) := by
    intro k
    induction k with
    | zero => exact ⟨1, 1, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨n, s, h1, h2⟩ := ih
      obtain ⟨b, hb⟩ := hsq k
      refine ⟨n * (σ ^ k) a, s * b, ?_, ?_⟩
      · rw [map_mul, h1, pow_succ' σ k, MulAut.mul_apply]
        group
      · have hk : (σ ^ k) a = b * b * a := by
          rw [← hb]
          group
        rw [h2, hk, pow_succ]
        ac_rfl
  obtain ⟨n, s, h1, h2⟩ := hnorm 7
  have hn : σ n = n := by
    rw [h1, hσ, MulAut.one_apply, mul_comm n a, inv_mul_cancel_left]
  have hn1 : n = 1 := hfree n hn
  have h7 : a ^ 7 * (s * s) = 1 := by rw [← h2, hn1]
  refine ⟨(a ^ 3 * s)⁻¹, ?_⟩
  have h8 : a * (a ^ 3 * s * (a ^ 3 * s)) = 1 := by
    calc a * (a ^ 3 * s * (a ^ 3 * s)) = (a * a ^ 3 * a ^ 3) * (s * s) := by ac_rfl
      _ = a ^ 7 * (s * s) := by group
      _ = 1 := h7
  rw [← mul_inv_rev, eq_inv_of_mul_eq_one_right h8, inv_inv]

theorem mem_sq_of_sigma_fixed {A : Type*} [Group A] [Finite A] (hA : ∀ a b : A, a * b = b * a)
    (σ : MulAut A) (hσ : σ ^ 7 = 1) (hfree : ∀ a : A, σ a = a → a = 1) {a : A}
    (ha : ∃ b : A, σ a * a⁻¹ = b * b) : ∃ c : A, a = c * c := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hA }
  exact mem_sq_of_sigma_fixed_comm σ hσ hfree ha

end CFSG.EvenSporadicStandard.J1Std
