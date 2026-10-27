module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped commutatorElement Pointwise

theorem zjr_card_modEq {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    {M : Subgroup Y} {a : Y} (hap : a ^ p = 1) (haM : a ∈ normalizer (M : Set Y)) :
    Nat.card M ≡ Nat.card (M ⊓ centralizer ({a} : Set Y) : Subgroup Y) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype M := Fintype.ofFinite M
  let f : Function.End M := fun m => ⟨a * m * a⁻¹, (mem_normalizer_iff.1 haM m).1 m.2⟩
  have hfk : ∀ k : ℕ, ∀ m : M, ((f ^ k : Function.End M) m : Y) = a ^ k * m * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro m; simp; rfl
    | succ k ih =>
      intro m
      rw [pow_succ]
      change ((f ^ k : Function.End M) (f m) : Y) = _
      rw [ih]
      simp only [f]
      rw [pow_succ]; group
  have hf : f ^ p ^ 1 = 1 := by
    funext m
    apply Subtype.ext
    rw [pow_one, hfk]
    simp [hap]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hf
  have hfix : ∀ m : M, f m = m ↔ (m : Y) ∈ centralizer ({a} : Set Y) := by
    intro m
    rw [mem_centralizer_iff]
    constructor
    · intro h h' hh'
      rw [Set.mem_singleton_iff.1 hh']
      have h := congrArg Subtype.val h
      change a * (m : Y) * a⁻¹ = m at h
      calc a * m = (a * m * a⁻¹) * a := by group
        _ = m * a := by rw [h]
    · intro h
      have hy := h a rfl
      apply Subtype.ext
      change a * (m : Y) * a⁻¹ = m
      calc a * (m : Y) * a⁻¹ = ((m : Y) * a) * a⁻¹ := by rw [hy]
        _ = m := by group
  have e : Nat.card (Function.fixedPoints f) =
      Nat.card (M ⊓ centralizer ({a} : Set Y) : Subgroup Y) := by
    refine Nat.card_congr
      { toFun := fun m => ⟨(m.1 : Y), mem_inf.2 ⟨m.1.2, (hfix m.1).1 m.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).1⟩, (hfix _).2 (mem_inf.1 y.2).2⟩
        left_inv := fun m => rfl
        right_inv := fun y => rfl }
  rw [Nat.card_eq_fintype_card, ← e, Nat.card_eq_fintype_card (α := Function.fixedPoints f)]
  exact hmod

theorem zjr_three_mul_card_le {Y : Type*} [Group Y] [Finite Y] {H K : Subgroup Y}
    (hK : IsPGroup 3 K) (hHK : H < K) : 3 * Nat.card H ≤ Nat.card K := by
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK.le
  have hne : m ≠ 1 := by
    rintro rfl
    exact hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le (by rw [hm, mul_one]))
  have hmdvd : m ∣ 3 ^ n := ⟨Nat.card H, by rw [← hn, hm, mul_comm]⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hmdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hj)
  have h3 : 3 ≤ m := by
    rw [hj]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hj0)
  rw [hm]
  calc 3 * Nat.card H ≤ m * Nat.card H := Nat.mul_le_mul_right _ h3
    _ = Nat.card H * m := mul_comm _ _

theorem zjr_card_fixed_mul_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*} [Group Y]
    [Finite Y] {M : Subgroup Y} (hM : IsPGroup 3 M) {a : Y} (hap : a ^ p = 1)
    (haM : a ∈ normalizer (M : Set Y)) (hnc : ¬ M ≤ centralizer ({a} : Set Y)) :
    27 * Nat.card (M ⊓ centralizer ({a} : Set Y) : Subgroup Y) ≤ Nat.card M := by
  set C : Subgroup Y := M ⊓ centralizer ({a} : Set Y) with hC
  have hCM : C < M := lt_of_le_of_ne inf_le_left (fun h => hnc (h ▸ inf_le_right))
  have hmod := zjr_card_modEq hp hap haM
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hCp : IsPGroup 3 C := hM.to_le hCM.le
  obtain ⟨k, hk⟩ := hCp.exists_card_eq
  have hlt : Nat.card C < Nat.card M := by
    refine lt_of_le_of_ne (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hCM.le))
      fun h => hCM.ne (Subgroup.eq_of_le_of_card_ge hCM.le h.ge)
  rw [hn, hk] at hmod hlt
  have hkn : k < n := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  have hj0 : 0 < j := by omega
  have hcop : Nat.gcd p (3 ^ k) = 1 :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
  have hmod' : 3 ^ k * 3 ^ j ≡ 3 ^ k * 1 [MOD p] := by
    rw [← pow_add, mul_one]; exact hmod
  have hmod'' := Nat.ModEq.cancel_left_of_coprime hcop hmod'
  have hj3 : 3 ≤ j := by
    by_contra hj
    have hj12 : j = 1 ∨ j = 2 := by omega
    rcases hj12 with rfl | rfl
    · have : p ∣ 2 := by
        have := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod''.symm
        simpa using this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    · have : p ∣ 8 := by
        have := (Nat.modEq_iff_dvd' (by norm_num)).1 hmod''.symm
        simpa using this
      have := Nat.le_of_dvd (by norm_num) this
      interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rw [hn, hk]
  calc 27 * 3 ^ k = 3 ^ 3 * 3 ^ k := by norm_num
    _ ≤ 3 ^ j * 3 ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hj3)
    _ = 3 ^ (k + j) := by rw [← pow_add, add_comm]

theorem zjr_three_pow_four_le_card {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type*} [Group Y]
    [Finite Y] {D M : Subgroup Y} (hDp : ∀ d ∈ D, d ^ p = 1) (hDc : Nat.card D = p ^ 2)
    (hM : IsPGroup 3 M) (hDM : D ≤ normalizer (M : Set Y))
    (hfaith : D ⊓ centralizer (M : Set Y) = ⊥) : 3 ^ 4 ≤ Nat.card M := by
  by_contra hlt
  replace hlt := not_le.1 hlt
  obtain ⟨n, hn⟩ := hM.exists_card_eq
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨⟨a, haD⟩, ha1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have ha1 : a ≠ 1 := fun h => ha1' (Subtype.ext h)
  have hnc : ∀ d ∈ D, d ≠ 1 → ¬ M ≤ centralizer ({d} : Set Y) := by
    intro d hd hd1 hle
    apply hd1
    have hdc : d ∈ centralizer (M : Set Y) := by
      rw [mem_centralizer_iff]
      intro m hm
      exact (mem_centralizer_iff.1 (hle hm) d rfl).symm
    have : d ∈ D ⊓ centralizer (M : Set Y) := ⟨hd, hdc⟩
    rw [hfaith, Subgroup.mem_bot] at this
    exact_mod_cast this
  have hbot : ∀ d ∈ D, d ≠ 1 → M ⊓ centralizer ({d} : Set Y) = ⊥ := by
    intro d hd hd1
    have h27 := zjr_card_fixed_mul_le hp hp5 hM (hDp d hd) (hDM hd) (hnc d hd hd1)
    set C : Subgroup Y := M ⊓ centralizer ({d} : Set Y) with hC
    have hCp : IsPGroup 3 C := hM.to_le inf_le_left
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    rw [hk, hn] at h27
    rw [hn] at hlt
    have hk0 : k = 0 := by
      by_contra hk0
      have : 3 ≤ 3 ^ k := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hk0)
      have : 81 ≤ 3 ^ n := by nlinarith
      omega
    rw [hk0, pow_zero] at hk
    exact (Subgroup.card_eq_one).1 hk
  have hCa := hbot a haD ha1
  have h27 := zjr_card_fixed_mul_le hp hp5 hM (hDp a haD) (hDM haD) (hnc a haD ha1)
  rw [hCa, Subgroup.card_bot] at h27
  have hmod := zjr_card_modEq hp (hDp a haD) (hDM haD)
  rw [hCa, Subgroup.card_bot] at hmod
  have hMn : Nat.card M = 27 := by
    rw [hn] at h27 hlt ⊢
    have h3 : 3 ≤ n := by
      by_contra h
      have : 3 ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3' : n ≤ 3 := by
      by_contra h
      have : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : n = 3 := by omega
    subst this; norm_num
  obtain ⟨m₀, hm₀M, hm₀1⟩ : ∃ m ∈ M, m ≠ 1 := by
    by_contra h
    have : M = ⊥ := (Subgroup.eq_bot_iff_forall M).2 fun x hx => by
      by_contra hx1
      exact h ⟨x, hx, hx1⟩
    rw [this, Subgroup.card_bot] at hMn
    omega
  have hinj : Function.Injective (fun d : D =>
      (⟨(d : Y) * m₀ * (d : Y)⁻¹, (mem_normalizer_iff.1 (hDM d.2) m₀).1 hm₀M⟩ : M)) := by
    intro d d' hdd
    have h := congrArg Subtype.val hdd
    change (d : Y) * m₀ * (d : Y)⁻¹ = (d' : Y) * m₀ * (d' : Y)⁻¹ at h
    by_contra hne
    have hg1 : (d' : Y)⁻¹ * d ≠ 1 := by
      intro h1
      apply hne
      have : (d : Y) = d' := by
        calc (d : Y) = d' * ((d' : Y)⁻¹ * d) := by group
          _ = d' := by rw [h1, mul_one]
      exact Subtype.ext this
    have hgD : (d' : Y)⁻¹ * d ∈ D := mul_mem (inv_mem d'.2) d.2
    have hcomm : (d' : Y)⁻¹ * d * m₀ = m₀ * ((d' : Y)⁻¹ * d) := by
      have h2 : (d : Y) * m₀ = (d' : Y) * m₀ * (d' : Y)⁻¹ * d := by
        calc (d : Y) * m₀ = ((d : Y) * m₀ * (d : Y)⁻¹) * d := by group
          _ = _ := by rw [h]
      calc (d' : Y)⁻¹ * d * m₀ = (d' : Y)⁻¹ * ((d : Y) * m₀) := by group
        _ = (d' : Y)⁻¹ * ((d' : Y) * m₀ * (d' : Y)⁻¹ * d) := by rw [h2]
        _ = m₀ * ((d' : Y)⁻¹ * d) := by group
    have hmem : m₀ ∈ M ⊓ centralizer ({(d' : Y)⁻¹ * d} : Set Y) := by
      refine mem_inf.2 ⟨hm₀M, ?_⟩
      rw [mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff.1 hh']
      exact hcomm
    rw [hbot _ hgD hg1, Subgroup.mem_bot] at hmem
    exact hm₀1 hmem
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [hDc, hMn] at hcard
  have hp5' : p = 5 := by
    by_contra hne
    have : 6 ≤ p := by omega
    nlinarith
  subst hp5'
  rw [hMn] at hmod
  have : (27 : ℕ) ≡ 1 [MOD 5] := hmod
  revert this
  decide

theorem zjr_card_sup_le {Y : Type*} [Group Y] [Finite Y] {Z : Subgroup Y} {x : Y}
    (hx3 : x ^ 3 = 1) (hxZ : ∀ z ∈ Z, z * x = x * z) :
    Nat.card (Z ⊔ zpowers x : Subgroup Y) ≤ 3 * Nat.card Z := by
  have key : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    calc x * z * x⁻¹ = (x * z) * x⁻¹ := rfl
      _ = (z * x) * x⁻¹ := by rw [hxZ z hz]
      _ = z := by group
  have hnorm : zpowers x ≤ normalizer (Z : Set Y) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [key h hh]
      exact hh
    · intro hh
      have e : x * h * x⁻¹ = h := by
        have h1 := key _ hh
        calc x * h * x⁻¹ = x⁻¹ * (x * (x * h * x⁻¹) * x⁻¹) * x := by group
          _ = x⁻¹ * (x * h * x⁻¹) * x := by rw [h1]
          _ = h := by group
      rw [← e]
      exact hh
  have hset := coe_mul_of_left_le_normalizer_right (zpowers x) Z hnorm
  rw [sup_comm] at hset
  have hsurj : Function.Surjective (fun q : zpowers x × Z =>
      (⟨(q.1 : Y) * q.2, Set.mul_mem_mul q.1.2 q.2.2⟩ : ((zpowers x : Set Y) * (Z : Set Y)))) := by
    rintro ⟨_, a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have h1 : Nat.card (Z ⊔ zpowers x : Subgroup Y) =
      Nat.card ((zpowers x : Set Y) * (Z : Set Y)) := by
    rw [← hset]
    rfl
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_zpowers] at h2
  have h3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  calc Nat.card (Z ⊔ zpowers x : Subgroup Y) ≤ orderOf x * Nat.card Z := h1 ▸ h2
    _ ≤ 3 * Nat.card Z := Nat.mul_le_mul_right _ h3


theorem zjr_card_le_centralizer_mul {B : Type*} [Group B] [Finite B] {Z : Subgroup B}
    (hcomm : ∀ b b' : B, ⁅b, b'⁆ ∈ Z) (x : B) :
    Nat.card B ≤ Nat.card (centralizer ({x} : Set B)) * Nat.card Z := by
  have h1 := index_centralizer_eq_ncard x
  have h2 : conjugatesOf x ⊆ (fun z => z * x) '' (Z : Set B) := by
    intro c hc
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc
    exact ⟨⁅g, x⁆, hcomm g x, by simp [commutatorElement_def]⟩
  have h3 : (conjugatesOf x).ncard ≤ Nat.card Z :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_image_le (Set.toFinite _)).trans_eq (Nat.card_coe_set_eq _).symm)
  have h4 := card_mul_index (centralizer ({x} : Set B))
  rw [← h4, h1]
  exact Nat.mul_le_mul_left _ h3


theorem zjr_comm_sup {B : Type*} [Group B] {H K : Subgroup B}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hHK : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) : ∀ a ∈ H ⊔ K, ∀ b ∈ H ⊔ K, a * b = b * a := by
  have hsup : H ⊔ K = closure ((H : Set B) ∪ (K : Set B)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have : IsMulCommutative ↥(closure ((H : Set B) ∪ (K : Set B))) := by
    refine isMulCommutative_closure ?_
    intro a ha b hb _
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hH a ha b hb
    · exact hHK a ha b hb
    · exact (hHK b hb a ha).symm
    · exact hK a ha b hb
  intro a ha b hb
  rw [hsup] at ha hb
  exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
    (⟨a, ha⟩ : ↥(closure ((H : Set B) ∪ (K : Set B)))) ⟨b, hb⟩)

theorem zjr_comm_zpowers {B : Type*} [Group B] (x : B) :
    ∀ a ∈ zpowers x, ∀ b ∈ zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
  exact (Commute.zpow_zpow_self x m n).eq

theorem zjr_exists_abelian {B : Type*} [Group B] [Finite B] {Z : Subgroup B}
    (hexp : ∀ b : B, b ^ 3 = 1) (hZc : ∀ z ∈ Z, ∀ b : B, z * b = b * z)
    (hcomm : ∀ b b' : B, ⁅b, b'⁆ ∈ Z) (hZ3 : 3 ≤ Nat.card Z)
    (hB : 27 * Nat.card Z ≤ Nat.card B) :
    ∃ M : Subgroup B, Z ≤ M ∧ (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ 27 ≤ Nat.card M := by
  have hP : IsPGroup 3 B := fun b => ⟨1, by simpa using hexp b⟩
  have hZp : IsPGroup 3 Z := hP.to_subgroup Z
  obtain ⟨x, hxZ⟩ : ∃ x : B, x ∉ Z := by
    by_contra h
    have hZtop : Z = ⊤ := eq_top_iff.2 fun x _ => by
      by_contra hx
      exact h ⟨x, hx⟩
    rw [hZtop, card_top] at hB
    have := Nat.card_pos (α := B)
    omega
  have hxZ' : ∀ z ∈ Z, z * x = x * z := fun z hz => hZc z hz x
  have hM₀comm : ∀ a ∈ Z ⊔ zpowers x, ∀ b ∈ Z ⊔ zpowers x, a * b = b * a :=
    zjr_comm_sup (fun a ha b _ => hZc a ha b) (zjr_comm_zpowers x)
      (fun a ha b _ => hZc a ha b)
  have hZM₀ : Z < Z ⊔ zpowers x :=
    lt_of_le_of_ne le_sup_left fun h => hxZ (h ▸ mem_sup_right (mem_zpowers x))
  have hM₀card : 3 * Nat.card Z ≤ Nat.card (Z ⊔ zpowers x : Subgroup B) :=
    zjr_three_mul_card_le (hP.to_subgroup _) hZM₀
  by_cases h9 : 9 ≤ Nat.card Z
  · exact ⟨Z ⊔ zpowers x, le_sup_left, hM₀comm, by omega⟩
  · have hZ3' : Nat.card Z = 3 := by
      obtain ⟨k, hk⟩ := hZp.exists_card_eq
      rw [hk] at hZ3 h9 ⊢
      have h1 : 1 ≤ k := by
        by_contra h
        have : k = 0 := by omega
        subst this
        norm_num at hZ3
      have h2 : k ≤ 1 := by
        by_contra h
        have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : k = 1 := by omega
      subst this
      norm_num
    have hCcard := zjr_card_le_centralizer_mul hcomm x
    rw [hZ3'] at hCcard hB
    have hC27 : 27 ≤ Nat.card (centralizer ({x} : Set B)) := by omega
    have hM₀le : Nat.card (Z ⊔ zpowers x : Subgroup B) ≤ 9 := by
      have := zjr_card_sup_le (hexp x) hxZ'
      omega
    obtain ⟨y, hyC, hyM₀⟩ : ∃ y ∈ centralizer ({x} : Set B), y ∉ Z ⊔ zpowers x := by
      by_contra h
      have hle : centralizer ({x} : Set B) ≤ Z ⊔ zpowers x := fun y hy => by
        by_contra hy'
        exact h ⟨y, hy, hy'⟩
      have := Subgroup.card_le_of_le hle
      omega
    have hyx : x * y = y * x := (mem_centralizer_iff.1 hyC x rfl)
    have hM₀y : Z ⊔ zpowers x ≤ centralizer ({y} : Set B) := by
      refine sup_le (fun z hz => ?_) ?_
      · rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hZc z hz y).symm
      · rw [zpowers_le, mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hyx.symm
    have hMcomm : ∀ a ∈ (Z ⊔ zpowers x) ⊔ zpowers y, ∀ b ∈ (Z ⊔ zpowers x) ⊔ zpowers y,
        a * b = b * a := by
      refine zjr_comm_sup hM₀comm (zjr_comm_zpowers y) ?_
      intro a ha b hb
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
      have hay : y * a = a * y := mem_centralizer_iff.1 (hM₀y ha) y rfl
      exact ((Commute.zpow_right (show Commute a y from hay.symm) n)).eq
    have hM₀M : (Z ⊔ zpowers x) < (Z ⊔ zpowers x) ⊔ zpowers y :=
      lt_of_le_of_ne le_sup_left fun h => hyM₀ (h ▸ mem_sup_right (mem_zpowers y))
    have hMcard := zjr_three_mul_card_le (hP.to_subgroup _) hM₀M
    exact ⟨(Z ⊔ zpowers x) ⊔ zpowers y, le_sup_left.trans le_sup_left, hMcomm, by omega⟩


theorem zjr_exists_abelian_ambient {Y : Type*} [Group Y] [Finite Y] {U Z : Subgroup Y}
    (hZU : Z ≤ U) (hexp : ∀ b ∈ U, b ^ 3 = 1) (hZc : ∀ z ∈ Z, ∀ b ∈ U, z * b = b * z)
    (hcomm : ∀ b ∈ U, ∀ b' ∈ U, ⁅b, b'⁆ ∈ Z) (hZ3 : 3 ≤ Nat.card Z)
    (hU : 27 * Nat.card Z ≤ Nat.card U) :
    ∃ M : Subgroup Y, M ≤ U ∧ Z ≤ M ∧ (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧
      27 ≤ Nat.card M := by
  have hmap : (Z.subgroupOf U).map U.subtype = Z := by
    rw [subgroupOf_map_subtype, inf_of_le_left hZU]
  have hcard : Nat.card (Z.subgroupOf U) = Nat.card Z := by
    calc Nat.card (Z.subgroupOf U) = Nat.card ((Z.subgroupOf U).map U.subtype) :=
          (card_map_of_injective U.subtype_injective).symm
      _ = Nat.card Z := by rw [hmap]
  obtain ⟨M', hZM', hcomm', hcardM'⟩ := zjr_exists_abelian (B := U) (Z := Z.subgroupOf U)
    (fun b => Subtype.ext (hexp b b.2)) (fun z hz b => Subtype.ext (hZc z hz b b.2))
    (fun b b' => (mem_subgroupOf).2 (hcomm b b.2 b' b'.2)) (hcard ▸ hZ3) (by rw [hcard]; exact hU)
  refine ⟨M'.map U.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [← hmap]
    exact map_mono hZM'
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm' a ha b hb)
  · rw [card_map_of_injective U.subtype_injective]
    exact hcardM'

end CFSG.LocalAnalysis.RankThreeTheoremC
