module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

variable {Γ : Type} [Group Γ]

theorem card_modEq_cent {W : Subgroup Γ} [Finite W] {a : Γ} (ha : a ^ 5 = 1)
    (hW : ∀ w ∈ W, a * w * a⁻¹ ∈ W) :
    Nat.card ↥W ≡ Nat.card {w : ↥W // a * (w : Γ) * a⁻¹ = w} [MOD 5] := by
  classical
  haveI : Fintype ↥W := Fintype.ofFinite ↥W
  let φ : Function.End ↥W := fun w => ⟨a * (w : Γ) * a⁻¹, hW w w.2⟩
  have hiter : ∀ k (w : ↥W), ((φ^[k]) w : Γ) = a ^ k * (w : Γ) * (a ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro w; rw [Function.iterate_zero]; simp
    | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply']
        change a * (((φ^[k]) w : ↥W) : Γ) * a⁻¹ = a ^ (k + 1) * (w : Γ) * (a ^ (k + 1))⁻¹
        rw [ih w, pow_succ']
        group
  have hφ5 : φ ^ 5 = 1 := by
    funext w
    apply Subtype.ext
    change ((φ^[5]) w : Γ) = (w : Γ)
    rw [hiter 5 w, ha]
    group
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥W) (f := φ) (p := 5) (n := 1) hφ5
  have hmod' : Nat.card ↥W ≡ Nat.card (Function.fixedPoints φ) [MOD 5] := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact hmod
  have he : {w : ↥W // a * (w : Γ) * a⁻¹ = w} ≃ (Function.fixedPoints φ : Type) :=
    { toFun := fun w => ⟨w.1, by
        change φ w.1 = w.1
        exact Subtype.ext w.2⟩
      invFun := fun w => ⟨w.1, by
        have h : φ w.1 = w.1 := w.2
        exact congrArg Subtype.val h⟩
      left_inv := fun w => rfl
      right_inv := fun w => rfl }
  rw [Nat.card_congr he]
  exact hmod'

theorem cent_of_card {W : Subgroup Γ} [Finite W] {a : Γ} (ha : a ^ 5 = 1)
    (hW : ∀ w ∈ W, a * w * a⁻¹ ∈ W)
    (hcard : Nat.card ↥W = 1 ∨ Nat.card ↥W = 3 ∨ Nat.card ↥W = 9 ∨ Nat.card ↥W = 27 ∨
      Nat.card ↥W = 5 ∨ Nat.card ↥W = 17) :
    ∀ w ∈ W, a * w = w * a := by
  classical
  let C : Subgroup ↥W :=
    { carrier := {w | a * (w : Γ) * a⁻¹ = w}
      one_mem' := by
        change a * ((1 : ↥W) : Γ) * a⁻¹ = ((1 : ↥W) : Γ)
        simp
      mul_mem' := by
        intro x y hx hy
        change a * ((x : Γ) * (y : Γ)) * a⁻¹ = (x : Γ) * (y : Γ)
        calc a * ((x : Γ) * (y : Γ)) * a⁻¹
            = (a * (x : Γ) * a⁻¹) * (a * (y : Γ) * a⁻¹) := by group
          _ = (x : Γ) * (y : Γ) := by rw [hx, hy]
      inv_mem' := by
        intro x hx
        change a * ((x : Γ))⁻¹ * a⁻¹ = ((x : Γ))⁻¹
        calc a * ((x : Γ))⁻¹ * a⁻¹ = (a * (x : Γ) * a⁻¹)⁻¹ := by group
          _ = ((x : Γ))⁻¹ := by rw [hx] }
  haveI : Finite ↥C := Subtype.finite
  have hmod := card_modEq_cent ha hW
  have hC : Nat.card ↥C ≡ Nat.card {w : ↥W // a * (w : Γ) * a⁻¹ = w} [MOD 5] := by
    rw [show Nat.card ↥C = Nat.card {w : ↥W // a * (w : Γ) * a⁻¹ = w} from rfl]
  have hmodC : Nat.card ↥W ≡ Nat.card ↥C [MOD 5] := hmod.trans hC.symm
  have hdvd := Subgroup.card_subgroup_dvd_card C
  have hle : Nat.card ↥C ≤ Nat.card ↥W := Nat.le_of_dvd Nat.card_pos hdvd
  have hCc : Nat.card ↥C = Nat.card ↥W := by
    rcases hcard with h | h | h | h | h | h
    · rw [h] at hdvd hmodC ⊢
      exact Nat.dvd_one.mp hdvd
    · rw [h] at hdvd hmodC ⊢
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hd | hd
      · rw [hd] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · exact hd
    · rw [h] at hdvd hmodC ⊢
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hdvd
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num)).mp hdvd
      interval_cases j
      · rw [hj] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · rw [hj] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · exact hj
    · rw [h] at hdvd hmodC ⊢
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at hdvd
      obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num)).mp hdvd
      interval_cases j
      · rw [hj] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · rw [hj] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · rw [hj] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · exact hj
    · rw [h] at hdvd hmodC ⊢
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with hd | hd
      · rw [hd] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · exact hd
    · rw [h] at hdvd hmodC ⊢
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hdvd with hd | hd
      · rw [hd] at hmodC
        norm_num [Nat.ModEq] at hmodC
      · exact hd
  have htop : C = ⊤ := Subgroup.eq_top_of_card_eq (H := C) hCc
  intro w hw
  let w' : ↥W := ⟨w, hw⟩
  have hmem : w' ∈ C := by rw [htop]; exact Subgroup.mem_top w'
  have h : a * w * a⁻¹ = w := hmem
  calc a * w = (a * w * a⁻¹) * a := by group
    _ = w * a := by rw [h]

private def torsion (P : Subgroup Γ) (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) (n : ℕ) :
    Subgroup Γ where
  carrier := {w | w ∈ P ∧ w ^ n = 1}
  one_mem' := ⟨P.one_mem, one_pow n⟩
  mul_mem' := by
    rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
    exact ⟨P.mul_mem hxP hyP, by
      have hxy : Commute x y := hcomm x hxP y hyP
      rw [hxy.mul_pow, hx, hy, one_mul]⟩
  inv_mem' := by
    rintro x ⟨hxP, hx⟩
    exact ⟨P.inv_mem hxP, by rw [inv_pow, hx, inv_one]⟩

private lemma torsion_le (P : Subgroup Γ) (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) (n : ℕ) :
    torsion P hcomm n ≤ P := fun _ h => h.1

private lemma card_dvd_card_of_le {H K : Subgroup Γ} (h : H ≤ K) :
    Nat.card ↥H ∣ Nat.card ↥K := by
  have e := (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rw [← Nat.card_congr e]
  exact Subgroup.card_subgroup_dvd_card _

private lemma prime_dvd_card_torsion {P : Subgroup Γ} [Finite P]
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {n q k r : ℕ}
    (hq : Nat.Prime q) (hn : n = q ^ k) (hr : Nat.Prime r)
    (hrdvd : r ∣ Nat.card ↥(torsion P hcomm n)) : r = q := by
  haveI : Finite ↥(torsion P hcomm n) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (torsion_le P hcomm n)).toEquiv
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(torsion P hcomm n)) r hrdvd
  have hxpow : (x : Γ) ^ n = 1 := x.2.2
  have hrdvdn : r ∣ n := by
    have hord : orderOf (x : Γ) = r := by rw [Subgroup.orderOf_coe, hxord]
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hxpow
  rw [hn] at hrdvdn
  exact (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrdvdn)

private lemma card_torsion_dvd_prime_pow {P : Subgroup Γ} [Finite P]
    (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {n q k : ℕ} (hq : Nat.Prime q)
    (hn : n = q ^ k) (hd : Nat.card ↥(torsion P hcomm n) ∣ 2295)
    (hnot : ¬ q ^ (k + 1) ∣ 2295) :
    Nat.card ↥(torsion P hcomm n) ∣ q ^ k := by
  haveI : Finite ↥(torsion P hcomm n) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (torsion_le P hcomm n)).toEquiv
  have hpos : Nat.card ↥(torsion P hcomm n) ≠ 0 := Nat.card_pos.ne'
  have huniq : ∀ {r : ℕ}, Nat.Prime r → r ∣ Nat.card ↥(torsion P hcomm n) → r = q :=
    fun {r} hr hrd => prime_dvd_card_torsion hcomm hq hn hr hrd
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hpos huniq
  set j := (Nat.card ↥(torsion P hcomm n)).primeFactorsList.length with hj
  have hdj : q ^ j ∣ 2295 := hpow ▸ hd
  have hjk : j ≤ k := by
    by_contra h
    have hkj : k + 1 ≤ j := by omega
    exact hnot (dvd_trans (pow_dvd_pow q hkj) hdj)
  rw [hpow]
  exact pow_dvd_pow q hjk

theorem cent_of_dvd {P : Subgroup Γ} [Finite P] {a : Γ} (ha : a ^ 5 = 1)
    (hP : ∀ p ∈ P, a * p * a⁻¹ ∈ P) (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hd : Nat.card ↥P ∣ 2295) : ∀ p ∈ P, a * p = p * a := by
  haveI : Finite ↥(torsion P hcomm 27) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (torsion_le P hcomm 27)).toEquiv
  haveI : Finite ↥(torsion P hcomm 5) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (torsion_le P hcomm 5)).toEquiv
  haveI : Finite ↥(torsion P hcomm 17) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe (torsion_le P hcomm 17)).toEquiv
  have hnorm : ∀ n : ℕ, ∀ w ∈ torsion P hcomm n, a * w * a⁻¹ ∈ torsion P hcomm n := by
    intro n w hw
    exact ⟨hP w hw.1, by
      rw [conj_pow, hw.2]
      group⟩
  have hd27 : Nat.card ↥(torsion P hcomm 27) ∣ 3 ^ 3 :=
    card_torsion_dvd_prime_pow hcomm (by norm_num) (by norm_num)
      (dvd_trans (card_dvd_card_of_le (torsion_le P hcomm 27)) hd) (by norm_num)
  have hd5 : Nat.card ↥(torsion P hcomm 5) ∣ 5 ^ 1 :=
    card_torsion_dvd_prime_pow hcomm (by norm_num) (by norm_num)
      (dvd_trans (card_dvd_card_of_le (torsion_le P hcomm 5)) hd) (by norm_num)
  have hd17 : Nat.card ↥(torsion P hcomm 17) ∣ 17 ^ 1 :=
    card_torsion_dvd_prime_pow hcomm (by norm_num) (by norm_num)
      (dvd_trans (card_dvd_card_of_le (torsion_le P hcomm 17)) hd) (by norm_num)
  have hcard27 : Nat.card ↥(torsion P hcomm 27) = 1 ∨
      Nat.card ↥(torsion P hcomm 27) = 3 ∨ Nat.card ↥(torsion P hcomm 27) = 9 ∨
      Nat.card ↥(torsion P hcomm 27) = 27 ∨ Nat.card ↥(torsion P hcomm 27) = 5 ∨
      Nat.card ↥(torsion P hcomm 27) = 17 := by
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num)).mp hd27
    interval_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (Or.inl (by simpa using hj))
    · exact Or.inr (Or.inr (Or.inl (by simpa using hj)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hj))))
  have hcard5 : Nat.card ↥(torsion P hcomm 5) = 1 ∨
      Nat.card ↥(torsion P hcomm 5) = 3 ∨ Nat.card ↥(torsion P hcomm 5) = 9 ∨
      Nat.card ↥(torsion P hcomm 5) = 27 ∨ Nat.card ↥(torsion P hcomm 5) = 5 ∨
      Nat.card ↥(torsion P hcomm 5) = 17 := by
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 5) Nat.prime_five).mp hd5
    interval_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hj)))))
  have hcard17 : Nat.card ↥(torsion P hcomm 17) = 1 ∨
      Nat.card ↥(torsion P hcomm 17) = 3 ∨ Nat.card ↥(torsion P hcomm 17) = 9 ∨
      Nat.card ↥(torsion P hcomm 17) = 27 ∨ Nat.card ↥(torsion P hcomm 17) = 5 ∨
      Nat.card ↥(torsion P hcomm 17) = 17 := by
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow (p := 17) (by norm_num : Nat.Prime 17)).mp hd17
    interval_cases j
    · exact Or.inl (by simpa using hj)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hj)))))
  have hc27 := cent_of_card ha (hnorm 27) hcard27
  have hc5 := cent_of_card ha (hnorm 5) hcard5
  have hc17 := cent_of_card ha (hnorm 17) hcard17
  intro x hxP
  have hxcard : x ^ Nat.card ↥P = 1 := by
    have h1 := congrArg (fun y : ↥P => (y : Γ))
      (pow_card_eq_one' (x := (⟨x, hxP⟩ : ↥P)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
  obtain ⟨k, hk⟩ := hd
  have hx2295 : x ^ 2295 = 1 := by rw [hk, pow_mul, hxcard, one_pow]
  have h595 : Commute a (x ^ 595) := hc27 _ ⟨P.pow_mem hxP 595, by
    rw [← pow_mul, show 595 * 27 = 2295 * 7 by norm_num, pow_mul, hx2295, one_pow]⟩
  have h1836 : Commute a (x ^ 1836) := hc5 _ ⟨P.pow_mem hxP 1836, by
    rw [← pow_mul, show 1836 * 5 = 2295 * 4 by norm_num, pow_mul, hx2295, one_pow]⟩
  have h2160 : Commute a (x ^ 2160) := hc17 _ ⟨P.pow_mem hxP 2160, by
    rw [← pow_mul, show 2160 * 17 = 2295 * 16 by norm_num, pow_mul, hx2295, one_pow]⟩
  have hxeq : x = x ^ 595 * x ^ 1836 * x ^ 2160 := by
    rw [← pow_add, ← pow_add]
    rw [show 595 + 1836 + 2160 = 2295 * 2 + 1 by norm_num, pow_add, pow_mul, hx2295]
    simp
  rw [hxeq]
  exact ((h595.mul_right h1836).mul_right h2160)

theorem A_comm_P {A P : Subgroup Γ} (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6))) [Finite P]
    (hn : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ ∈ P) (hcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hd : Nat.card ↥P ∣ 2295) : ∀ a ∈ A, ∀ p ∈ P, a * p = p * a := by
  obtain ⟨e⟩ := hA
  haveI : Finite ↥A := Finite.of_equiv (alternatingGroup (Fin 6)) e.symm.toEquiv
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥A := e.isSimpleGroup
  have hcardA : Nat.card ↥A = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5dvd : 5 ∣ Nat.card ↥A := by rw [hcardA]; norm_num
  obtain ⟨a5, ha5ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 5 h5dvd
  have ha5powA : a5 ^ 5 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [ha5ord])
  have ha5pow : (a5 : Γ) ^ 5 = 1 := by
    have := congrArg Subtype.val ha5powA
    simpa using this
  have ha5ne : a5 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha5ord
    norm_num at ha5ord
  have ha5comm : ∀ p ∈ P, (a5 : Γ) * p = p * (a5 : Γ) :=
    cent_of_dvd ha5pow (fun p hp => hn a5 a5.2 p hp) hcomm hd
  let Cp : Subgroup Γ :=
    { carrier := {g | ∀ p ∈ P, g * p = p * g}
      one_mem' := by intro p _; rw [one_mul, mul_one]
      mul_mem' := by
        intro x y hx hy p hp
        calc x * y * p = x * (y * p) := by group
          _ = x * (p * y) := by rw [hy p hp]
          _ = (x * p) * y := by group
          _ = (p * x) * y := by rw [hx p hp]
          _ = p * (x * y) := by group
      inv_mem' := by
        intro x hx p hp
        calc x⁻¹ * p = x⁻¹ * (p * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * p) * x⁻¹ := by rw [← hx p hp]
          _ = p * x⁻¹ := by group }
  let K : Subgroup ↥A := Cp.subgroupOf A
  haveI : K.Normal := by
    refine ⟨fun c hc g => ?_⟩
    intro p hp
    have hgp : (g : Γ)⁻¹ * p * (g : Γ) ∈ P := by
      simpa using hn (g⁻¹) (A.inv_mem g.2) p hp
    have hc' : (c : Γ) * ((g : Γ)⁻¹ * p * (g : Γ)) =
        ((g : Γ)⁻¹ * p * (g : Γ)) * (c : Γ) := hc _ hgp
    change ((g : Γ) * (c : Γ) * (g : Γ)⁻¹) * p =
      p * ((g : Γ) * (c : Γ) * (g : Γ)⁻¹)
    calc ((g : Γ) * (c : Γ) * (g : Γ)⁻¹) * p
        = (g : Γ) * ((c : Γ) * ((g : Γ)⁻¹ * p * (g : Γ))) * (g : Γ)⁻¹ := by group
      _ = (g : Γ) * (((g : Γ)⁻¹ * p * (g : Γ)) * (c : Γ)) * (g : Γ)⁻¹ := by rw [hc']
      _ = p * ((g : Γ) * (c : Γ) * (g : Γ)⁻¹) := by group
  have hKtop : K = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top K with h | h
    · exfalso
      have ha5K : a5 ∈ K := ha5comm
      rw [h] at ha5K
      exact ha5ne (Subgroup.mem_bot.mp ha5K)
    · exact h
  intro a ha p hp
  let aA : ↥A := ⟨a, ha⟩
  have haCp : (aA : Γ) ∈ Cp := by
    have haK : aA ∈ K := by rw [hKtop]; exact Subgroup.mem_top aA
    exact haK
  exact haCp p hp

end C10

end CFSG.OddStandard.SmallF3.Omega
