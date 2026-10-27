module

public import CFSG.LargeExtraspecial.OrthoF2PairsCases
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem isTypeA_conj [FiniteDimensional (ZMod 2) V] {t g : V ≃ₗ[ZMod 2] V} {l : ℕ}
    (ht : IsTypeA q t l) (hg : g ∈ orthogonalGroup q) : IsTypeA q (g * t * g⁻¹) l := by
  obtain ⟨hiso, hne, hinv, hdim, hsing⟩ := ht
  have hg' : g⁻¹ ∈ orthogonalGroup q := inv_mem hg
  refine ⟨fun v => ?_, fun h => hne ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hiso,
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg']
  · calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hinv, mul_one, mul_inv_cancel]
  · rw [finrank_commSpace_conj, hdim]
  · intro x hx
    rw [commSpace_conj] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change q (g y) = 0
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg, hsing y hy]

namespace OrthoF2

theorem finite_linearEquiv [FiniteDimensional (ZMod 2) V] : Finite (V ≃ₗ[ZMod 2] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective _ (DFunLike.coe_injective (F := V ≃ₗ[ZMod 2] V))

theorem exists_mul_conj_eq_of_inverted {G : Type*} [Group G] {t : G} (htt : t * t = 1)
    {P : Subgroup G} (hodd : Odd (Nat.card P)) (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) {x : G}
    (hx : x ∈ P) : ∃ y ∈ P, x = t * (y⁻¹ * t * y⁻¹⁻¹) := by
  obtain ⟨k, hk⟩ := hodd
  have hxn : x ^ Nat.card P = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val h
  refine ⟨x ^ (k + 1), pow_mem hx _, ?_⟩
  set y := x ^ (k + 1)
  have hyy : y * y = x := by
    rw [← pow_add, show k + 1 + (k + 1) = Nat.card P + 1 by omega, pow_succ, hxn, one_mul]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : t * y⁻¹ * t = y := by
    have := hinv y⁻¹ (inv_mem (pow_mem hx _))
    rwa [htinv, inv_inv] at this
  calc x = y * y := hyy.symm
    _ = t * y⁻¹ * t * y := by rw [h1]
    _ = t * (y⁻¹ * t * y⁻¹⁻¹) := by rw [inv_inv]; simp only [mul_assoc]

end OrthoF2

theorem orderOf_eq_three_of_inverted [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {t : V ≃ₗ[ZMod 2] V} (ht : IsTypeA q t 2)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ orthogonalGroup q) (hodd : Odd (Nat.card P))
    (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ P) (hx1 : x ≠ 1) :
    orderOf x = 3 ∧ finrank (ZMod 2) (commSpace x) = 4 := by
  obtain ⟨y, hy, rfl⟩ := exists_mul_conj_eq_of_inverted ht.2.2.1 hodd hinv hx
  have hs := isTypeA_conj (q := q) ht (hP (inv_mem hy))
  have hdvd : orderOf (t * (y⁻¹ * t * y⁻¹⁻¹)) ∣ Nat.card P := by
    have h := orderOf_dvd_natCard (G := P) ⟨_, hx⟩
    rwa [Subgroup.orderOf_mk] at h
  have hodd' := Odd.of_dvd_nat hodd hdvd
  have h1 : orderOf (t * (y⁻¹ * t * y⁻¹⁻¹)) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨hmem, -⟩ := aschbacher_3_7 hq ht hs
  have h3 : orderOf (t * (y⁻¹ * t * y⁻¹⁻¹)) = 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact absurd h h1
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  exact ⟨h3, (commSpace_mul_of_orderOf_eq_three hq ht hs h3).2.2.1⟩

namespace OrthoF2

theorem card_dvd_of_finrank_commSpace_eq_four [FiniteDimensional (ZMod 2) V]
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (h4 : ∀ x ∈ P, x ≠ 1 → finrank (ZMod 2) (commSpace x) = 4) :
    Nat.card P ∣ 2 ^ finrank (ZMod 2) V + (Nat.card P - 1) * 2 ^ (finrank (ZMod 2) V - 4) := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype P := Fintype.ofFinite P
  let : ∀ g : P, Fintype (MulAction.fixedBy V g) := fun g => Fintype.ofFinite _
  let : Fintype (Quotient (MulAction.orbitRel P V)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group P V
  have hcard : ∀ g : P, Fintype.card (MulAction.fixedBy V g) =
      2 ^ finrank (ZMod 2) (fixSpace (g : V ≃ₗ[ZMod 2] V)) := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    have e : MulAction.fixedBy V g = (fixSpace (g : V ≃ₗ[ZMod 2] V) : Set V) := by
      ext v
      rw [MulAction.mem_fixedBy, SetLike.mem_coe, mem_fixSpace, Subgroup.smul_def]
      rfl
    rw [e, SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h1 : Fintype.card (MulAction.fixedBy V (1 : P)) = 2 ^ finrank (ZMod 2) V := by
    rw [hcard]
    congr 1
    have h := finrank_commSpace_add_finrank_fixSpace ((1 : P) : V ≃ₗ[ZMod 2] V)
    rw [OneMemClass.coe_one, commSpace_one, finrank_bot] at h
    rw [OneMemClass.coe_one]
    omega
  have h2 : ∀ g ∈ ({1}ᶜ : Finset P), Fintype.card (MulAction.fixedBy V g) =
      2 ^ (finrank (ZMod 2) V - 4) := by
    intro g hg
    have hg1 : (g : V ≃ₗ[ZMod 2] V) ≠ 1 := by
      intro h
      apply Finset.mem_compl.mp hg
      rw [Finset.mem_singleton]
      exact Subtype.ext h
    rw [hcard]
    congr 1
    have h := finrank_commSpace_add_finrank_fixSpace (g : V ≃ₗ[ZMod 2] V)
    rw [h4 g g.2 hg1] at h
    omega
  rw [Fintype.sum_eq_add_sum_compl 1, h1, Finset.sum_congr rfl h2, Finset.sum_const,
    Finset.card_compl, Finset.card_singleton, smul_eq_mul] at hB
  rw [Nat.card_eq_fintype_card, hB]
  exact Dvd.intro_left _ rfl

end OrthoF2

theorem aschbacher_5_7 [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {t : V ≃ₗ[ZMod 2] V} (ht : IsTypeA q t 2) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hP : P ≤ orthogonalGroup q) (hodd : Odd (Nat.card P))
    (hinv : ∀ x ∈ P, t * x * t⁻¹ = x⁻¹) : Nat.card P ≤ 3 := by
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have key := fun x (hx : x ∈ P) (hx1 : x ≠ 1) =>
    orderOf_eq_three_of_inverted hq ht hP hodd hinv hx hx1
  rcases P.bot_or_exists_ne_one with hbot | ⟨x₀, hx₀, hx₀1⟩
  · rw [hbot, Subgroup.card_bot]
    norm_num
  set m := finrank (ZMod 2) V with hm
  have hm4 : 4 ≤ m := by
    have h := Submodule.finrank_le (commSpace x₀)
    rwa [(key x₀ hx₀ hx₀1).2] at h
  have hdvd := card_dvd_of_finrank_commSpace_eq_four (fun x hx hx1 => (key x hx hx1).2)
  rw [← hm] at hdvd
  set n := Nat.card P with hn
  have hn1 : 1 ≤ n := hodd.pos
  have e : 2 ^ m + (n - 1) * 2 ^ (m - 4) = 2 ^ (m - 4) * (n + 15) := by
    have : 2 ^ m = 2 ^ (m - 4) * 16 := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, Nat.sub_add_cancel hm4]
    rw [this]
    zify [hn1]
    ring
  rw [e] at hdvd
  have hcop : Nat.Coprime n (2 ^ (m - 4)) := (Odd.coprime_two_right hodd).pow_right _
  have h15 : n ∣ 15 := by
    have h := hcop.dvd_of_dvd_mul_left hdvd
    exact (Nat.dvd_add_right (dvd_refl n)).mp h
  have h5 : ¬ 5 ∣ n := by
    intro h5
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : Finite P := inferInstance
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 h5
    rw [← Subgroup.orderOf_coe] at hx
    by_cases hx1 : (x : V ≃ₗ[ZMod 2] V) = 1
    · rw [hx1, orderOf_one] at hx
      norm_num at hx
    · rw [(key x x.2 hx1).1] at hx
      norm_num at hx
  have hle : n ≤ 15 := Nat.le_of_dvd (by norm_num) h15
  interval_cases n <;> omega

theorem commute_of_normalizes_of_coprime [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {t : V ≃ₗ[ZMod 2] V} (ht : IsTypeA q t 2)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hP : P ≤ orthogonalGroup q)
    (hcop : Nat.Coprime (Nat.card P) 6) (hnorm : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ P) : t * x = x * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht.2.2.1
  have hs := isTypeA_conj (q := q) ht (hP (inv_mem hx))
  have hmem : t * (x⁻¹ * t * x⁻¹⁻¹) ∈ P := by
    have h := mul_mem (hnorm x⁻¹ (inv_mem hx)) hx
    rw [htinv] at h
    rw [inv_inv]
    simpa only [mul_assoc] using h
  have hdvd : orderOf (t * (x⁻¹ * t * x⁻¹⁻¹)) ∣ Nat.card P := by
    have h := orderOf_dvd_natCard (G := P) ⟨_, hmem⟩
    rwa [Subgroup.orderOf_mk] at h
  have hcop' := Nat.Coprime.coprime_dvd_left hdvd hcop
  obtain ⟨hmem', -⟩ := aschbacher_3_7 hq ht hs
  have h1 : orderOf (t * (x⁻¹ * t * x⁻¹⁻¹)) = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem'
    rcases hmem' with h | h | h | h
    · exact h
    all_goals (rw [h] at hcop'; exact absurd hcop' (by norm_num))
  rw [orderOf_eq_one_iff, inv_inv] at h1
  have hc : x⁻¹ * t * x = t := by
    have h := eq_inv_of_mul_eq_one_right h1
    rwa [htinv] at h
  calc t * x = x * (x⁻¹ * t * x) := by group
    _ = x * t := by rw [hc]

end CFSG.LargeExtraspecial
