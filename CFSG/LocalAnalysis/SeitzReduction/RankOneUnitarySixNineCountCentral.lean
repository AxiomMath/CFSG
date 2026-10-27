module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountSum
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.SeitzReduction.RankOne

namespace SixNineCount

open Finset

variable {R : Type*} [Ring R]

theorem pow_conj_mem {F : Subgroup Rˣ} {ε : Rˣ} (hεF : ∀ f ∈ F, ε * f * ε⁻¹ ∈ F) :
    ∀ i : ℕ, ∀ f ∈ F, ε ^ i * f * (ε ^ i)⁻¹ ∈ F := by
  intro i
  induction i with
  | zero => intro f hf; simpa using hf
  | succ i ih =>
    intro f hf
    have e : ε ^ (i + 1) * f * (ε ^ (i + 1))⁻¹ = ε * (ε ^ i * f * (ε ^ i)⁻¹) * ε⁻¹ := by
      rw [pow_succ']
      group
    rw [e]
    exact hεF _ (ih f hf)

theorem sum_eq_card_of_free (F : Subgroup Rˣ) [Fintype F] {ε : Rˣ} {p : ℕ} (hp : 0 < p)
    (hεF : ∀ f ∈ F, ε * f * ε⁻¹ ∈ F)
    (hfree : ∀ i, 0 < i → i < p → ∀ f ∈ F, ε ^ i * f = f * ε ^ i → f = 1)
    (hε : ∑ i ∈ range p, (ε : R) ^ i = 0) :
    ∑ f : F, ((f : Rˣ) : R) = (Fintype.card F : R) := by
  classical
  have hterm : ∀ i, 0 < i → i < p →
      ∑ f : F, (((f : Rˣ) * ε ^ i * (f : Rˣ)⁻¹ : Rˣ) : R) =
        (∑ f : F, ((f : Rˣ) : R)) * (ε : R) ^ i := by
    intro i hi0 hip
    let ψ : F → F := fun f => ⟨(f : Rˣ) * (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹),
      F.mul_mem f.2 (pow_conj_mem hεF i _ (F.inv_mem f.2))⟩
    have hψ : Function.Injective ψ := by
      intro f g hfg
      have h1 : (f : Rˣ) * (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹) =
          (g : Rˣ) * (ε ^ i * (g : Rˣ)⁻¹ * (ε ^ i)⁻¹) := congrArg Subtype.val hfg
      have heq : (g : Rˣ)⁻¹ * f = ε ^ i * ((g : Rˣ)⁻¹ * f) * (ε ^ i)⁻¹ := by
        calc (g : Rˣ)⁻¹ * f = (g : Rˣ)⁻¹ * ((f : Rˣ) * (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹)) *
              (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹)⁻¹ := by group
          _ = (g : Rˣ)⁻¹ * ((g : Rˣ) * (ε ^ i * (g : Rˣ)⁻¹ * (ε ^ i)⁻¹)) *
              (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹)⁻¹ := by rw [h1]
          _ = ε ^ i * ((g : Rˣ)⁻¹ * f) * (ε ^ i)⁻¹ := by group
      rw [eq_mul_inv_iff_mul_eq] at heq
      have h3 := hfree i hi0 hip _ (F.mul_mem (F.inv_mem g.2) f.2) heq.symm
      rw [inv_mul_eq_one] at h3
      exact Subtype.ext h3.symm
    rw [sum_mul]
    refine Fintype.sum_bijective ψ hψ.bijective_of_finite _ _ (fun f => ?_)
    have e : (f : Rˣ) * ε ^ i * (f : Rˣ)⁻¹ = ((ψ f : F) : Rˣ) * ε ^ i := by
      show _ = (f : Rˣ) * (ε ^ i * (f : Rˣ)⁻¹ * (ε ^ i)⁻¹) * ε ^ i
      group
    rw [e, Units.val_mul, Units.val_pow_eq_pow_val]
  have hzero : ∑ f : F, ((f : Rˣ) : R) * (∑ i ∈ range p, (ε : R) ^ i) *
      (((f : Rˣ)⁻¹ : Rˣ) : R) = 0 := by
    simp [hε]
  have hexp : ∑ f : F, ((f : Rˣ) : R) * (∑ i ∈ range p, (ε : R) ^ i) *
      (((f : Rˣ)⁻¹ : Rˣ) : R) =
      ∑ i ∈ range p, ∑ f : F, (((f : Rˣ) * ε ^ i * (f : Rˣ)⁻¹ : Rˣ) : R) := by
    rw [sum_comm]
    refine sum_congr rfl fun f _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rfl
  rw [hexp, range_eq_Ico, sum_eq_sum_Ico_succ_bot hp] at hzero
  have h0 : ∑ f : F, (((f : Rˣ) * ε ^ 0 * (f : Rˣ)⁻¹ : Rˣ) : R) = Fintype.card F := by
    simp
  have h1 : ∑ i ∈ Ico (0 + 1) p, ∑ f : F, (((f : Rˣ) * ε ^ i * (f : Rˣ)⁻¹ : Rˣ) : R) =
      (∑ f : F, ((f : Rˣ) : R)) * ∑ i ∈ Ico 1 p, (ε : R) ^ i := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hip⟩ := mem_Ico.mp hi
    exact hterm i hi1 hip
  have h2 : ∑ i ∈ Ico 1 p, (ε : R) ^ i = -1 := by
    have h := hε
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hp, pow_zero] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  rw [h0, h1, h2, mul_neg_one, add_neg_eq_zero] at hzero
  exact hzero.symm

@[expose] def commSubgroup (A : Subgroup Rˣ) (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (ε : Rˣ) (hεA : ∀ a ∈ A, ε * a * ε⁻¹ ∈ A) : Subgroup Rˣ where
  carrier := {f | ∃ x ∈ A, f = ε * x * ε⁻¹ * x⁻¹}
  one_mem' := ⟨1, A.one_mem, by group⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, A.mul_mem hx hy, ?_⟩
    have hc : x⁻¹ * (ε * y * ε⁻¹ * y⁻¹) = (ε * y * ε⁻¹ * y⁻¹) * x⁻¹ :=
      hAcomm _ (A.inv_mem hx) _ (A.mul_mem (hεA y hy) (A.inv_mem hy))
    calc ε * x * ε⁻¹ * x⁻¹ * (ε * y * ε⁻¹ * y⁻¹) =
          ε * x * ε⁻¹ * (x⁻¹ * (ε * y * ε⁻¹ * y⁻¹)) := by group
      _ = ε * x * ε⁻¹ * ((ε * y * ε⁻¹ * y⁻¹) * x⁻¹) := by rw [hc]
      _ = ε * (x * y) * ε⁻¹ * (x * y)⁻¹ := by group
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x⁻¹, A.inv_mem hx, ?_⟩
    have hc : x * (ε * x * ε⁻¹)⁻¹ = (ε * x * ε⁻¹)⁻¹ * x :=
      hAcomm _ hx _ (A.inv_mem (hεA x hx))
    calc (ε * x * ε⁻¹ * x⁻¹)⁻¹ = x * (ε * x * ε⁻¹)⁻¹ := by group
      _ = (ε * x * ε⁻¹)⁻¹ * x := hc
      _ = ε * x⁻¹ * ε⁻¹ * x⁻¹⁻¹ := by group

section CommSubgroup

variable {A : Subgroup Rˣ} {hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a} {ε : Rˣ}
  {hεA : ∀ a ∈ A, ε * a * ε⁻¹ ∈ A}

theorem commSubgroup_le : commSubgroup A hAcomm ε hεA ≤ A := by
  rintro _ ⟨x, hx, rfl⟩
  exact A.mul_mem (hεA x hx) (A.inv_mem hx)

theorem conj_mem_commSubgroup :
    ∀ f ∈ commSubgroup A hAcomm ε hεA, ε * f * ε⁻¹ ∈ commSubgroup A hAcomm ε hεA := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨ε * x * ε⁻¹, hεA x hx, by group⟩

end CommSubgroup

theorem commute_aux_ne (h2 : (2 : R) = 0) (A : Subgroup Rˣ) [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hAexp : ∀ a ∈ A, a ^ l = 1) {ε : Rˣ} {p : ℕ} (hp : p.Prime) (hpl : p ≠ l)
    (hεp : ε ^ p = 1) (hεA : ∀ a ∈ A, ε * a * ε⁻¹ ∈ A) (hε : ∑ i ∈ range p, (ε : R) ^ i = 0)
    {f₀ : Rˣ} (hf₀ : f₀ ∈ commSubgroup A hAcomm ε hεA) (hf₀ne : f₀ ≠ 1) : False := by
  classical
  set F := commSubgroup A hAcomm ε hεA with hFdef
  have hFA : F ≤ A := commSubgroup_le
  have : Finite F :=
    Finite.of_injective (Subgroup.inclusion hFA) (Subgroup.inclusion_injective hFA)
  let : Fintype F := Fintype.ofFinite F
  have hfix : ∀ f ∈ F, ε * f = f * ε → f = 1 := by
    rintro f ⟨x, hx, hfx⟩ hcomm
    have hεx : ε * x = f * x * ε := by rw [hfx]; group
    have hpow : ∀ k : ℕ, ε ^ k * x = f ^ k * x * ε ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hcomm' : ε * f ^ k = f ^ k * ε := (Commute.pow_right hcomm k).eq
        calc ε ^ (k + 1) * x = ε * (ε ^ k * x) := by rw [pow_succ', mul_assoc]
          _ = ε * (f ^ k * x * ε ^ k) := by rw [ih]
          _ = (ε * f ^ k) * x * ε ^ k := by group
          _ = f ^ k * (ε * x) * ε ^ k := by rw [hcomm']; group
          _ = f ^ k * (f * x * ε) * ε ^ k := by rw [hεx]
          _ = f ^ (k + 1) * x * ε ^ (k + 1) := by rw [pow_succ f k, pow_succ' ε k]; group
    have hfp : f ^ p = 1 := by
      have h := hpow p
      rw [hεp, one_mul, mul_one] at h
      exact mul_right_cancel (h.symm.trans (one_mul x).symm)
    have hfl : f ^ l = 1 := hAexp f (hFA ⟨x, hx, hfx⟩)
    have hcop : Nat.Coprime p l := (Nat.coprime_primes hp hl).mpr hpl
    have h1 : orderOf f = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hfp) hcop)
      (orderOf_dvd_of_pow_eq_one hfl)
    exact orderOf_eq_one_iff.mp h1
  have hfree : ∀ i, 0 < i → i < p → ∀ f ∈ F, ε ^ i * f = f * ε ^ i → f = 1 := by
    intro i hi0 hip f hf hcomm
    apply hfix f hf
    have hcop : Nat.Coprime i p := Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hi0 hip))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hεeq : (ε ^ i) ^ m = ε := by
      rw [← pow_mul, pow_eq_pow_mod_of_pow_eq_one hεp (i * m), hm, pow_one]
    have := (Commute.pow_left hcomm m).eq
    rwa [hεeq] at this
  have hsum := sum_eq_card_of_free F hp.pos conj_mem_commSubgroup hfree hε
  have hodd : Odd (Fintype.card F) := by
    rcases Nat.even_or_odd (Fintype.card F) with h | h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 (even_iff_two_dvd.mp h)
      have hdvd : orderOf (g : Rˣ) ∣ l := orderOf_dvd_of_pow_eq_one (hAexp _ (hFA g.2))
      rw [Subgroup.orderOf_coe, hg] at hdvd
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl).mp hdvd).symm
    · exact h
  rw [natCast_eq_one_of_odd h2 hodd] at hsum
  have hall : ∀ g : F, (g : Rˣ) = 1 := by
    intro g
    have hmul : ((g : Rˣ) : R) * ∑ f : F, ((f : Rˣ) : R) = ∑ f : F, ((f : Rˣ) : R) := by
      rw [mul_sum]
      exact Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun f => by simp)
    rw [hsum, mul_one] at hmul
    exact Units.val_eq_one.mp hmul
  exact hf₀ne (hall ⟨f₀, hf₀⟩)

theorem commute_aux_eq (h2 : (2 : R) = 0) (A : Subgroup Rˣ) [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hAexp : ∀ a ∈ A, a ^ p = 1) {ε : Rˣ} (hεp : ε ^ p = 1) (hεA : ∀ a ∈ A, ε * a * ε⁻¹ ∈ A)
    (hε : ∑ i ∈ range p, (ε : R) ^ i = 0) {f₀ : Rˣ} (hf₀ : f₀ ∈ commSubgroup A hAcomm ε hεA)
    (hf₀ne : f₀ ≠ 1) : False := by
  classical
  set F := commSubgroup A hAcomm ε hεA with hFdef
  have hFA : F ≤ A := commSubgroup_le
  have : Finite F :=
    Finite.of_injective (Subgroup.inclusion hFA) (Subgroup.inclusion_injective hFA)
  let : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hcardF : p ∣ Fintype.card F := by
    have hord : orderOf (⟨f₀, hf₀⟩ : F) = p := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hAexp _ (hFA hf₀)) hf₀ne
    rw [← hord]
    exact orderOf_dvd_card
  let σ : Function.End F := fun f => ⟨ε * f * ε⁻¹, conj_mem_commSubgroup _ f.2⟩
  have hσpow : ∀ n : ℕ, ∀ f : F, (((σ ^ n) f : F) : Rˣ) = ε ^ n * f * (ε ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro f; show ((f : F) : Rˣ) = _; simp
    | succ n ih =>
      intro f
      show ((σ^[n + 1] f : F) : Rˣ) = _
      rw [Function.iterate_succ_apply']
      show ε * ((σ^[n] f : F) : Rˣ) * ε⁻¹ = _
      rw [show ((σ^[n] f : F) : Rˣ) = ε ^ n * f * (ε ^ n)⁻¹ from ih f, pow_succ']
      group
  have hσp : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext f
    apply Subtype.ext
    show (((σ ^ p) f : F) : Rˣ) = (f : Rˣ)
    rw [hσpow, hεp, one_mul, inv_one, mul_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hσp
  have hfixdvd : p ∣ Fintype.card (Function.fixedPoints σ) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hcardF))
  have h1fix : (1 : F) ∈ Function.fixedPoints σ := by
    show σ 1 = 1
    apply Subtype.ext
    show ε * ((1 : F) : Rˣ) * ε⁻¹ = ((1 : F) : Rˣ)
    simp
  have hcard1 : 1 < Fintype.card (Function.fixedPoints σ) := by
    have hpos : 0 < Fintype.card (Function.fixedPoints σ) :=
      Fintype.card_pos_iff.mpr ⟨⟨1, h1fix⟩⟩
    have := Nat.le_of_dvd hpos hfixdvd
    have := hp.two_le
    omega
  obtain ⟨⟨⟨c, hcF⟩, hcfix⟩, hcne⟩ := Fintype.exists_ne_of_one_lt_card hcard1 ⟨1, h1fix⟩
  have hc1 : c ≠ 1 := by
    intro h
    apply hcne
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hcfix' : σ ⟨c, hcF⟩ = ⟨c, hcF⟩ := hcfix
  have hcε : ε * c * ε⁻¹ = c := congrArg Subtype.val hcfix'
  have hcomm : ε * c = c * ε := by
    calc ε * c = ε * c * ε⁻¹ * ε := by group
      _ = c * ε := by rw [hcε]
  have hcA : c ∈ A := hFA hcF
  obtain ⟨x, hx, hcx₀⟩ := hcF
  have hcx : c * x = x * c := hAcomm _ hcA _ hx
  have hconj1 : x⁻¹ * ε * x = c * ε := by
    calc x⁻¹ * ε * x = x⁻¹ * (ε * x * ε⁻¹ * x⁻¹) * x * ε := by group
      _ = x⁻¹ * (c * x) * ε := by rw [← hcx₀]; group
      _ = x⁻¹ * (x * c) * ε := by rw [hcx]
      _ = c * ε := by group
  have hconj : ∀ j : ℕ, (x ^ j)⁻¹ * ε * x ^ j = c ^ j * ε := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hcxj : c ^ j * x = x * c ^ j := (Commute.pow_left hcx j).eq
      calc (x ^ (j + 1))⁻¹ * ε * x ^ (j + 1) = x⁻¹ * ((x ^ j)⁻¹ * ε * x ^ j) * x := by
            rw [pow_succ]; group
        _ = x⁻¹ * (c ^ j * ε) * x := by rw [ih]
        _ = x⁻¹ * (c ^ j * x) * (x⁻¹ * ε * x) := by group
        _ = x⁻¹ * (x * c ^ j) * (c * ε) := by rw [hcxj, hconj1]
        _ = c ^ (j + 1) * ε := by rw [pow_succ]; group
  have key : (c : R) = 1 := by
    refine eq_one_of_geom_sum_eq_zero h2 (b := (ε : R)) ?_ hp hp2 ?_ ?_
    · show (c : R) * ε = ε * c
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    · rw [← Units.val_pow_eq_pow_val, hAexp c hcA, Units.val_one]
    · intro j _
      obtain ⟨u, hεc⟩ : ∃ u : Rˣ, ε * c ^ j = u⁻¹ * ε * u :=
        ⟨x ^ j, by rw [hconj j]; exact (Commute.pow_right hcomm j).eq⟩
      have e : ∀ i, ((ε : R) * (c : R) ^ j) ^ i = ((u⁻¹ : Rˣ) : R) * (ε : R) ^ i * (u : R) := by
        intro i
        have hu : (ε * c ^ j) ^ i = u⁻¹ * ε ^ i * u := by
          rw [hεc]
          have := conj_pow (a := u⁻¹) (b := ε) (i := i)
          rwa [inv_inv] at this
        have := congrArg Units.val hu
        simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
        exact this
      simp_rw [e]
      rw [← sum_mul, ← mul_sum, hε, mul_zero, zero_mul]
  exact hc1 (Units.val_eq_one.mp key)

theorem commute_of_geom_sum_eq_zero (h2 : (2 : R) = 0) (A : Subgroup Rˣ) [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hAexp : ∀ a ∈ A, a ^ l = 1) {ε : Rˣ} {p : ℕ} (hp : p.Prime) (hεp : ε ^ p = 1)
    (hεA : ∀ a ∈ A, ε * a * ε⁻¹ ∈ A) (hε : ∑ i ∈ range p, (ε : R) ^ i = 0) :
    ∀ a ∈ A, ε * a = a * ε := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a₀, ha₀, hne⟩ := hcon
  have hf₀ : ε * a₀ * ε⁻¹ * a₀⁻¹ ∈ commSubgroup A hAcomm ε hεA := ⟨a₀, ha₀, rfl⟩
  have hf₀ne : ε * a₀ * ε⁻¹ * a₀⁻¹ ≠ 1 := by
    intro h
    apply hne
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  by_cases hpl : p = l
  · subst hpl
    exact commute_aux_eq h2 A hAcomm hp hl2 hAexp hεp hεA hε hf₀ hf₀ne
  · exact commute_aux_ne h2 A hAcomm hl hl2 hAexp hp hpl hεp hεA hε hf₀ hf₀ne

end SixNineCount

end CFSG.SeitzReduction.RankOne
