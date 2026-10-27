module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.SmallF3.Omega

private lemma pow_two_eq_one_or_sixteen {k N : ℕ} (hk : k ≤ 4) (hN : N = 2 ^ k)
    (hmod : (16 : ℕ) ≡ N [MOD 5]) : N = 1 ∨ N = 16 := by
  subst hN
  interval_cases k
  · left; rfl
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · exfalso; revert hmod; decide
  · right; rfl

private lemma pow_three_inj {e d : ℕ} (he : e ≤ 3) (hd : d ≤ 3)
    (h : 3 ^ d ≡ 3 ^ e [MOD 5]) : e = d := by
  interval_cases d <;> interval_cases e <;>
    first
      | rfl
      | (exfalso; revert h; decide)

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem fg_five_dvd_card_of_free (σ : Equiv.Perm α) (hσ : σ ^ 5 = 1) (T : Finset α)
    (hT : ∀ a, a ∈ T ↔ σ a ∈ T) (hfree : ∀ a ∈ T, σ a ≠ a) : 5 ∣ T.card := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra h
  have hcard : ¬ 5 ∣ Fintype.card {a // a ∈ T} := by
    simpa [Fintype.card_coe] using h
  let σ' : Equiv.Perm {a // a ∈ T} := σ.subtypePerm (fun a => (hT a).symm)
  have hσ' : σ' ^ 5 = 1 := by
    ext x
    change (((σ.subtypePerm (fun a => (hT a).symm)) ^ 5) x : α) = (x : α)
    rw [Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply]
    change (σ ^ 5) (x : α) = (x : α)
    rw [hσ]
    rfl
  have hσ'' : σ' ^ 5 ^ 1 = 1 := by simpa using hσ'
  obtain ⟨a, ha⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1) hcard hσ''
  exact hfree a a.2 (congrArg Subtype.val ha)

theorem fg_orbit_count (σ : Equiv.Perm α) (hσ : σ ^ 5 = 1) (S : Finset α)
    (hS : ∀ a, a ∈ S ↔ σ a ∈ S) (hfree : ∀ a ∈ S, σ a ≠ a) (d : α → ℕ)
    (hd : ∀ a, d (σ a) = d a) (hpos : ∀ a ∈ S, 1 ≤ d a) (hne : S.Nonempty)
    (hsum : ∑ a ∈ S, d a ≤ 6) : S.card = 5 ∧ ∀ a ∈ S, d a = 1 := by
  classical
  let S2 : Finset α := S.filter (fun a => 2 ≤ d a)
  have h5S : 5 ∣ S.card := fg_five_dvd_card_of_free σ hσ S hS hfree
  have hS2inv : ∀ a, a ∈ S2 ↔ σ a ∈ S2 := by
    intro a
    rw [Finset.mem_filter, Finset.mem_filter, hS a, hd a]
  have hfree2 : ∀ a ∈ S2, σ a ≠ a := fun a ha => hfree a (Finset.mem_filter.mp ha).1
  have h5S2 : 5 ∣ S2.card := fg_five_dvd_card_of_free σ hσ S2 hS2inv hfree2
  have hineq : S.card + S2.card ≤ ∑ a ∈ S, d a := by
    calc S.card + S2.card
        = ∑ a ∈ S, (1 + if 2 ≤ d a then 1 else 0) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · simp
          · exact Finset.card_filter (fun a => 2 ≤ d a) S
      _ ≤ ∑ a ∈ S, d a := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases h : 2 ≤ d a
          · simp [h]
          · simp [h]; exact hpos a ha
  have hne1 : 1 ≤ S.card := Finset.card_pos.mpr hne
  have hge5 : 5 ≤ S.card := by
    obtain ⟨k, hk⟩ := h5S
    omega
  have hS2le : S2.card ≤ 1 := by
    have := hineq.trans hsum
    omega
  have hS2zero : S2.card = 0 := by
    obtain ⟨k, hk⟩ := h5S2
    omega
  have hle6 : S.card ≤ 6 := by
    have := hineq.trans hsum
    rw [hS2zero] at this
    omega
  have hS5 : S.card = 5 := by
    obtain ⟨k, hk⟩ := h5S
    omega
  refine ⟨hS5, fun a ha => ?_⟩
  have hmem : a ∉ S2 := by
    rw [Finset.card_eq_zero.mp hS2zero]
    simp
  rw [Finset.mem_filter] at hmem
  have hlt : ¬ 2 ≤ d a := fun h => hmem ⟨ha, h⟩
  have := hpos a ha
  omega

end Perm

section Group

variable {Γ : Type*} [Group Γ] {f : Γ}

theorem fg_card_modEq_centralizer (hf : f ^ 5 = 1) (H : Subgroup Γ) [Finite H]
    (hH : ∀ h, h ∈ H ↔ f * h * f⁻¹ ∈ H) :
    Nat.card H ≡ Nat.card ↥(H ⊓ Subgroup.centralizer {f}) [MOD 5] := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fintype H := Fintype.ofFinite H
  let π : Equiv.Perm H :=
    { toFun := fun h => ⟨f * (h : Γ) * f⁻¹, (hH h).mp h.2⟩
      invFun := fun h => ⟨f⁻¹ * (h : Γ) * f,
        (hH (f⁻¹ * (h : Γ) * f)).mpr (by
          have hval : f * (f⁻¹ * (h : Γ) * f) * f⁻¹ = (h : Γ) := by group
          rw [hval]; exact h.2)⟩
      left_inv := fun h => Subtype.ext (by group)
      right_inv := fun h => Subtype.ext (by group) }
  have hpow : ∀ n : ℕ, ∀ h : H, ((π ^ n) h : Γ) = f ^ n * (h : Γ) * (f ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      rw [pow_succ, Equiv.Perm.mul_apply]
      change ((π ^ n) (π h) : Γ) = _
      rw [ih (π h)]
      show f ^ n * (f * (h : Γ) * f⁻¹) * (f ^ n)⁻¹ =
        f ^ (n + 1) * (h : Γ) * (f ^ (n + 1))⁻¹
      rw [pow_succ]
      group
  have hπ5 : π ^ 5 = 1 := by
    ext h
    rw [hpow 5 h, hf]
    simp
  have hmod :=
    Equiv.Perm.card_fixedPoints_modEq (f := (⇑π : Function.End H)) (p := 5) (n := 1) (by
      rw [pow_one]
      have h2 := Equiv.Perm.coe_pow π 5
      rw [hπ5, Equiv.Perm.coe_one] at h2
      exact h2.symm)
  have hfixed : Nat.card ↥(H ⊓ Subgroup.centralizer {f}) =
      Nat.card (Function.fixedPoints (⇑π : Function.End H)) := by
    refine Nat.card_congr ⟨fun x => ?_, fun y => ?_, ?_, ?_⟩
    · have hxcomm : (x : Γ) * f = f * (x : Γ) :=
        Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      refine ⟨⟨(x : Γ), x.2.1⟩, ?_⟩
      apply Subtype.ext
      change f * (x : Γ) * f⁻¹ = (x : Γ)
      calc f * (x : Γ) * f⁻¹ = (x : Γ) * f * f⁻¹ := by rw [← hxcomm]
        _ = (x : Γ) := by group
    · have hy : π y.1 = y.1 := y.2
      have hval : f * (y.1 : Γ) * f⁻¹ = (y.1 : Γ) := by
        have := congrArg Subtype.val hy
        simpa [π] using this
      have hcomm : (y.1 : Γ) * f = f * (y.1 : Γ) := by
        calc (y.1 : Γ) * f = (f * (y.1 : Γ) * f⁻¹) * f := by rw [hval]
          _ = f * (y.1 : Γ) := by group
      exact ⟨(y.1 : Γ), y.1.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    · intro x; rfl
    · intro y; rfl
  have hmod' : Nat.card H ≡
      Nat.card (Function.fixedPoints (⇑π : Function.End H)) [MOD 5] := by
    simpa only [Nat.card_eq_fintype_card] using hmod
  rw [← hfixed] at hmod'
  exact hmod'

theorem fg_card_centralizer_sixteen (hf : f ^ 5 = 1) (B : Subgroup Γ) (hB : Nat.card B = 16)
    (hBn : ∀ h, h ∈ B ↔ f * h * f⁻¹ ∈ B) :
    Nat.card ↥(B ⊓ Subgroup.centralizer {f}) = 1 ∨
      Nat.card ↥(B ⊓ Subgroup.centralizer {f}) = 16 := by
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  have hmod := fg_card_modEq_centralizer (f := f) hf B hBn
  rw [hB] at hmod
  have hdvd : Nat.card ↥(B ⊓ Subgroup.centralizer {f}) ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hB]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hN⟩ := (Nat.dvd_prime_pow (p := 2) (Nat.prime_two) (m := 4)).mp hdvd
  exact pow_two_eq_one_or_sixteen hk hN hmod

theorem fg_card_invariant_subgroup (hf : f ^ 5 = 1) (B H : Subgroup Γ) (hB : Nat.card B = 16)
    (hHB : H ≤ B) (hBC : B ⊓ Subgroup.centralizer {f} = ⊥)
    (hH : ∀ h, h ∈ H ↔ f * h * f⁻¹ ∈ H) : Nat.card H = 1 ∨ Nat.card H = 16 := by
  haveI : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  haveI : Finite H :=
    Finite.of_injective (Subgroup.inclusion hHB) (Subgroup.inclusion_injective hHB)
  have hmod := fg_card_modEq_centralizer (f := f) hf H hH
  have hbot : H ⊓ Subgroup.centralizer {f} = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ B ⊓ Subgroup.centralizer {f} := ⟨hHB hx.1, hx.2⟩
      rw [hBC] at hx'
      exact hx'
    · exact bot_le
  have hcardC : Nat.card ↥(H ⊓ Subgroup.centralizer {f}) = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  rw [hcardC] at hmod
  have hdvd : Nat.card H ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hB]
    exact Subgroup.card_dvd_of_le hHB
  obtain ⟨k, hk, hN⟩ := (Nat.dvd_prime_pow (p := 2) (Nat.prime_two) (m := 4)).mp hdvd
  exact pow_two_eq_one_or_sixteen hk hN
    ((by decide : (16 : ℕ) ≡ 1 [MOD 5]).trans hmod.symm)

end Group

section Space

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

theorem fg_fix_of_finrank_le_three (E : Submodule (ZMod 3) V) (f : V ≃ₗ[ZMod 3] V)
    (hf : f ^ 5 = 1) (hE : ∀ v ∈ E, f v ∈ E) (hd : Module.finrank (ZMod 3) E ≤ 3) :
    ∀ v ∈ E, f v = v := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite E := Module.finite_of_finite (R := ZMod 3) (M := E)
  haveI : Fintype E := Fintype.ofFinite E
  let g : Function.End E := fun x => ⟨f x, hE x x.2⟩
  have hgpow : ∀ n : ℕ, ∀ x : E, ((g ^ n) x : V) = (f ^ n) (x : V) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ']
      change f (((g ^ n) x : V)) = (f ^ (n + 1)) (x : V)
      rw [ih x]
      rw [pow_succ']
      rfl
  have hg5 : g ^ 5 = 1 := by
    funext x
    apply Subtype.ext
    show ((g ^ 5) x : V) = (x : V)
    rw [hgpow 5 x, hf]
    rfl
  have hmod5 :=
    Equiv.Perm.card_fixedPoints_modEq (f := (g : Function.End E)) (p := 5) (n := 1) (by
      rw [pow_one]
      exact hg5)
  have hcardE : Fintype.card E = 3 ^ Module.finrank (ZMod 3) E := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := E), ZMod.card]
  let K : Submodule (ZMod 3) V :=
    E ⊓ LinearMap.ker (f.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V))
  haveI : Finite K := Module.finite_of_finite (R := ZMod 3) (M := K)
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 3 ^ Module.finrank (ZMod 3) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod 3) (V := K), ZMod.card]
  have hcardFix : Fintype.card (Function.fixedPoints (g : E → E)) = Fintype.card K := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x => ⟨(x.1 : V), ⟨x.1.2, ?_⟩⟩
        invFun := fun y => ⟨⟨(y.1 : V), y.2.1⟩, ?_⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
    · have hx : f (x.1 : V) = (x.1 : V) := congrArg Subtype.val x.2
      show (f.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (x.1 : V) ∈
        (⊥ : Submodule (ZMod 3) V)
      rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.id_apply]
      exact sub_eq_zero.mpr hx
    · apply Subtype.ext
      show f ((y.1 : V)) = (y.1 : V)
      have hy : (f.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) (y.1 : V) ∈
          (⊥ : Submodule (ZMod 3) V) := y.2.2
      rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.id_apply] at hy
      exact sub_eq_zero.mp hy
  have hmod5' : Fintype.card E ≡ Fintype.card (Function.fixedPoints (g : E → E)) [MOD 5] := by
    simpa using hmod5
  have hmod : 3 ^ Module.finrank (ZMod 3) E ≡ 3 ^ Module.finrank (ZMod 3) K [MOD 5] := by
    simpa only [hcardE, hcardFix, hcardK] using hmod5'
  have hdK : Module.finrank (ZMod 3) K ≤ Module.finrank (ZMod 3) E :=
    Submodule.finrank_mono inf_le_left
  have heq : Module.finrank (ZMod 3) K = Module.finrank (ZMod 3) E :=
    pow_three_inj (le_trans hdK hd) hd hmod
  have hKE : K = E := Submodule.eq_of_le_of_finrank_eq inf_le_left heq
  intro v hv
  have hvK : v ∈ K := by rw [hKE]; exact hv
  have hsub : (f.toLinearMap - (LinearMap.id : V →ₗ[ZMod 3] V)) v ∈
      (⊥ : Submodule (ZMod 3) V) := hvK.2
  rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.id_apply] at hsub
  exact sub_eq_zero.mp hsub

end Space

end CFSG.OddStandard.SmallF3.Omega
