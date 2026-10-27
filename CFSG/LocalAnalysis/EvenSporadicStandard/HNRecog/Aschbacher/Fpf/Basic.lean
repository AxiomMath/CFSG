module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem disjoint_ker_range (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1) :
    Disjoint (LinearMap.ker (γ - 1)) (LinearMap.range (γ - 1)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rw [Submodule.mem_bot]
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvker, hvrange⟩ := hv
  obtain ⟨w, hw⟩ := hvrange
  have hγv : γ v = v := by
    have hker := hvker
    rw [LinearMap.mem_ker] at hker
    change γ v - v = 0 at hker
    exact sub_eq_zero.mp hker
  let N : Module.End (ZMod 2) V := ∑ i ∈ Finset.range 5, γ ^ i
  have hN : N * (γ - 1) = 0 := by
    have hgs := geom_sum_mul γ 5
    rw [h, sub_self] at hgs
    simpa only [N] using hgs
  have hNv : N v = 0 := by
    rw [← hw, ← Module.End.mul_apply, hN]
    rfl
  have hNv' : N v = v := by
    have hpow : ∀ i : ℕ, (γ ^ i) v = v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ', Module.End.mul_apply, ih, hγv]
    calc N v = (∑ i ∈ Finset.range 5, γ ^ i) v := rfl
      _ = ∑ i ∈ Finset.range 5, (γ ^ i) v := LinearMap.sum_apply _ _ _
      _ = ∑ _i ∈ Finset.range 5, v := Finset.sum_congr rfl (fun i _ => hpow i)
      _ = v := by
          rw [Finset.sum_const, Finset.card_range,
            ← Nat.cast_smul_eq_nsmul (R := ZMod 2) 5 v,
            show ((5 : ℕ) : ZMod 2) = 1 from by decide, one_smul]
  rw [← hNv', hNv]

private lemma mem_fixedPoints_zpowers_perm_iff {α : Type*} (g : Equiv.Perm α) (a : α) :
    a ∈ MulAction.fixedPoints (Subgroup.zpowers g) α ↔ g a = a := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using h ⟨g, Subgroup.mem_zpowers g⟩
  · intro h m
    have hm : (m : Equiv.Perm α) ∈ Subgroup.zpowers g := m.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    change (m : Equiv.Perm α) • a = a
    rw [← hk]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k

private theorem four_dvd_finrank_of_fixedFree_aux
    (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1)
    (U : Submodule (ZMod 2) V) (hU : ∀ u ∈ U, γ u ∈ U) (hfix : ∀ u ∈ U, γ u = u → u = 0) :
    4 ∣ finrank (ZMod 2) U := by
  let f : U → U := fun u => ⟨γ (u : V), hU (u : V) u.2⟩
  have hf_iter : ∀ n : ℕ, ∀ u : U, ((f^[n] u : U) : V) = (γ ^ n) (u : V) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
        intro u
        rw [Function.iterate_succ_apply']
        change γ (((f^[n] u : U) : V)) = (γ ^ (n + 1)) (u : V)
        rw [ih u, pow_succ', Module.End.mul_apply]
  have hf5 : f^[5] = id := by
    funext u
    apply Subtype.ext
    have hiter := hf_iter 5 u
    rw [h] at hiter
    simpa using hiter
  have hf_inj : Function.Injective f := by
    intro a b hab
    have h' : f^[5] a = f^[5] b := by
      change f^[4] (f a) = f^[4] (f b)
      exact congrArg (f^[4]) hab
    rw [hf5] at h'
    simpa using h'
  have hf_surj : Function.Surjective f := by
    intro b
    refine ⟨f^[4] b, ?_⟩
    have h' : f^[5] = f ∘ f^[4] := Function.iterate_succ' f 4
    change (f ∘ f^[4]) b = b
    rw [← h', hf5]
    rfl
  let g : Equiv.Perm U := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hg_apply : ∀ u : U, g u = f u := fun u => rfl
  have hg_zero : g (0 : U) = 0 := by
    rw [hg_apply]
    apply Subtype.ext
    simp [f]
  have hg5 : g ^ 5 = 1 := by
    have hgf : (g : U → U) = f := funext hg_apply
    have hiter : g^[5] = f^[5] := congrArg (fun φ : U → U => φ^[5]) hgf
    apply Equiv.ext
    intro u
    change g^[5] u = u
    rw [hiter, hf5]
    rfl
  have hIsPGroup : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (p := 5) (n := 1) (by
      simpa [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hg5)
  have hmem0 : (0 : U) ∈ MulAction.fixedPoints (Subgroup.zpowers g) U :=
    (mem_fixedPoints_zpowers_perm_iff g 0).mpr hg_zero
  have hsub : Subsingleton (MulAction.fixedPoints (Subgroup.zpowers g) U) := by
    refine ⟨fun a b => Subtype.ext ?_⟩
    have ha : (a : U) = 0 := by
      apply Subtype.ext
      refine hfix (a : U) a.1.2 ?_
      have hga : g (a : U) = (a : U) := (mem_fixedPoints_zpowers_perm_iff g (a : U)).mp a.2
      have := congrArg (fun x : U => (x : V)) hga
      simpa [hg_apply, f] using this
    have hb : (b : U) = 0 := by
      apply Subtype.ext
      refine hfix (b : U) b.1.2 ?_
      have hgb : g (b : U) = (b : U) := (mem_fixedPoints_zpowers_perm_iff g (b : U)).mp b.2
      have := congrArg (fun x : U => (x : V)) hgb
      simpa [hg_apply, f] using this
    rw [ha, hb]
  haveI : Nonempty (MulAction.fixedPoints (Subgroup.zpowers g) U) := ⟨⟨0, hmem0⟩⟩
  haveI : Subsingleton (MulAction.fixedPoints (Subgroup.zpowers g) U) := hsub
  have hcard_fix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers g) U) = 1 :=
    Nat.card_unique
  have hmod : Nat.card U ≡ 1 [MOD 5] := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h := hIsPGroup.card_modEq_card_fixedPoints U
    rwa [hcard_fix] at h
  have hUcard : Nat.card U = 2 ^ finrank (ZMod 2) U := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod]
  have hmod2 : 2 ^ finrank (ZMod 2) U ≡ 1 [MOD 5] := by
    simpa [hUcard] using hmod
  have hz : (2 : ZMod 5) ^ finrank (ZMod 2) U = 1 := by
    have h1 : ((2 ^ finrank (ZMod 2) U : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) :=
      (ZMod.natCast_eq_natCast_iff _ _ 5).mpr hmod2
    simpa using h1
  have h24 : (2 : ZMod 5) ^ 4 = 1 := by decide
  have h2m : ∀ m : ℕ, m < 4 → 0 < m → (2 : ZMod 5) ^ m ≠ 1 := by
    intro m hm hm0
    interval_cases m <;> decide
  have horder : orderOf (2 : ZMod 5) = 4 :=
    (orderOf_eq_iff (x := (2 : ZMod 5)) (by norm_num : (0 : ℕ) < 4)).mpr ⟨h24, h2m⟩
  exact horder ▸ orderOf_dvd_iff_pow_eq_one.mpr hz

theorem four_dvd_finrank_range (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1) :
    4 ∣ finrank (ZMod 2) (LinearMap.range (γ - 1)) := by
  refine four_dvd_finrank_of_fixedFree_aux γ h (LinearMap.range (γ - 1)) ?_ ?_
  · rintro u ⟨w, rfl⟩
    refine ⟨γ w, ?_⟩
    have hcomm : (γ - 1) * γ = γ * (γ - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hcomm]
  · intro u hu hgu
    have hker : u ∈ LinearMap.ker (γ - 1) := by
      rw [LinearMap.mem_ker]
      change γ u - u = 0
      rw [hgu, sub_self]
    have hdisj := disjoint_ker_range γ h
    rw [disjoint_iff_inf_le] at hdisj
    simpa using hdisj (Submodule.mem_inf.mpr ⟨hker, hu⟩)

theorem four_dvd_finrank_of_fixedFree (γ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1)
    (U : Submodule (ZMod 2) V) (hU : ∀ u ∈ U, γ u ∈ U) (hfix : ∀ u ∈ U, γ u = u → u = 0) :
    4 ∣ finrank (ZMod 2) U :=
  four_dvd_finrank_of_fixedFree_aux γ h U hU hfix

end CFSG.EvenSporadicStandard.HNRecog.Fpf
