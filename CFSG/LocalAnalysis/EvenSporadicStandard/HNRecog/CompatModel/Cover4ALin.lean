module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L27.LA5Cyclic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Module CFSG.EvenSporadicStandard.HNRecog.Harada.L27

section Cover

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem five_nsmul_eq (x : V) : (5 : ℕ) • x = x := by
  have h : ((5 : ℕ) : ZMod 2) = 1 := by decide
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), h, one_smul]

theorem End_apply_pow_succ (σ : V →ₗ[ZMod 2] V) (i : ℕ) (x : V) :
    σ ((σ ^ i) x) = (σ ^ (i + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]

theorem End_sum_fixed {σ : V →ₗ[ZMod 2] V} (h5 : σ ^ 5 = 1) (x : V) :
    σ (∑ i ∈ Finset.range 5, (σ ^ i) x) = ∑ i ∈ Finset.range 5, (σ ^ i) x := by
  have h5x : (σ ^ 5) x = x := by rw [h5]; rfl
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, map_add,
    End_apply_pow_succ, pow_zero, Module.End.one_apply, h5x]
  simp only [zero_add, pow_one, h5x]
  abel

theorem End_sum_of_fixed {σ : V →ₗ[ZMod 2] V} {x : V} (hx : σ x = x) :
    ∑ i ∈ Finset.range 5, (σ ^ i) x = x := by
  have hpow : ∀ i : ℕ, (σ ^ i) x = x := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← End_apply_pow_succ, ih, hx]
  simp only [hpow, Finset.sum_const, Finset.card_range]
  exact five_nsmul_eq x

theorem End_pow_apply_of_fixed {σ : V →ₗ[ZMod 2] V} {x : V} (hx : σ x = x) (i : ℕ) :
    (σ ^ i) x = x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← End_apply_pow_succ, ih, hx]

variable [Finite V]

theorem cover_lin (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hβ : ∀ w : V, (∀ v, β v w = 0) → w = 0)
    (σ : V →ₗ[ZMod 2] V) (h5 : σ ^ 5 = 1) (hβσ : ∀ x y, β (σ x) (σ y) = β x y)
    (hdim : finrank (ZMod 2) V ≤ 8) {v₀ : V} (hv₀ : v₀ ≠ 0) (hσv₀ : σ v₀ = v₀)
    {d t : V} (hd : σ d ≠ d) (ht : ∀ i : ℕ, β ((σ ^ i) d) t = 1) : σ t = t := by
  classical
  let T : V →ₗ[ZMod 2] V := ∑ i ∈ Finset.range 5, σ ^ i
  have hTapp : ∀ x, T x = ∑ i ∈ Finset.range 5, (σ ^ i) x := fun x => by
    simp [T, LinearMap.sum_apply]
  have hσT : ∀ x, σ (T x) = T x := fun x => by rw [hTapp]; exact End_sum_fixed h5 x
  have hTfix : ∀ x, σ x = x → T x = x := fun x hx => by rw [hTapp]; exact End_sum_of_fixed hx
  have hTT : ∀ x, T (T x) = T x := fun x => hTfix _ (hσT x)
  have hTσ : ∀ x, T (σ x) = T x := by
    intro x
    have h5x : (σ ^ 5) x = x := by rw [h5]; rfl
    have e : ∀ i : ℕ, (σ ^ i) (σ x) = (σ ^ (i + 1)) x := fun i => by
      rw [pow_succ, Module.End.mul_apply]
    rw [hTapp, hTapp]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, e,
      pow_zero, Module.End.one_apply, h5x]
    simp only [zero_add, pow_one, h5x]
    abel
  have hTσpow : ∀ (i : ℕ) x, T ((σ ^ i) x) = T x := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [pow_succ', Module.End.mul_apply, hTσ, ih]
  have hker : ∀ x, T (x - T x) = 0 := fun x => by rw [map_sub, hTT, sub_self]
  have hinv : ∀ (i : ℕ) x y, β ((σ ^ i) x) ((σ ^ i) y) = β x y := by
    intro i
    induction i with
    | zero => intro x y; rfl
    | succ i ih => intro x y; rw [← End_apply_pow_succ, ← End_apply_pow_succ, hβσ, ih]
  have hpowT : ∀ (i : ℕ) x, (σ ^ i) (T x) = T x := fun i x =>
    End_pow_apply_of_fixed (hσT x) i
  have horth : ∀ x v, σ x = x → T v = 0 → β x v = 0 := by
    intro x v hx hv
    have h1 : ∀ i : ℕ, β x ((σ ^ i) v) = β x v := fun i => by
      conv_lhs => rw [← End_pow_apply_of_fixed hx i]
      exact hinv i x v
    have h2 : β x (T v) = ∑ i ∈ Finset.range 5, β x ((σ ^ i) v) := by
      rw [hTapp, map_sum]
    rw [hv, map_zero] at h2
    simp only [h1, Finset.sum_const, Finset.card_range] at h2
    rw [five_nsmul_eq] at h2
    exact h2.symm
  have hdN0 : d - T d ≠ 0 := by
    intro h0
    apply hd
    have h1 : d = T d := sub_eq_zero.mp h0
    exact (congrArg σ h1).trans ((hσT d).trans h1.symm)
  have hG : ∀ i j : ℕ, β ((σ ^ i) d) ((σ ^ j) t) = 1 := by
    intro i j
    have h1 := hinv (4 * j) ((σ ^ i) d) ((σ ^ j) t)
    have e1 : (σ ^ (4 * j)) ((σ ^ i) d) = (σ ^ (4 * j + i)) d := by
      rw [pow_add, Module.End.mul_apply]
    have e2 : (σ ^ (4 * j)) ((σ ^ j) t) = t := by
      rw [← Module.End.mul_apply, ← pow_add]
      have h4 : 4 * j + j = 5 * j := by ring
      rw [h4, pow_mul, h5, one_pow]
      rfl
    rw [e1, e2, ht] at h1
    exact h1.symm
  have hsum1 : ∀ i : ℕ, β ((σ ^ i) d) (T t) = 1 := by
    intro i
    rw [hTapp t, map_sum]
    simp only [hG i]
    decide
  have hsum2 : β (T d) t = 1 := by
    rw [hTapp d]
    simp only [map_sum, LinearMap.sum_apply, ht]
    decide
  have hsum3 : β (T d) (T t) = 1 := by
    rw [hTapp d, hTapp t]
    simp only [map_sum, LinearMap.sum_apply, hG]
    decide
  have hperp : ∀ i : ℕ, β ((σ ^ i) (d - T d)) (t - T t) = 0 := by
    intro i
    have e : (σ ^ i) (d - T d) = (σ ^ i) d - T d := by rw [map_sub, hpowT i d]
    rw [e]
    simp only [map_sub, LinearMap.sub_apply, ht i, hsum1 i, hsum2, hsum3]
    decide
  have hσK : ∀ x ∈ LinearMap.ker T, σ x ∈ LinearMap.ker T := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hTσ]
    exact hx
  have hKfix : ∀ x ∈ LinearMap.ker T, σ x = x → x = 0 := fun x hx hfx => by
    rw [LinearMap.mem_ker] at hx
    rw [← hTfix x hfx]
    exact hx
  have hgenK : ∀ i : ℕ, (σ ^ i) (d - T d) ∈ LinearMap.ker T := fun i => by
    rw [LinearMap.mem_ker, hTσpow]
    exact hker d
  have hMK : Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) (d - T d)) ≤
      LinearMap.ker T :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hgenK i)
  have hM4 := finrank_span_orbit_eq_four σ h5 hdN0 (fun x hx hfx => hKfix x (hMK hx) hfx)
  have hrange : 1 ≤ finrank (ZMod 2) (LinearMap.range T) := by
    have hne : LinearMap.range T ≠ ⊥ := by
      intro h
      apply hv₀
      have hmem : v₀ ∈ LinearMap.range T := ⟨v₀, hTfix v₀ hσv₀⟩
      rw [h] at hmem
      exact (Submodule.mem_bot _).1 hmem
    exact Submodule.one_le_finrank_iff.2 hne
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have h5K : (σ.restrict hσK) ^ 5 = 1 := by
    rw [Module.End.pow_restrict]
    ext x
    rw [LinearMap.coe_restrict_apply]
    exact congrArg (fun f : V →ₗ[ZMod 2] V => f (x : V)) h5
  have hfixK : ∀ x : ↥(LinearMap.ker T), (σ.restrict hσK) x = x → x = 0 := by
    intro x hx
    apply Subtype.ext
    have h1 : ((σ.restrict hσK) x : V) = (x : V) :=
      congrArg (fun y : ↥(LinearMap.ker T) => (y : V)) hx
    rw [LinearMap.coe_restrict_apply hσK x] at h1
    exact hKfix (x : V) x.2 h1
  have h4K := four_dvd_finrank_of_fpf (σ.restrict hσK) h5K hfixK
  have hK4 : finrank (ZMod 2) (LinearMap.ker T) ≤ 4 := by
    obtain ⟨k, hk⟩ := h4K
    omega
  have hMeq : Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) (d - T d)) =
      LinearMap.ker T := Submodule.eq_of_le_of_finrank_le hMK (by omega)
  have hMtN : ∀ m ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) (d - T d)),
      β m (t - T t) = 0 := by
    intro m hm
    refine Submodule.span_induction (p := fun m _ => β m (t - T t) = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨i, rfl⟩
      exact hperp i
    · simp
    · intro x y _ _ hx hy
      rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
    · intro c x _ hx
      rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  have hall : ∀ v, β v (t - T t) = 0 := by
    intro v
    have hv1 : β (T v) (t - T t) = 0 := horth (T v) (t - T t) (hσT v) (hker t)
    have hv2 : β (v - T v) (t - T t) = 0 :=
      hMtN _ (hMeq ▸ (LinearMap.mem_ker.2 (hker v)))
    calc β v (t - T t) = β (T v + (v - T v)) (t - T t) := by rw [add_sub_cancel]
      _ = 0 := by rw [map_add, LinearMap.add_apply, hv1, hv2, add_zero]
  have htN0 : t - T t = 0 := hβ _ hall
  have h1 : t = T t := sub_eq_zero.mp htN0
  exact (congrArg σ h1).trans ((hσT t).trans h1.symm)

end Cover

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
