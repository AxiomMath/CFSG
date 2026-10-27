module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Module

private theorem four_dvd_of_two_pow_modEq_one {n : ℕ} (h : 2 ^ n ≡ 1 [MOD 5]) : 4 ∣ n := by
  have hz : (2 : ZMod 5) ^ n = 1 := by
    have h' : ((2 ^ n : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact h
    simpa [Nat.cast_pow] using h'
  have hord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, fun m hm hm0 => by interval_cases m <;> decide⟩
  have hdvd := orderOf_dvd_iff_pow_eq_one.mpr hz
  rwa [hord] at hdvd

private theorem orbit_span_stable {K W : Type*} [CommRing K] [AddCommGroup W] [Module K W]
    (σ : W →ₗ[K] W) (u : W) :
    ∀ y ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u),
      σ y ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u) := by
  intro y hy
  refine Submodule.span_induction
    (p := fun y _ => σ y ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u)) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨i, rfl⟩
    refine Submodule.subset_span ⟨i + 1, ?_⟩
    simp only [pow_succ', Module.End.mul_apply]
  · simpa using Submodule.zero_mem (Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u))
  · intro z w _ _ hz hw
    rw [map_add]
    exact Submodule.add_mem _ hz hw
  · intro a z _ hz
    rw [map_smul]
    exact Submodule.smul_mem _ a hz

private theorem exists_polynomial_of_mem_span_orbit {K W : Type*} [CommRing K] [AddCommGroup W]
    [Module K W] (σ : W →ₗ[K] W) (u : W)
    {y : W} (hy : y ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u)) :
    ∃ p : Polynomial K, (Polynomial.aeval σ p) u = y := by
  refine Submodule.span_induction
    (p := fun y _ => ∃ p : Polynomial K, (Polynomial.aeval σ p) u = y) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨i, rfl⟩
    exact ⟨Polynomial.X ^ i, by rw [Polynomial.aeval_X_pow]⟩
  · exact ⟨0, by simp⟩
  · rintro z w _ _ ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p + q, by rw [Polynomial.aeval_add, LinearMap.add_apply, hp, hq]⟩
  · rintro a z _ ⟨p, hp⟩
    refine ⟨Polynomial.C a * p, ?_⟩
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Module.End.mul_apply, hp]
    rfl

theorem four_dvd_finrank_of_fpf {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : W →ₗ[ZMod 2] W) (h5 : σ ^ 5 = 1) (hfix : ∀ x : W, σ x = x → x = 0) :
    4 ∣ Module.finrank (ZMod 2) W := by
  classical
  letI := Fintype.ofFinite W
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let f : Function.End W := fun x => σ x
  have hf : f ^ 5 ^ 1 = 1 := by
    change (fun x : W => σ x) ^[5] = id
    have h := Module.End.coe_pow σ 5
    rw [h5] at h
    rw [← h]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf
  have hcardfix : Fintype.card ↑(Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, ?_⟩, fun b => ?_⟩
    · exact map_zero σ
    · apply Subtype.ext
      exact hfix (b : W) b.2
  rw [hcardfix] at hmod
  have hpow : 2 ^ Module.finrank (ZMod 2) W ≡ 1 [MOD 5] := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [ZMod.card] at hc
    rw [hc] at hmod
    exact hmod
  exact four_dvd_of_two_pow_modEq_one hpow

theorem finrank_span_orbit_eq_four {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : W →ₗ[ZMod 2] W) (h5 : σ ^ 5 = 1) {u : W} (hu : u ≠ 0)
    (hfix : ∀ x ∈ Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u),
      σ x = x → x = 0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let M : Submodule (ZMod 2) W := Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u)
  have hgen : ∀ i : ℕ, (σ ^ i) u ∈ M := fun i => Submodule.subset_span ⟨i, rfl⟩
  have huM : u ∈ M := by simpa using hgen 0
  have hσM : ∀ x ∈ M, σ x ∈ M := fun x hx => orbit_span_stable σ u x hx
  let e : W := (σ ^ 0) u + (σ ^ 1) u + (σ ^ 2) u + (σ ^ 3) u + (σ ^ 4) u
  have heM : e ∈ M := by
    have heq : e = ∑ i ∈ Finset.range 5, (σ ^ i) u := by
      simp [e, Finset.sum_range_succ]
    rw [heq]
    exact M.sum_mem (fun i _ => hgen i)
  have h5u : (σ ^ 5) u = u := by
    rw [h5]
    rfl
  have hs : ∀ i : ℕ, σ ((σ ^ i) u) = (σ ^ (i + 1)) u := fun i => by
    rw [pow_succ', Module.End.mul_apply]
  have hσe : σ e = e := by
    have hsimp : σ e = (σ ^ 1) u + (σ ^ 2) u + (σ ^ 3) u + (σ ^ 4) u + (σ ^ 5) u := by
      simp only [e, map_add, hs]
    rw [hsimp, h5u]
    simp only [e, pow_zero, Module.End.one_apply]
    abel
  have he0 : e = 0 := hfix e heM hσe
  have h4 : (σ ^ 4) u = -((σ ^ 0) u + (σ ^ 1) u + (σ ^ 2) u + (σ ^ 3) u) := by
    have h := he0
    simp only [e] at h
    refine eq_neg_iff_add_eq_zero.mpr ?_
    rw [add_comm]
    exact h
  let b : Fin 4 → W := fun k => (σ ^ (k : ℕ)) u
  let N : Submodule (ZMod 2) W := Submodule.span (ZMod 2) (Set.range b)
  have hN : ∀ k : Fin 4, b k ∈ N := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hmemN : ∀ i : ℕ, (σ ^ i) u ∈ N := by
    intro i
    refine Nat.strong_induction_on i ?_
    intro j ih
    rcases lt_or_ge j 5 with hj | hj
    · interval_cases j
      · exact hN ⟨0, by norm_num⟩
      · exact hN ⟨1, by norm_num⟩
      · exact hN ⟨2, by norm_num⟩
      · exact hN ⟨3, by norm_num⟩
      · rw [h4]
        exact N.neg_mem (N.add_mem (N.add_mem (N.add_mem (hN ⟨0, by norm_num⟩)
          (hN ⟨1, by norm_num⟩)) (hN ⟨2, by norm_num⟩)) (hN ⟨3, by norm_num⟩))
    · have hj5 : j = 5 + (j - 5) := by omega
      have hred : (σ ^ j) u = (σ ^ (j - 5)) u := by
        rw [hj5, pow_add, h5, one_mul, Nat.add_sub_cancel_left]
      rw [hred]
      exact ih (j - 5) (by omega)
  have hMN : M ≤ N := by
    change Submodule.span (ZMod 2) (Set.range fun i : ℕ => (σ ^ i) u) ≤ N
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemN i
  have hNM : N ≤ M := by
    change Submodule.span (ZMod 2) (Set.range b) ≤ M
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hgen (k : ℕ)
  have hMN_eq : M = N := le_antisymm hMN hNM
  haveI : Module.Finite (ZMod 2) ↥N := by
    change Module.Finite (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range b))
    exact Module.Finite.span_of_finite (ZMod 2) (Set.finite_range b)
  have hfinN_le : Module.finrank (ZMod 2) ↥N ≤ 4 := by
    have h := finrank_range_le_card (R := ZMod 2) b
    simpa only [Set.finrank, N, Fintype.card_fin] using h
  have hspan_le_N : Submodule.span (ZMod 2) ({u} : Set W) ≤ N := by
    rw [Submodule.span_le]
    rintro x (rfl : x = u)
    exact hMN_eq ▸ huM
  have hfinN_ge : 1 ≤ Module.finrank (ZMod 2) ↥N := by
    have h1 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({u} : Set W)) = 1 :=
      finrank_span_singleton hu
    have h2 := Submodule.finrank_mono hspan_le_N
    rwa [h1] at h2
  have hσN : ∀ y ∈ N, σ y ∈ N := fun y hy => hMN (hσM y (hNM hy))
  have h5N : (σ.restrict hσN) ^ 5 = 1 := by
    rw [Module.End.pow_restrict]
    ext x
    rw [LinearMap.coe_restrict_apply]
    exact congrArg (fun f : W →ₗ[ZMod 2] W => f (x : W)) h5
  have hfixN : ∀ x : ↥N, (σ.restrict hσN) x = x → x = 0 := by
    intro x hx
    apply Subtype.ext
    have h1 : ((σ.restrict hσN) x : W) = (x : W) := congrArg (fun y : ↥N => (y : W)) hx
    rw [LinearMap.coe_restrict_apply hσN x] at h1
    exact hfix (x : W) (hNM x.2) h1
  have h4dvdN : 4 ∣ Module.finrank (ZMod 2) ↥N :=
    four_dvd_finrank_of_fpf (σ.restrict hσN) h5N hfixN
  have hfinN : Module.finrank (ZMod 2) ↥N = 4 := by
    obtain ⟨k, hk⟩ := h4dvdN
    omega
  change Module.finrank (ZMod 2) ↥M = 4
  rw [hMN_eq]
  exact hfinN

theorem commute_on_orbit_span {K W : Type*} [CommRing K] [AddCommGroup W] [Module K W]
    (σ g h : W →ₗ[K] W) (hg : ∀ x, g (σ x) = σ (g x)) (hh : ∀ x, h (σ x) = σ (h x)) (u : W)
    (hgu : g u ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u))
    (hhu : h u ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u))
    {x : W} (hx : x ∈ Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u)) :
    g (h x) = h (g x) := by
  classical
  let M : Submodule K W := Submodule.span K (Set.range fun i : ℕ => (σ ^ i) u)
  obtain ⟨pg, hpg⟩ := exists_polynomial_of_mem_span_orbit σ u hgu
  obtain ⟨ph, hph⟩ := exists_polynomial_of_mem_span_orbit σ u hhu
  have hMstab : ∀ y ∈ M, σ y ∈ M := fun y hy => orbit_span_stable σ u y hy
  have hMpow : ∀ (i : ℕ) {y : W}, y ∈ M → (σ ^ i) y ∈ M := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih =>
        intro y hy
        rw [pow_succ', Module.End.mul_apply]
        exact hMstab _ (ih hy)
  have preserve : ∀ (φ : W →ₗ[K] W), (∀ y, φ (σ y) = σ (φ y)) → φ u ∈ M →
      ∀ y ∈ M, φ y ∈ M := by
    intro φ hφ hφu y hy
    refine Submodule.span_induction (p := fun y _ => φ y ∈ M) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩
      have hcomm : Commute φ σ :=
        LinearMap.ext fun y => by simpa [Module.End.mul_apply] using hφ y
      have hci : φ ((σ ^ i) u) = (σ ^ i) (φ u) := by
        have h := congrArg (fun f : W →ₗ[K] W => f u) (hcomm.pow_right i)
        simpa [Module.End.mul_apply] using h
      rw [hci]
      exact hMpow i hφu
    · simpa using Submodule.zero_mem M
    · intro z w _ _ hz hw
      rw [map_add]
      exact Submodule.add_mem _ hz hw
    · intro a z _ hz
      rw [map_smul]
      exact Submodule.smul_mem _ a hz
  have key : ∀ (φ : W →ₗ[K] W) (p : Polynomial K), (∀ y, φ (σ y) = σ (φ y)) →
      φ u = (Polynomial.aeval σ p) u →
      ∀ y ∈ M, φ y = (Polynomial.aeval σ p) y := by
    intro φ p hφ hp y hy
    refine Submodule.span_induction (p := fun y _ => φ y = (Polynomial.aeval σ p) y)
      ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩
      have hcomm : Commute φ σ :=
        LinearMap.ext fun y => by simpa [Module.End.mul_apply] using hφ y
      have h1 : φ ((σ ^ i) u) = (σ ^ i) (φ u) := by
        have h := congrArg (fun f : W →ₗ[K] W => f u) (hcomm.pow_right i)
        simpa [Module.End.mul_apply] using h
      have h2 : (Polynomial.aeval σ p) ((σ ^ i) u) = (σ ^ i) ((Polynomial.aeval σ p) u) := by
        have hcomm2 : Commute (Polynomial.aeval σ p) (σ ^ i) := by
          have hXi : σ ^ i = Polynomial.aeval σ ((Polynomial.X : Polynomial K) ^ i) :=
            (Polynomial.aeval_X_pow σ).symm
          rw [hXi]
          show Polynomial.aeval σ p * Polynomial.aeval σ ((Polynomial.X : Polynomial K) ^ i) =
            Polynomial.aeval σ ((Polynomial.X : Polynomial K) ^ i) * Polynomial.aeval σ p
          rw [← Polynomial.aeval_mul, ← Polynomial.aeval_mul,
            mul_comm p ((Polynomial.X : Polynomial K) ^ i)]
        have h := congrArg (fun f : W →ₗ[K] W => f u) hcomm2
        simpa [Module.End.mul_apply] using h
      rw [h1, h2, hp]
    · simp
    · intro z w _ _ hz hw
      rw [map_add, map_add, hz, hw]
    · intro a z _ hz
      rw [map_smul, map_smul, hz]
  have hgM : ∀ y ∈ M, g y ∈ M := preserve g (fun y => hg y) hgu
  have hhM : ∀ y ∈ M, h y ∈ M := preserve h (fun y => hh y) hhu
  have keyg := key g pg (fun y => hg y) hpg.symm
  have keyh := key h ph (fun y => hh y) hph.symm
  have hcomm_poly : (Polynomial.aeval σ pg) ((Polynomial.aeval σ ph) x) =
      (Polynomial.aeval σ ph) ((Polynomial.aeval σ pg) x) := by
    have hcomm : Commute (Polynomial.aeval σ pg) (Polynomial.aeval σ ph) := by
      show Polynomial.aeval σ pg * Polynomial.aeval σ ph =
        Polynomial.aeval σ ph * Polynomial.aeval σ pg
      rw [← Polynomial.aeval_mul, ← Polynomial.aeval_mul, mul_comm pg ph]
    have h := congrArg (fun f : W →ₗ[K] W => f x) hcomm
    simpa [Module.End.mul_apply] using h
  calc
    g (h x) = (Polynomial.aeval σ pg) (h x) := keyg (h x) (hhM x hx)
    _ = (Polynomial.aeval σ pg) ((Polynomial.aeval σ ph) x) := by rw [keyh x hx]
    _ = (Polynomial.aeval σ ph) ((Polynomial.aeval σ pg) x) := hcomm_poly
    _ = (Polynomial.aeval σ ph) (g x) := by rw [keyg x hx]
    _ = h (g x) := (keyh (g x) (hgM x hx)).symm

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
