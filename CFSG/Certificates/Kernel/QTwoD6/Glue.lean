module

public import CFSG.Certificates.Kernel.QTwoD6.Sound
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.QTwoD6.K

open Module CFSG.KC.QTwoD6K CFSG.StandardType.QTwoLin

instance qTwoD6K_fact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem decL_apply (t : Nat) (v : V7) : decL t v = v - decA (aK t) v • decV (hK t) := rfl

theorem eq_reflection_of_code {t : Nat} (h2 : decA (aK t) (decV (hK t)) = 2)
    {ρ : V7 ≃ₗ[ZMod 3] V7} (hρ : (ρ : V7 →ₗ[ZMod 3] V7) = decL t) : ρ = reflection h2 := by
  apply LinearEquiv.ext
  intro v
  have h := LinearMap.congr_fun hρ v
  rw [LinearEquiv.coe_coe] at h
  rw [h, reflection_apply, decL_apply]

theorem not_tvFact {A B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hTV : TransvectionFree A) (hBA : B ≤ A)
    (h : TVFact B) : False := by
  obtain ⟨t₁, t₂, ⟨h₁, ρ₁, hρ₁B, hρ₁⟩, ⟨h₂, ρ₂, hρ₂B, hρ₂⟩, hne, hc⟩ := h
  have e₁ := eq_reflection_of_code h₁ hρ₁
  have e₂ := eq_reflection_of_code h₂ hρ₂
  rcases hc with hc | ⟨μ, hμ⟩
  · have hφ : decA (aK t₁) ≠ decA (aK t₂) := by
      intro hφ
      apply hne
      unfold decL
      rw [hφ, hc]
    have h₂' : decA (aK t₂) (decV (hK t₁)) = 2 := by rw [hc]; exact h₂
    have hT := transvection_of_same_centre h₁ h₂' hφ
    have hr₂ : reflection h₂' = ρ₂ := by
      rw [e₂]
      apply LinearEquiv.ext
      intro v
      rw [reflection_apply, reflection_apply, hc]
    refine hTV _ (A.mul_mem (hBA ?_) (hBA ?_)) hT
    · rw [hr₂]
      exact hρ₂B
    · rw [← e₁]
      exact hρ₁B
  · refine hTV _ (A.mul_mem (hBA hρ₂B) (hBA hρ₁B))
      ⟨μ • decV (hK t₂) - decV (hK t₁), decA (aK t₁), ?_, ?_, ?_, ?_⟩
    · intro h0
      apply hne
      have hu : μ • decV (hK t₂) = decV (hK t₁) := sub_eq_zero.mp h0
      apply LinearMap.ext
      intro v
      rw [decL_apply, decL_apply, hμ, ← hu]
      simp only [LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm]
    · intro h0
      rw [h0, LinearMap.zero_apply] at h₁
      exact absurd h₁ (by decide)
    · have h₂μ : μ * decA (aK t₁) (decV (hK t₂)) = 2 := by
        rw [hμ] at h₂
        simpa using h₂
      rw [map_sub, map_smul, smul_eq_mul, h₂μ, h₁, sub_self]
    · intro v
      rw [LinearEquiv.mul_apply, e₁, e₂, reflection_apply, reflection_apply]
      simp only [hμ, map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul, h₁]
      module

@[expose] noncomputable def monoG : Subgroup (V7 ≃ₗ[ZMod 3] V7) where
  carrier := {g | MonoEps (g : V7 →ₗ[ZMod 3] V7)}
  one_mem' := ⟨1, fun _ => 1, fun _ => one_ne_zero, fun i => by simp⟩
  mul_mem' := by
    rintro a b ⟨σ, s, hs, ha⟩ ⟨τ, t, ht, hb⟩
    refine ⟨τ.trans σ, fun i => t i * s (τ i), fun i => mul_ne_zero (ht i) (hs _), fun i => ?_⟩
    simp only [LinearEquiv.coe_coe] at ha hb ⊢
    rw [LinearEquiv.mul_apply, hb, map_smul, ha, smul_smul]
    rfl
  inv_mem' := by
    rintro a ⟨σ, s, hs, ha⟩
    refine ⟨σ.symm, fun i => (s (σ.symm i))⁻¹, fun i => inv_ne_zero (hs (σ.symm i)), fun i => ?_⟩
    simp only [LinearEquiv.coe_coe] at ha ⊢
    have h1 := ha (σ.symm i)
    rw [Equiv.apply_symm_apply] at h1
    apply a.injective
    change a (a.symm (epsV i)) = a ((s (σ.symm i))⁻¹ • epsV (σ.symm i))
    rw [LinearEquiv.apply_symm_apply, map_smul, h1, smul_smul, inv_mul_cancel₀ (hs _), one_smul]

@[expose] def sAct (j : Fin 6) (v : V7) : V7 :=
  v - (∑ i : Fin 6, ((cartanD6 i j : ℤ) : ZMod 3) * v i.succ) • hvec j

theorem simpleD6_apply_eq (j : Fin 6) (v : V7) : simpleD6 j v = sAct j v := by
  rw [simpleD6, reflection_apply, sAct]
  congr 2

@[expose] def sPerm (j : Fin 6) : Equiv.Perm (Fin 6) :=
  if h : j.val < 4 then Equiv.swap j ⟨j.val + 1, by omega⟩ else Equiv.swap 4 5

@[expose] def sSign (j i : Fin 6) : ZMod 3 := if j = 5 ∧ 4 ≤ i.val then 2 else 1

theorem sAct_eps : ∀ j i : Fin 6, sAct j (epsV i) = sSign j i • epsV (sPerm j i) := by
  decide +kernel

theorem W6_le_monoG : W6 ≤ monoG := by
  rw [W6, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj⟩ := hg
  subst hj
  change MonoEps ((simpleD6 j : V7 ≃ₗ[ZMod 3] V7) : V7 →ₗ[ZMod 3] V7)
  refine ⟨sPerm j, sSign j, fun i => ?_, fun i => ?_⟩
  · unfold sSign
    split_ifs <;> decide
  · rw [LinearEquiv.coe_coe, simpleD6_apply_eq, sAct_eps]

theorem eps_eq_sum : ∀ i : Fin 6, epsV i = ∑ k : Fin 6, epsV i k.succ • hvec k := by
  decide +kernel

@[expose] def swSign (i : Fin 6) : ZMod 3 := if i = 5 then 2 else 1

theorem eps_swap_sum : ∀ i : Fin 6,
    ∑ k : Fin 6, epsV i k.succ • hvec (swapD6 k) = swSign i • epsV i := by
  decide +kernel

theorem monoEps_of_normForm {φ w : V7 ≃ₗ[ZMod 3] V7} (hw : w ∈ W6) {c : ZMod 3} (hc : c ≠ 0)
    {π : Fin 6 ≃ Fin 6} (hπ : π = Equiv.refl _ ∨ π = swapD6)
    (hφ : ∀ i, φ (hvec i) = c • w (hvec (π i))) : MonoEps (φ : V7 →ₗ[ZMod 3] V7) := by
  obtain ⟨σ, s, hs, hws⟩ := W6_le_monoG hw
  simp only [LinearEquiv.coe_coe] at hws
  have key : ∀ i, φ (epsV i) = c • w (∑ k : Fin 6, epsV i k.succ • hvec (π k)) := by
    intro i
    conv_lhs => rw [eps_eq_sum i]
    rw [map_sum, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hφ k, map_smul, smul_comm]
  rcases hπ with rfl | rfl
  · refine ⟨σ, fun i => c * s i, fun i => mul_ne_zero hc (hs i), fun i => ?_⟩
    rw [LinearEquiv.coe_coe, key i]
    simp only [Equiv.refl_apply]
    rw [← eps_eq_sum i, hws, smul_smul]
  · refine ⟨σ, fun i => c * swSign i * s i, fun i => ?_, fun i => ?_⟩
    · refine mul_ne_zero (mul_ne_zero hc ?_) (hs i)
      unfold swSign
      split_ifs <;> decide
    · rw [LinearEquiv.coe_coe, key i, eps_swap_sum i, map_smul, hws, smul_smul, smul_smul]

theorem ub_zero : ub 0 = e0 := by
  decide +kernel

@[expose] def cR : Fin 6 → Fin 6 → ZMod 3 :=
  ![![0, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1], ![1, 1, 0, 1, 1, 1], ![1, 1, 1, 0, 1, 1],
    ![1, 1, 1, 1, 0, 1], ![2, 2, 2, 2, 2, 0]]

@[expose] def dR : Fin 6 → Fin 6 → ZMod 3 :=
  ![![1, 2, 2, 2, 2, 2], ![2, 1, 2, 2, 2, 2], ![2, 2, 1, 2, 2, 2], ![2, 2, 2, 1, 2, 2],
    ![2, 2, 2, 2, 1, 2], ![1, 1, 1, 1, 1, 2]]

theorem ub_succ_eps : ∀ j : Fin 6, ub j.succ = ∑ i : Fin 6, cR i j • epsV i := by
  decide +kernel

theorem eps_ub_sum : ∀ i : Fin 6, epsV i = ∑ j : Fin 6, dR i j • ub j.succ := by
  decide +kernel

theorem eps_mem_uSpan (i : Fin 6) : epsV i ∈ uSpan := by
  rw [eps_ub_sum i]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem apply_decV_eq_zero {f : Dual (ZMod 3) V7} (h0 : f e0 = 0) (he : ∀ i, f (epsV i) = 0)
    (v : Nat) : f (decV v) = 0 := by
  rw [decV, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul]
  induction j using Fin.cases with
  | zero => rw [ub_zero, h0, smul_zero]
  | succ j =>
    rw [ub_succ_eps, map_sum]
    simp only [map_smul, he, smul_zero, Finset.sum_const_zero]

theorem not_hlFact {A B : Subgroup (V7 ≃ₗ[ZMod 3] V7)} (hBA : B ≤ A)
    (hNF : ∀ φ ∈ A, φ e0 ∈ Submodule.span (ZMod 3) {e0} →
      ∃ w ∈ W6, ∃ c : ZMod 3, c ≠ 0 ∧ ∃ π : Fin 6 ≃ Fin 6, (π = Equiv.refl _ ∨ π = swapD6) ∧
        ∀ i, φ (hvec i) = c • w (hvec (π i)))
    (h : HLFact B) : False := by
  obtain ⟨t, ⟨h2, ρ, hρB, hρ⟩, ha0, hcase⟩ := h
  have hρv : ∀ v, ρ v = v - decA (aK t) v • decV (hK t) := fun v => by
    have h := LinearMap.congr_fun hρ v
    rw [LinearEquiv.coe_coe] at h
    rw [h, decL_apply]
  have hρe0 : ρ e0 = e0 := by rw [hρv, ha0, zero_smul, sub_zero]
  obtain ⟨w, hw, c, hc, π, hπ, hφ⟩ :=
    hNF ρ (hBA hρB) (by rw [hρe0]; exact Submodule.mem_span_singleton_self _)
  have hmono := monoEps_of_normForm hw hc hπ hφ
  rcases hcase with hout | hnm
  · apply hout
    obtain ⟨σ, s, -, hs⟩ := hmono
    by_cases hall : ∀ i, decA (aK t) (epsV i) = 0
    · rw [apply_decV_eq_zero ha0 hall] at h2
      exact absurd h2 (by decide)
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have h1 := hs i
      rw [LinearEquiv.coe_coe, hρv] at h1
      have hh : decV (hK t) = (decA (aK t) (epsV i))⁻¹ • (epsV i - s i • epsV (σ i)) := by
        rw [← h1, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hi, one_smul]
      rw [hh]
      exact Submodule.smul_mem _ _
        (Submodule.sub_mem _ (eps_mem_uSpan i) (Submodule.smul_mem _ _ (eps_mem_uSpan _)))
  · apply hnm
    rw [← hρ]
    exact hmono

end CFSG.StandardType.QTwoD6.K

end
