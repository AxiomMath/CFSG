module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private lemma act_eq_of_mem_adjoin {γ δ p : V →ₗ[ZMod 2] V}
    (hcomm : Commute δ γ) (hp : Commute γ p) {u : V} (hpu : p u = δ u) :
    ∀ w ∈ Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u),
      δ w = p w := by
  intro w hw
  have hgen : ∀ j : Fin 5, δ ((γ ^ (j : ℕ)) u) = p ((γ ^ (j : ℕ)) u) := by
    intro j
    calc δ ((γ ^ (j : ℕ)) u)
        = (δ * γ ^ (j : ℕ)) u := by rw [Module.End.mul_apply]
      _ = (γ ^ (j : ℕ) * δ) u := by rw [(hcomm.pow_right (j : ℕ)).eq]
      _ = (γ ^ (j : ℕ)) (δ u) := by rw [Module.End.mul_apply]
      _ = (γ ^ (j : ℕ)) (p u) := by rw [hpu]
      _ = (γ ^ (j : ℕ) * p) u := by rw [Module.End.mul_apply]
      _ = (p * γ ^ (j : ℕ)) u := by rw [(hp.pow_left (j : ℕ)).eq]
      _ = p ((γ ^ (j : ℕ)) u) := by rw [Module.End.mul_apply]
  have hle : Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u) ≤
      LinearMap.ker (δ - p) := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    change (δ - p) ((γ ^ (j : ℕ)) u) = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact hgen j
  have hmem := hle hw
  change (δ - p) w = 0 at hmem
  rw [LinearMap.sub_apply, sub_eq_zero] at hmem
  exact hmem

theorem commute_on_of_fixedFree (γ δ₁ δ₂ : V →ₗ[ZMod 2] V) (h : γ ^ 5 = 1)
    (hc₁ : δ₁ * γ = γ * δ₁) (hc₂ : δ₂ * γ = γ * δ₂) (U : Submodule (ZMod 2) V)
    (hU : ∀ u ∈ U, γ u ∈ U) (hU₁ : ∀ u ∈ U, δ₁ u ∈ U) (hU₂ : ∀ u ∈ U, δ₂ u ∈ U)
    (hfix : ∀ u ∈ U, γ u = u → u = 0) (h4 : finrank (ZMod 2) U = 4) :
    ∀ u ∈ U, δ₁ (δ₂ u) = δ₂ (δ₁ u) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0
    simp
  let W : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range fun i : Fin 5 => (γ ^ (i : ℕ)) u)
  have hpowU : ∀ n : ℕ, (γ ^ n) u ∈ U := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hU _ ih
  have huW : u ∈ W := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp
  have hWU : W ≤ U := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hpowU (i : ℕ)
  have hWγ : ∀ w ∈ W, γ w ∈ W := by
    have hle : W ≤ Submodule.comap γ W := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      change γ ((γ ^ (i : ℕ)) u) ∈ W
      have hstep : γ ((γ ^ (i : ℕ)) u) = (γ ^ ((i : ℕ) + 1)) u := by
        rw [pow_succ', Module.End.mul_apply]
      rw [hstep]
      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hlt | heq
      · exact Submodule.subset_span ⟨⟨(i : ℕ) + 1, hlt⟩, by simp⟩
      · have huv : (γ ^ ((i : ℕ) + 1)) u = u := by
          rw [show (i : ℕ) + 1 = 5 from heq, h, Module.End.one_apply]
        exact Submodule.subset_span ⟨0, by simpa using huv.symm⟩
    intro w hw
    exact hle hw
  have hWfix : ∀ w ∈ W, γ w = w → w = 0 := fun w hw => hfix w (hWU hw)
  have hW4 : finrank (ZMod 2) W = 4 := by
    have hdvd : 4 ∣ finrank (ZMod 2) W := four_dvd_finrank_of_fixedFree γ h W hWγ hWfix
    have hpos : 0 < finrank (ZMod 2) W := by
      rw [Nat.pos_iff_ne_zero]
      intro hz
      have hbot : W = ⊥ := (Submodule.finrank_eq_zero).1 hz
      have : u ∈ (⊥ : Submodule (ZMod 2) V) := hbot ▸ huW
      exact hu0 (by simpa using this)
    have hle4 : finrank (ZMod 2) W ≤ 4 := by
      rw [← h4]
      exact Submodule.finrank_mono hWU
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  have hWUeq : W = U :=
    Submodule.eq_of_le_of_finrank_eq (K := ZMod 2) (S₁ := W) (S₂ := U) hWU (by rw [hW4, h4])
  have hpoly : ∀ c : Fin 5 → ZMod 2,
      (∑ i : Fin 5, c i • (γ ^ (i : ℕ))) ∈
        Algebra.adjoin (ZMod 2) ({γ} : Set (Module.End (ZMod 2) V)) := by
    intro c
    refine Subalgebra.sum_mem
      (Algebra.adjoin (ZMod 2) ({γ} : Set (Module.End (ZMod 2) V))) (fun i _ => ?_)
    exact Subalgebra.smul_mem _
      (Subalgebra.pow_mem _
        (Algebra.subset_adjoin (Set.mem_singleton γ)) (i : ℕ)) (c i)
  have hδ₁uW : δ₁ u ∈ W := by rw [hWUeq]; exact hU₁ u hu
  obtain ⟨c₁, hc₁'⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hδ₁uW
  have hδ₂uW : δ₂ u ∈ W := by rw [hWUeq]; exact hU₂ u hu
  obtain ⟨c₂, hc₂'⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hδ₂uW
  set p₁ : Module.End (ZMod 2) V := ∑ i : Fin 5, c₁ i • (γ ^ (i : ℕ)) with hp₁def
  set p₂ : Module.End (ZMod 2) V := ∑ i : Fin 5, c₂ i • (γ ^ (i : ℕ)) with hp₂def
  have hp₁mem : p₁ ∈ Algebra.adjoin (ZMod 2) ({γ} : Set (Module.End (ZMod 2) V)) := by
    rw [hp₁def]; exact hpoly c₁
  have hp₂mem : p₂ ∈ Algebra.adjoin (ZMod 2) ({γ} : Set (Module.End (ZMod 2) V)) := by
    rw [hp₂def]; exact hpoly c₂
  have hp₁u : p₁ u = δ₁ u := by
    rw [hp₁def]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hc₁'
  have hp₂u : p₂ u = δ₂ u := by
    rw [hp₂def]
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hc₂'
  have hact₁ : ∀ w ∈ W, δ₁ w = p₁ w :=
    act_eq_of_mem_adjoin hc₁ (Algebra.commute_of_mem_adjoin_self hp₁mem) hp₁u
  have hact₂ : ∀ w ∈ W, δ₂ w = p₂ w :=
    act_eq_of_mem_adjoin hc₂ (Algebra.commute_of_mem_adjoin_self hp₂mem) hp₂u
  have hp₁₂ : p₁ * p₂ = p₂ * p₁ :=
    (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hp₂mem (by
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (Algebra.commute_of_mem_adjoin_self hp₁mem).symm)).eq
  have hδ₁δ₂ : ∀ w ∈ W, δ₁ (δ₂ w) = (p₁ * p₂) w := by
    intro w hw
    have hwU : w ∈ U := hWU hw
    have hδ₂wW : δ₂ w ∈ W := by rw [hWUeq]; exact hU₂ w hwU
    have hp₂wW : p₂ w ∈ W := by rw [← hact₂ w hw]; exact hδ₂wW
    rw [hact₂ w hw, hact₁ (p₂ w) hp₂wW, Module.End.mul_apply]
  have hδ₂δ₁ : ∀ w ∈ W, δ₂ (δ₁ w) = (p₂ * p₁) w := by
    intro w hw
    have hwU : w ∈ U := hWU hw
    have hδ₁wW : δ₁ w ∈ W := by rw [hWUeq]; exact hU₁ w hwU
    have hp₁wW : p₁ w ∈ W := by rw [← hact₁ w hw]; exact hδ₁wW
    rw [hact₁ w hw, hact₂ (p₁ w) hp₁wW, Module.End.mul_apply]
  calc δ₁ (δ₂ u) = (p₁ * p₂) u := hδ₁δ₂ u huW
    _ = (p₂ * p₁) u := by rw [hp₁₂]
    _ = δ₂ (δ₁ u) := (hδ₂δ₁ u huW).symm

theorem eq_self_of_conj_inv (γ δ ν : V →ₗ[ZMod 2] V) (hγ : γ ^ 5 = 1) (hδ : δ ^ 5 = 1)
    (hγδ : δ * γ = γ * δ) (hνγ : ν * γ = γ * ν) (hνδ : ν * δ = δ ^ 4 * ν)
    (hν : Function.Injective ν) (U : Submodule (ZMod 2) V)
    (hUγ : ∀ u ∈ U, γ u ∈ U) (hUδ : ∀ u ∈ U, δ u ∈ U) (hUν : ∀ u ∈ U, ν u ∈ U)
    (hfix : ∀ u ∈ U, γ u = u → u = 0) (h4 : finrank (ZMod 2) U = 4) :
    ∀ u ∈ U, δ u = u := by
  have hcomm : ∀ u ∈ U, δ (ν u) = ν (δ u) :=
    commute_on_of_fixedFree γ δ ν hγ hγδ hνγ U hUγ hUδ hUν hfix h4
  intro u hu
  let νU : U → U := fun x => ⟨ν x, hUν x x.2⟩
  have hνUinj : Function.Injective νU := by
    intro x y hxy
    apply Subtype.ext
    exact hν (by simpa [νU] using congrArg Subtype.val hxy)
  have hνUsurj : Function.Surjective νU := Finite.surjective_of_injective hνUinj
  obtain ⟨u', hu'⟩ := hνUsurj ⟨u, hu⟩
  have hνu' : ν u'.1 = u := by
    have := congrArg Subtype.val hu'
    simpa [νU] using this
  have h1 : δ u = (δ ^ 4) u := by
    calc δ u = δ (ν u'.1) := by rw [hνu']
      _ = ν (δ u'.1) := hcomm u'.1 u'.2
      _ = (δ ^ 4) (ν u'.1) := by
            have h := congrArg (fun f : Module.End (ZMod 2) V => f u'.1) hνδ
            simpa [Module.End.mul_apply] using h
      _ = (δ ^ 4) u := by rw [hνu']
  have h1' : (δ ^ 4) (δ u) = (δ ^ 4) ((δ ^ 4) u) := congrArg (fun x => (δ ^ 4) x) h1
  have hL : (δ ^ 4) (δ u) = u := by
    rw [← Module.End.mul_apply, ← pow_succ, hδ, Module.End.one_apply]
  have hδ8 : (δ ^ 4) * (δ ^ 4) = δ ^ 3 := by
    rw [← pow_add, show (4 + 4 : ℕ) = 3 + 5 from rfl, pow_add, hδ, mul_one]
  have hR : (δ ^ 4) ((δ ^ 4) u) = (δ ^ 3) u := by
    rw [← Module.End.mul_apply, hδ8]
  have h3 : u = (δ ^ 3) u := by
    rw [hL, hR] at h1'
    exact h1'
  have hδ5' : (δ ^ 5) = (δ ^ 2) * (δ ^ 3) := by
    rw [show (5 : ℕ) = 2 + 3 from rfl, pow_add]
  have h2 : (δ ^ 2) u = u := by
    have hw5 : (δ ^ 5) u = u := by rw [hδ, Module.End.one_apply]
    rw [hδ5', Module.End.mul_apply, ← h3] at hw5
    exact hw5
  have hδ3' : (δ ^ 3) = δ * (δ ^ 2) := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
  calc δ u = δ ((δ ^ 2) u) := by rw [h2]
    _ = (δ * (δ ^ 2)) u := by rw [Module.End.mul_apply]
    _ = (δ ^ 3) u := by rw [← hδ3']
    _ = u := by rw [← h3]

end CFSG.EvenSporadicStandard.HNRecog.Fpf
