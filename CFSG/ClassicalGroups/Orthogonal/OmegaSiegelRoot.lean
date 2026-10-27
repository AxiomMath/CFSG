module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open QuadraticMap
open scoped commutatorElement

variable {K : Type*} [Field K] [CharP K 2] {N : Type*} [AddCommGroup N] [Module K N]
  {Q : QuadraticForm K N}

private theorem two_smul_eq_zero_vec (v : N) : (2 : K) • v = 0 := by
  rw [CharTwo.two_eq_zero, zero_smul]

include K in
private theorem neg_eq_vec (v : N) : -v = v := by
  have h : v + v = 0 := by
    rw [← two_smul K v, two_smul_eq_zero_vec]
  exact (eq_neg_of_add_eq_zero_left h).symm

theorem eichler_apply_of_singular {a b : N} (ha : Q a = 0) (hb : Q b = 0)
    (hab : polar Q a b = 0) (x : N) :
    eichler Q a b x = x + polar Q x a • b + polar Q x b • a := by
  rw [eichler_apply ha hab, hb, zero_mul, add_zero, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem eichler_comm_of_singular {a b : N} (ha : Q a = 0) (hb : Q b = 0)
    (hab : polar Q a b = 0) : eichler Q a b = eichler Q b a := by
  have hba : polar Q b a = 0 := by rw [polar_comm, hab]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply_of_singular ha hb hab, eichler_apply_of_singular hb ha hba]
  exact add_right_comm _ _ _

theorem commutatorElement_eichler {a b c d : N} (ha : Q a = 0) (hb : Q b = 0) (hc : Q c = 0)
    (hd : Q d = 0) (hab : polar Q a b = 0) (hcd : polar Q c d = 0) (hac : polar Q a c = 0)
    (had : polar Q a d = 0) (hbd : polar Q b d = 0) :
    ⁅eichler Q a b, eichler Q c d⁆ = eichler Q a (polar Q b c • d) := by
  have hβ : polar Q a (polar Q b c • d) = 0 := by rw [polar_smul_right_eq, had, mul_zero]
  have hQβ : Q (polar Q b c • d) = 0 := by rw [map_smul_eq_sq, hd, mul_zero]
  have hba : polar Q b a = 0 := by rw [polar_comm, hab]
  have hca : polar Q c a = 0 := by rw [polar_comm, hac]
  have hda : polar Q d a = 0 := by rw [polar_comm, had]
  have hdb : polar Q d b = 0 := by rw [polar_comm, hbd]
  have hdc : polar Q d c = 0 := by rw [polar_comm, hcd]
  have hcb : polar Q c b = polar Q b c := polar_comm Q c b
  rw [commutatorElement_def, eichler_inv hab, eichler_inv hcd, neg_eq_vec (K := K) b,
    neg_eq_vec (K := K) d]
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, eichler_apply_of_singular ha hb hab,
    eichler_apply_of_singular hc hd hcd, eichler_apply_of_singular ha hQβ hβ]
  simp only [polar_add_left, polar_smul_left, polar_smul_right, smul_eq_mul,
    polar_self_eq_zero ha, polar_self_eq_zero hb, polar_self_eq_zero hc, polar_self_eq_zero hd,
    hab, hcd, hac, had, hbd, hba, hca, hda, hdb, hdc, hcb, mul_zero, add_zero]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  match_scalars
  all_goals first
    | rfl
    | linear_combination (polar Q x c) * h2
    | linear_combination (polar Q x d) * h2
    | linear_combination (polar Q x a) * h2
    | linear_combination (polar Q x b + polar Q x d * polar Q b c) * h2

theorem eichler_mem_of_forall_singular {u e₂ f₂ : N} {H : Submodule K N} (he₂ : e₂ ∈ H)
    (hf₂ : f₂ ∈ H) (hQe₂ : Q e₂ = 0) (hQf₂ : Q f₂ = 0) (hef₂ : polar Q e₂ f₂ = 1)
    (hHu : ∀ w ∈ H, polar Q u w = 0) {Y : Subgroup (N ≃ₗ[K] N)}
    (hY : ∀ w ∈ H, Q w = 0 → eichler Q u w ∈ Y) {w : N} (hw : w ∈ H) : eichler Q u w ∈ Y := by
  have hfe : polar Q f₂ e₂ = 1 := by rw [polar_comm, hef₂]
  have hff : polar Q f₂ f₂ = 0 := polar_self_eq_zero hQf₂
  have hee : polar Q e₂ e₂ = 0 := polar_self_eq_zero hQe₂
  obtain ⟨α, hα⟩ : ∃ α : K, α = polar Q w f₂ := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : K, β = polar Q w e₂ := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : N, y = w - α • e₂ - β • f₂ := ⟨_, rfl⟩
  have hyH : y ∈ H := by
    rw [hy]
    exact H.sub_mem (H.sub_mem hw (H.smul_mem α he₂)) (H.smul_mem β hf₂)
  have hye : polar Q y e₂ = 0 := by
    rw [hy]
    simp only [polar_sub_left, polar_smul_left, hee, hfe, smul_eq_mul, mul_zero, mul_one,
      sub_zero]
    rw [← hβ]
    ring
  have hyf : polar Q y f₂ = 0 := by
    rw [hy]
    simp only [polar_sub_left, polar_smul_left, hef₂, hff, smul_eq_mul, mul_zero, mul_one,
      sub_zero]
    rw [← hα]
    ring
  obtain ⟨t, ht⟩ : ∃ t : K, t = Q y := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : N, s = y + t • e₂ + f₂ := ⟨_, rfl⟩
  have hsH : s ∈ H := by
    rw [hs]
    exact H.add_mem (H.add_mem hyH (H.smul_mem t he₂)) hf₂
  have hsQ : Q s = 0 := by
    rw [hs, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, hQe₂, polar_add_left,
      polar_smul_right_eq, polar_smul_left_eq, hye, hyf, hef₂, hQf₂, ← ht]
    simp only [mul_zero, mul_one, zero_add, add_zero]
    exact CharTwo.add_self_eq_zero t
  have hdec : (α + t) • e₂ + (β + 1) • f₂ + s = w := by
    have h2e : (2 : K) • e₂ = 0 := two_smul_eq_zero_vec e₂
    have h2f : (2 : K) • f₂ = 0 := two_smul_eq_zero_vec f₂
    rw [hs, hy]
    linear_combination (norm := module) t • h2e + h2f
  have hpol1 : polar Q u ((α + t) • e₂) = 0 := by rw [polar_smul_right_eq, hHu e₂ he₂, mul_zero]
  have hpol2 : polar Q u ((β + 1) • f₂) = 0 := by rw [polar_smul_right_eq, hHu f₂ hf₂, mul_zero]
  have hpols : polar Q u s = 0 := hHu s hsH
  have hv12 : polar Q u ((α + t) • e₂ + (β + 1) • f₂) = 0 := by
    rw [polar_add_right, hpol1, hpol2, add_zero]
  have hQ1 : Q ((α + t) • e₂) = 0 := by rw [map_smul_eq_sq, hQe₂, mul_zero]
  have hQ2 : Q ((β + 1) • f₂) = 0 := by rw [map_smul_eq_sq, hQf₂, mul_zero]
  have m1 : eichler Q u ((α + t) • e₂) ∈ Y := hY _ (H.smul_mem _ he₂) hQ1
  have m2 : eichler Q u ((β + 1) • f₂) ∈ Y := hY _ (H.smul_mem _ hf₂) hQ2
  have m3 : eichler Q u s ∈ Y := hY s hsH hsQ
  have key : eichler Q u w = eichler Q u ((α + t) • e₂) * eichler Q u ((β + 1) • f₂) *
      eichler Q u s := by
    rw [eichler_mul hpol1 hpol2, eichler_mul hv12 hpols, ← hdec]
  rw [key]
  exact Y.mul_mem (Y.mul_mem m1 m2) m3

omit [CharP K 2] in
theorem linearIndependent_pair_of_polar {x y z₁ z₂ : N} (h₁ : polar Q x z₁ ≠ 0)
    (h₂ : polar Q y z₁ = 0) (h₃ : polar Q y z₂ ≠ 0) : LinearIndependent K ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hs : s • polar Q x z₁ = 0 := by
    have h := congrArg (fun v => polar Q v z₁) hst
    simpa [polar_add_left, polar_smul_left, h₂] using h
  have hs0 : s = 0 := (smul_eq_zero.mp hs).resolve_right h₁
  subst hs0
  have ht : t • y = 0 := by simpa using hst
  have ht' : t * polar Q y z₂ = 0 := by
    have h := congrArg (fun v => polar Q v z₂) ht
    simpa [polar_smul_left] using h
  exact ⟨rfl, (mul_eq_zero.mp ht').resolve_right h₃⟩

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
