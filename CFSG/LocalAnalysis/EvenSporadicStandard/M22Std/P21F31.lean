module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Cyc
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21FieldB

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem restrict_pow_apply (f : V →ₗ[ZMod 2] V) {S : Submodule (ZMod 2) V}
    (hS : ∀ s ∈ S, f s ∈ S) (n : ℕ) (v : S) :
    (((f.restrict hS) ^ n) v : V) = (f ^ n) v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ih]
    rfl

theorem pow_mem_of_inv (f : V →ₗ[ZMod 2] V) {S : Submodule (ZMod 2) V}
    (hS : ∀ s ∈ S, f s ∈ S) (n : ℕ) {s : V} (hs : s ∈ S) : (f ^ n) s ∈ S := by
  induction n generalizing s with
  | zero => simpa using hs
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (hS s hs)

theorem not_inv_conj_gen {ℓ e : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) (he : Odd e)
    (hdim : finrank (ZMod 2) V < 2 * e)
    (hunique : ∀ e' : ℕ, 1 ≤ e' → ℓ ∣ 2 ^ e' - 1 → e' ≤ finrank (ZMod 2) V → e' = e)
    (f t t' : Module.End (ZMod 2) V) (hf : f ^ ℓ = 1) (hf1 : f ≠ 1) (htt' : t * t' = 1)
    (ht't : t' * t = 1) (hconj : t * f = f ^ (ℓ - 1) * t) : False := by
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨S, hS, hSne, hSr, hmin, hirr, hne', hdvd⟩ := exists_cyclic_subspace f hℓ hodd hf hf1
  have hpos : 0 < finrank (ZMod 2) S := by
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hSne
    exact Module.finrank_pos
  have he1 : finrank (ZMod 2) S = e :=
    hunique _ hpos hdvd (Submodule.finrank_le S)
  have hfℓ : f * f ^ (ℓ - 1) = 1 := by
    rw [← pow_succ', show ℓ - 1 + 1 = ℓ by omega, hf]
  have hft : f * t = t * f ^ (ℓ - 1) := by
    calc f * t = f * t * (f * f ^ (ℓ - 1)) := by rw [hfℓ, mul_one]
      _ = f * (t * f) * f ^ (ℓ - 1) := by simp only [mul_assoc]
      _ = f * (f ^ (ℓ - 1) * t) * f ^ (ℓ - 1) := by rw [hconj]
      _ = (f * f ^ (ℓ - 1)) * t * f ^ (ℓ - 1) := by simp only [mul_assoc]
      _ = t * f ^ (ℓ - 1) := by rw [hfℓ, one_mul]
  have htinj : Function.Injective t := by
    intro a b hab
    have := congrArg t' hab
    simpa [← Module.End.mul_apply, ht't] using this
  set S' := S.map t with hS'
  have hS'inv : ∀ w ∈ S', f w ∈ S' := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(f ^ (ℓ - 1)) s, pow_mem_of_inv f hS _ hs, ?_⟩
    have := congrArg (fun T => T s) hft
    simpa using this.symm
  have hfin : finrank (ZMod 2) S' = finrank (ZMod 2) S :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective t htinj S)).symm
  have hSS' : S = S' := by
    by_cases h : S ⊓ S' = ⊥
    · exfalso
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq S S'
      rw [h, finrank_bot, add_zero, hfin, he1] at h1
      have h2 : finrank (ZMod 2) ↥(S ⊔ S') ≤ finrank (ZMod 2) V := Submodule.finrank_le _
      omega
    · have hinf : S ⊓ S' ≤ S := inf_le_left
      have hinv : Inv f (S ⊓ S') := fun w hw =>
        Submodule.mem_inf.2 ⟨hS w hw.1, hS'inv w hw.2⟩
      rcases hmin _ hinf hinv with h0 | h0
      · exact absurd h0 h
      · have hle : S ≤ S' := h0 ▸ inf_le_right
        exact Submodule.eq_of_le_of_finrank_le hle (by rw [hfin])
  have hSt : ∀ s ∈ S, t s ∈ S := fun s hs => hSS' ▸ Submodule.mem_map_of_mem hs
  have hSt' : ∀ s ∈ S, t' s ∈ S := by
    intro s hs
    have : s ∈ S' := hSS' ▸ hs
    obtain ⟨s₁, hs₁, rfl⟩ := this
    have := congrArg (fun T => T s₁) ht't
    simp only [Module.End.mul_apply, Module.End.one_apply] at this
    rw [this]
    exact hs₁
  let τ : S ≃ₗ[ZMod 2] S := LinearEquiv.ofLinearMap (t.restrict hSt) (t'.restrict hSt')
    (by
      ext v
      have := congrArg (fun T => T (v : V)) htt'
      simpa [LinearMap.coe_restrict_apply] using this)
    (by
      ext v
      have := congrArg (fun T => T (v : V)) ht't
      simpa [LinearMap.coe_restrict_apply] using this)
  have hgℓ : (f.restrict hS) ^ ℓ = 1 := by
    ext v
    rw [restrict_pow_apply, hf]
    rfl
  have hτapp : ∀ v : S, ((τ v : S) : V) = t (v : V) := fun v => rfl
  have hτ : τ.toLinearMap * f.restrict hS = (f.restrict hS) ^ (ℓ - 1) * τ.toLinearMap := by
    ext v
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [restrict_pow_apply, hτapp, hτapp, LinearMap.coe_restrict_apply]
    have h1 := congrArg (fun T => T (v : V)) hconj
    simpa only [Module.End.mul_apply] using h1
  exact not_inv_conj hirr (he1 ▸ he) hℓ hodd hgℓ hne' τ hτ

theorem not_inv_conj_31 (hdim : finrank (ZMod 2) V ≤ 8) (f t t' : Module.End (ZMod 2) V)
    (hf : f ^ 31 = 1) (hf1 : f ≠ 1) (htt' : t * t' = 1) (ht't : t' * t = 1)
    (hconj : t * f = f ^ 30 * t) : False := by
  refine not_inv_conj_gen (ℓ := 31) (e := 5) (by norm_num) (by decide) (by decide)
    (by omega) ?_ f t t' hf hf1 htt' ht't (by simpa using hconj)
  intro e' h1 hd hle
  have h8 : e' ≤ 8 := hle.trans hdim
  interval_cases e' <;> first | rfl | (exfalso; revert hd; decide)

end CFSG.EvenSporadicStandard.M22Std.P21Field
