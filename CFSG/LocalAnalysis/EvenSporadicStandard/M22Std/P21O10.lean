module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21F31
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem sub_mem_of_finrank_le {f : V →ₗ[ZMod 2] V} {ℓ : ℕ} (hℓ : 0 < ℓ) (hf : f ^ ℓ = 1)
    {S : Submodule (ZMod 2) V} (hS : Inv f S)
    (hdim : finrank (ZMod 2) V ≤ finrank (ZMod 2) S + 1) (v : V) : f v - v ∈ S := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  by_cases hv : v ∈ S
  · exact S.sub_mem (hS v hv) hv
  · have hv0 : v ≠ 0 := fun h => hv (h ▸ S.zero_mem)
    have hdisj : Disjoint S (Submodule.span (ZMod 2) {v}) :=
      (Submodule.disjoint_span_singleton' hv0).2 hv
    have hP : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 := finrank_span_singleton hv0
    have hsup : S ⊔ Submodule.span (ZMod 2) {v} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span (ZMod 2) {v})
      rw [hdisj.eq_bot, finrank_bot, add_zero, hP] at h1
      have h2 := Submodule.finrank_le (S ⊔ Submodule.span (ZMod 2) {v})
      omega
    have hfv : f v ∈ S ⊔ Submodule.span (ZMod 2) {v} := hsup ▸ Submodule.mem_top
    obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.1 hfv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hc : c = 0 ∨ c = 1 := by
      have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact this c
    rcases hc with rfl | rfl
    · exfalso
      apply hv
      have h0 : f v = s := by simpa using hsw.symm
      have : v = (f ^ ℓ) v := by rw [hf]; rfl
      rw [this, show ℓ = (ℓ - 1) + 1 by omega, pow_succ, Module.End.mul_apply, h0]
      exact pow_mem_of_inv f hS _ hs
    · have h1 : f v = s + v := by simpa using hsw.symm
      rw [h1, add_sub_cancel_right]
      exact hs

theorem eq_one_of_commute_five (hdim : finrank (ZMod 2) V ≤ 5) (y u : Module.End (ZMod 2) V)
    (hy : y ^ 5 = 1) (hy1 : y ≠ 1) (huu : u * u = 1) (hcomm : u * y = y * u) : u = 1 := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨S, hS, hSne, hSr, hmin, hirr, hne', hdvd⟩ :=
    exists_cyclic_subspace y (ℓ := 5) (by norm_num) (by decide) hy hy1
  have hpos : 0 < finrank (ZMod 2) S := by
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hSne
    exact Module.finrank_pos
  have hle : finrank (ZMod 2) S ≤ 5 := (Submodule.finrank_le S).trans hdim
  have he4 : finrank (ZMod 2) S = 4 := by
    generalize finrank (ZMod 2) S = e at hpos hle hdvd
    interval_cases e <;> first | rfl | (exfalso; revert hdvd; decide)
  have huinj : Function.Injective u := by
    intro a b hab
    have := congrArg u hab
    simpa [← Module.End.mul_apply, huu] using this
  have hyu : ∀ w, y (u w) = u (y w) := fun w => by
    have := congrArg (fun T => T w) hcomm
    simpa using this.symm
  set S' := S.map u with hS'
  have hS'inv : ∀ w ∈ S', y w ∈ S' := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨y s, hS s hs, (hyu s).symm⟩
  have hfin : finrank (ZMod 2) S' = finrank (ZMod 2) S :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective u huinj S)).symm
  have hSS' : S = S' := by
    by_cases h : S ⊓ S' = ⊥
    · exfalso
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq S S'
      rw [h, finrank_bot, add_zero, hfin, he4] at h1
      have h2 : finrank (ZMod 2) ↥(S ⊔ S') ≤ finrank (ZMod 2) V := Submodule.finrank_le _
      omega
    · have hinv : Inv y (S ⊓ S') := fun w hw =>
        Submodule.mem_inf.2 ⟨hS w hw.1, hS'inv w hw.2⟩
      rcases hmin _ inf_le_left hinv with h0 | h0
      · exact absurd h0 h
      · have hle' : S ≤ S' := h0 ▸ inf_le_right
        exact Submodule.eq_of_le_of_finrank_le hle' (by rw [hfin])
  have hSu : ∀ s ∈ S, u s ∈ S := fun s hs => hSS' ▸ Submodule.mem_map_of_mem hs
  have hus1 : ∀ s ∈ S, u s = s := by
    have hcS : u.restrict hSu * y.restrict hS = y.restrict hS * u.restrict hSu := by
      ext v
      simp only [Module.End.mul_apply, LinearMap.coe_restrict_apply]
      exact (by simpa using congrArg (fun T => T (v : V)) hcomm)
    have hK : u.restrict hSu ∈ K (y.restrict hS) := mem_K_of_commute hirr hcS
    letI : Field (K (y.restrict hS)) := fieldK hirr
    set a : K (y.restrict hS) := ⟨u.restrict hSu, hK⟩ with ha
    have haa : a * a = 1 := by
      apply Subtype.ext
      show (u.restrict hSu) * (u.restrict hSu) = 1
      ext v
      have := congrArg (fun T => T (v : V)) huu
      simpa [LinearMap.coe_restrict_apply] using this
    have h2 : (2 : K (y.restrict hS)) = 0 := by
      rw [← map_ofNat (algebraMap (ZMod 2) (K (y.restrict hS))) 2]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, map_zero]
    have h1 : (a - 1) * (a - 1) = 0 := by linear_combination haa - (a - 1) * h2
    have ha1 : a = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 h1)
    intro s hs
    have h3 : u.restrict hSu = 1 := congrArg Subtype.val ha1
    have := congrArg (fun T => (T ⟨s, hs⟩ : V)) h3
    simpa [LinearMap.coe_restrict_apply] using this
  have hrange : ∀ v, y v - v ∈ S := fun v =>
    sub_mem_of_finrank_le (by norm_num) hy hS (by rw [he4]; omega) v
  have hRS : LinearMap.range (y - 1) = S := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simpa using hrange v
    · exact hSr
  set C := LinearMap.ker (y - 1) with hCdef
  have hCS : C ⊓ S = ⊥ := by
    have := ker_inf_range_eq_bot y (by decide) hy
    rw [← hRS]
    exact this
  have hCfin : finrank (ZMod 2) C + 4 = finrank (ZMod 2) V := by
    have h : finrank (ZMod 2) (LinearMap.range (y - 1)) + finrank (ZMod 2) C =
        finrank (ZMod 2) V := LinearMap.finrank_range_add_finrank_ker (y - 1)
    rw [hRS, he4] at h
    omega
  have hsupC : C ⊔ S = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq C S
    rw [hCS, finrank_bot, add_zero, he4] at h1
    omega
  have hCinv : ∀ c ∈ C, u c ∈ C := by
    intro c hc
    rw [hCdef, LinearMap.mem_ker] at hc ⊢
    have h1 : y c = c := by simpa [sub_eq_zero] using hc
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [hyu, h1]
  have hC1 : finrank (ZMod 2) C ≤ 1 := by omega
  have huC : ∀ c ∈ C, u c = c := by
    obtain ⟨c₀, hc₀⟩ := finrank_le_one_iff.1 hC1
    obtain ⟨b, hb⟩ := hc₀ ⟨u c₀, hCinv c₀ c₀.2⟩
    have hbc : b = 0 ∨ b = 1 := by
      have : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
      exact this b
    have hu0 : ((u c₀ : V)) = b • (c₀ : V) := by
      have := congrArg Subtype.val hb
      simpa using this.symm
    intro c hc
    obtain ⟨a, ha⟩ := hc₀ ⟨c, hc⟩
    have hca : c = a • (c₀ : V) := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    rw [hca, map_smul]
    rcases hbc with rfl | rfl
    · have h00 : (c₀ : V) = 0 := by
        have h1 : u (u (c₀ : V)) = (c₀ : V) := by
          have := congrArg (fun T => T (c₀ : V)) huu
          simpa using this
        rw [hu0, zero_smul, map_zero] at h1
        exact h1.symm
      rw [h00]
      simp
    · rw [hu0, one_smul]
  ext v
  have hv : v ∈ C ⊔ S := hsupC ▸ Submodule.mem_top
  obtain ⟨c, hc, s, hs, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, huC c hc, hus1 s hs]
  rfl

end CFSG.EvenSporadicStandard.M22Std.P21Field
