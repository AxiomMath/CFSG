module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module

section Swap

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

include h hodd

theorem two_le_finrank_range_lineProj [Module.Finite (ZMod 2) E]
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) {u w : K × K} (hw : det2 u w ≠ 0)
    (hne : lineProj ρ u ≠ 0) : 2 ≤ finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) := by
  by_contra hlt
  push Not at hlt
  have hMne : LinearMap.range (lineProj ρ u) ≠ ⊥ := fun h0 => hne (LinearMap.range_eq_bot.1 h0)
  have hpos : 1 ≤ finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) :=
    Submodule.one_le_finrank_iff.2 hMne
  have h1 : finrank (ZMod 2) (LinearMap.range (lineProj ρ u)) = 1 := by omega
  obtain ⟨x, hx0, hx⟩ := (finrank_eq_one_iff'.1 h1 : ∃ v : LinearMap.range (lineProj ρ u),
    v ≠ 0 ∧ ∀ w, ∃ c : ZMod 2, c • v = w)
  have hxM : (x : E) ∈ LinearMap.range (lineProj ρ u) := x.2
  have hxne : (x : E) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hinv : ρ w x ∈ LinearMap.range (lineProj ρ u) := by
    obtain ⟨y, hy⟩ := hxM
    refine ⟨ρ w y, ?_⟩
    have := LinearMap.congr_fun (opE_mul_lineProj_comm h w u) y
    simpa [Module.End.mul_apply, opE, ← hy] using this.symm
  obtain ⟨c, hc⟩ := hx ⟨ρ w x, hinv⟩
  have hρne : ρ w x ≠ 0 := fun h0 => hxne (by simpa using congrArg (ρ w).symm h0)
  have hc2 : c = 0 ∨ c = 1 := by
    have : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    exact this c
  have hc1 : c = 1 := by
    rcases hc2 with rfl | rfl
    · exfalso
      apply hρne
      have := congrArg Subtype.val hc
      rw [zero_smul] at this
      exact this.symm
    · rfl
  have hfix : ρ w x = x := by
    have := congrArg Subtype.val hc
    rw [hc1, one_smul] at this
    exact this.symm
  exact hxne (fpf_of_mem_range h hodd hw hK hxM hfix)

omit [Fintype K] h hodd in
theorem det2_swap (u v : K × K) : det2 v u = -det2 u v := by
  unfold det2; ring

omit h hodd in
theorem lineProj_swap {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1) {τ : K × K → K × K}
    (hτ2 : ∀ x, τ (τ x) = x) (hτk : ∀ (k : K) (x : K × K), τ (k • x) = k • τ x)
    (hsρ : ∀ x, s * ρ x * s = ρ (τ x)) (u : K × K) :
    (s : Module.End (ZMod 2) E) * lineProj ρ u * (s : Module.End (ZMod 2) E) =
      lineProj ρ (τ u) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hbij : Function.Bijective τ := Function.Involutive.bijective hτ2
  have := lineProj_conj (g := s) (ρ := ρ) hbij hτk (fun x => by rw [hsinv]; exact hsρ x) u
  rw [hsinv] at this
  exact this

theorem card_le_finrank_range_sub1_swap [Module.Finite (ZMod 2) E]
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    {τ : K × K → K × K} (hτ2 : ∀ x, τ (τ x) = x)
    (hτk : ∀ (k : K) (x : K × K), τ (k • x) = k • τ x)
    (hsρ : ∀ x, s * ρ x * s = ρ (τ x)) (U : Finset (K × K))
    (hself : ∀ u ∈ U, det2 u (τ u) ≠ 0)
    (hpair : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 ∧ det2 u (τ v) ≠ 0 ∧
      det2 (τ u) v ≠ 0 ∧ det2 (τ u) (τ v) ≠ 0)
    (hne : ∀ u ∈ U, lineProj ρ u ≠ 0) :
    2 * U.card ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  set π : K × K → Module.End (ZMod 2) E := fun u => lineProj ρ u + lineProj ρ (τ u) with hπdef
  have hs' : (s : Module.End (ZMod 2) E) * (s : Module.End (ZMod 2) E) = 1 :=
    congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) hs
  have hsw : ∀ u, (s : Module.End (ZMod 2) E) * lineProj ρ u =
      lineProj ρ (τ u) * (s : Module.End (ZMod 2) E) := by
    intro u
    calc (s : Module.End (ZMod 2) E) * lineProj ρ u
        = (s : Module.End (ZMod 2) E) * lineProj ρ u * ((s : Module.End (ZMod 2) E) *
            (s : Module.End (ZMod 2) E)) := by rw [hs', mul_one]
      _ = ((s : Module.End (ZMod 2) E) * lineProj ρ u * (s : Module.End (ZMod 2) E)) *
            (s : Module.End (ZMod 2) E) := by simp only [mul_assoc]
      _ = lineProj ρ (τ u) * (s : Module.End (ZMod 2) E) := by
          rw [lineProj_swap hs hτ2 hτk hsρ u]
  have hπ : ∀ u ∈ U, π u * π u = π u := by
    intro u hu
    have h1 := lineProj_mul_self h hodd u
    have h2 := lineProj_mul_self h hodd (τ u)
    have h3 := lineProj_mul_of_indep h hodd (hself u hu)
    have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
      rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
    simp only [hπdef, add_mul, mul_add, h1, h2, h3, h4]
    simp
  have horth : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → π u * π v = 0 := by
    intro u hu v hv huv
    obtain ⟨d1, d2, d3, d4⟩ := hpair u hu v hv huv
    simp only [hπdef, add_mul, mul_add,
      lineProj_mul_of_indep h hodd d1, lineProj_mul_of_indep h hodd d2,
      lineProj_mul_of_indep h hodd d3, lineProj_mul_of_indep h hodd d4]
    simp
  have hcomm : ∀ u ∈ U, (s : Module.End (ZMod 2) E) * π u = π u * (s : Module.End (ZMod 2) E) := by
    intro u hu
    simp only [hπdef, mul_add, add_mul, hsw u, hsw (τ u), hτ2 u]
    abel
  have hc : ∀ u ∈ U, 2 ≤ finrank (ZMod 2) ((LinearMap.range (π u)).map (sub1 s)) := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      exact hself 0 hu (by simp [det2])
    obtain ⟨w, hw⟩ := exists_det_ne u hu0
    have hX2 := two_le_finrank_range_lineProj h hodd hK hw (hne u hu)
    set X := LinearMap.range (lineProj ρ u) with hX
    have hXle : X ≤ LinearMap.range (π u) := by
      rintro _ ⟨y, rfl⟩
      refine ⟨lineProj ρ u y, ?_⟩
      have h1 := lineProj_mul_self h hodd u
      have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
        rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
      simp only [hπdef, LinearMap.add_apply]
      have e1 : lineProj ρ u (lineProj ρ u y) = lineProj ρ u y := by
        rw [← Module.End.mul_apply, h1]
      have e2 : lineProj ρ (τ u) (lineProj ρ u y) = 0 := by
        rw [← Module.End.mul_apply, h4]; rfl
      rw [e1, e2, add_zero]
    have hinj : Function.Injective ((sub1 s).domRestrict X) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, hxX⟩ hx0
      obtain ⟨y, rfl⟩ := hxX
      have hsx : s (lineProj ρ u y) = lineProj ρ u y := by
        have := hx0
        simp only [LinearMap.domRestrict_apply, sub1_apply'] at this
        exact e_eq_of_add_eq_zero this
      have h4 := lineProj_mul_of_indep h hodd (show det2 (τ u) u ≠ 0 by
        rw [det2_swap]; exact neg_ne_zero.2 (hself u hu))
      have h1 := lineProj_mul_self h hodd u
      have hxa : lineProj ρ (τ u) (lineProj ρ u y) = 0 := by
        rw [← Module.End.mul_apply, h4]; rfl
      have hxa' : lineProj ρ (τ u) (lineProj ρ u y) = lineProj ρ u y := by
        have := lineProj_swap hs hτ2 hτk hsρ u
        have h5 := LinearMap.congr_fun this (lineProj ρ u y)
        simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at h5
        have e1 : lineProj ρ u (s (lineProj ρ u y)) = lineProj ρ u y := by
          rw [hsx]
          rw [← Module.End.mul_apply, h1]
        rw [e1, hsx] at h5
        exact h5.symm
      apply Subtype.ext
      show lineProj ρ u y = 0
      rw [← hxa', hxa]
    have hrk : finrank (ZMod 2) (LinearMap.range ((sub1 s).domRestrict X)) =
        finrank (ZMod 2) X := LinearMap.finrank_range_of_inj hinj
    rw [LinearMap.range_domRestrict] at hrk
    have hmono := Submodule.finrank_mono (Submodule.map_mono (f := sub1 s) hXle)
    omega
  have := sum_le_finrank_range_sub1 s U π hπ horth hcomm (fun _ => 2) hc
  simpa [Finset.sum_const, mul_comm] using this

end Swap

end CFSG.QuasithinUnique.Setup.Family
