module

public import CFSG.ClassicalInvolution.RouteD.TWS8Geo3
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.TWS8 CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped MatrixGroups commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Reflect

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem exists_stabE_reflect (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : F) ≠ 0)
    (fr : OFrame Q) {b : V} (hb : b ∈ fr.perp) (hQb : Q b ≠ 0) :
    ∃ g ∈ stabE fr, g fr.e₁ = fr.e₁ ∧ ∀ a ∈ fr.perp, g a = reflect Q b a := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : V, w = fr.e₂ + Q b • fr.f₂ := ⟨_, rfl⟩
  have hf₂ : fr.f₂ ∈ wPlane fr := ⟨!![0, 0; 1, 0], by simp [Frame.incl_apply]⟩
  have hwW : w ∈ wPlane fr := by
    rw [hw]
    exact (wPlane fr).add_mem (e₂_mem_wPlane fr) ((wPlane fr).smul_mem _ hf₂)
  have hQw : Q w = Q b := by
    rw [hw, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, fr.Q_e₂,
      fr.Q_f₂, fr.polar_e₂_f₂]
    ring
  have hQw0 : Q w ≠ 0 := by rw [hQw]; exact hQb
  have hbw : polar Q b w = 0 := polar_perp_wPlane hb hwW
  have hwb : polar Q w b = 0 := polar_wPlane_perp hb hwW
  have he₁w : polar Q fr.e₁ w = 0 := by
    rw [hw, polar_add_right, polar_smul_right_eq, fr.orth.ee, fr.orth.ef]
    ring
  have hwe₁ : polar Q w fr.e₁ = 0 := by rw [polar_comm]; exact he₁w
  have hbe₁ : polar Q b fr.e₁ = 0 := polar_perp_wPlane hb (e₁_mem_wPlane fr)
  have hQy : Q (b - w) = 2 * Q b := by
    have h1 : b - w = b + (-1 : F) • w := by rw [neg_smul, one_smul, sub_eq_add_neg]
    rw [h1, QuadraticMap.map_add Q, map_smul_eq_sq, polar_smul_right_eq, hQw, hbw]
    ring
  have hQy0 : Q (b - w) ≠ 0 := by
    rw [hQy]
    exact mul_ne_zero h2 hQb
  have hyb : reflect Q (b - w) b = w := by
    have hpol : polar Q (b - w) b = 2 * Q b := by
      rw [polar_sub_left, hwb, polar_self, sub_zero, nsmul_eq_mul]
      norm_num
    rw [reflect_apply hQy0, hpol, hQy, div_self (mul_ne_zero h2 hQb), one_smul]
    abel
  have hcomm : ⁅reflect Q b, reflect Q (b - w)⁆ = reflect Q b * reflect Q w := by
    have hyO := reflect_mem_orthogonalGroup Q (b - w)
    have h1 := reflect_conj hyO b
    rw [hyb, reflect_inv] at h1
    simp only [commutatorElement_def, reflect_inv]
    calc reflect Q b * reflect Q (b - w) * reflect Q b * reflect Q (b - w)
        = reflect Q b * (reflect Q (b - w) * reflect Q b * reflect Q (b - w)) := by group
      _ = reflect Q b * reflect Q w := by rw [h1]
  have hgE : ⁅reflect Q b, reflect Q (b - w)⁆ ∈ elementaryGroup Q :=
    commutatorElement_reflect_mem hQ fr.orth b (b - w)
  rw [hcomm] at hgE
  have hrw : ∀ x, polar Q w x = 0 → reflect Q w x = x := fun x h =>
    reflect_apply_of_polar_eq_zero h
  have hrb : ∀ x, polar Q b x = 0 → reflect Q b x = x := fun x h =>
    reflect_apply_of_polar_eq_zero h
  refine ⟨reflect Q b * reflect Q w, ⟨hgE, mem_stabSub_of_mapsTo fun y hy => ?_⟩, ?_,
    fun a ha => ?_⟩
  · have h1 : reflect Q w y ∈ wPlane fr := by
      rw [reflect_apply hQw0]
      exact (wPlane fr).sub_mem hy ((wPlane fr).smul_mem _ hwW)
    rw [LinearEquiv.mul_apply, hrb _ (polar_perp_wPlane hb h1)]
    exact h1
  · rw [LinearEquiv.mul_apply, hrw _ hwe₁, hrb _ hbe₁]
  · rw [LinearEquiv.mul_apply, hrw a (polar_wPlane_perp ha hwW)]

theorem mixMod_reflect (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : F) ≠ 0) (fr : OFrame Q)
    {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H) {b a : V} (hb : b ∈ fr.perp)
    (hQb : Q b ≠ 0) (ha : a ∈ mixMod fr H hH) : reflect Q b a ∈ mixMod fr H hH := by
  obtain ⟨g, hg, hge, hga⟩ := exists_stabE_reflect hQ h2 fr hb hQb
  obtain ⟨ha1, ha2⟩ := mem_mixMod.mp ha
  have hO := elementaryGroup_le_orthogonalGroup Q hg.1
  refine mem_mixMod.mpr ⟨?_, ?_⟩
  · rw [reflect_apply hQb]
    exact fr.perp.sub_mem ha1 (fr.perp.smul_mem _ hb)
  · have h1 := eichler_conj hO fr.e₁ a
    rw [hge, hga a ha1] at h1
    rw [← h1]
    exact H.mul_mem (H.mul_mem (hH hg) ha2) (H.inv_mem (hH hg))

end Reflect


section Mix

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem mixMod_eq_perp_of_aniso (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    (hdim : Module.finrank F fr.perp = 2) (hQ0 : ∀ x ∈ fr.perp, Q x = 0 → x = 0) {a : V}
    (ha : a ∈ mixMod fr H hH) (ha0 : a ≠ 0) : ∀ x ∈ fr.perp, x ∈ mixMod fr H hH := by
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.Orth15.two_ne_zero_of_odd_card hodd
  have hNle : mixMod fr H hH ≤ fr.perp := fun x hx => (mem_mixMod.mp hx).1
  have haA : a ∈ fr.perp := hNle ha
  have hQa0 : Q a ≠ 0 := fun h => ha0 (hQ0 a haA h)
  obtain ⟨a', ha'A, ha'span⟩ : ∃ a' ∈ fr.perp, a' ∉ Submodule.span F {a} := by
    by_contra hcon
    push Not at hcon
    have h1 : fr.perp ≤ Submodule.span F {a} := fun x hx => hcon x hx
    have h2' := Submodule.finrank_mono h1
    rw [finrank_span_singleton ha0, hdim] at h2'
    omega
  have hapol : polar Q a a ≠ 0 := by
    rw [polar_self, nsmul_eq_mul]
    simpa using mul_ne_zero h2 hQa0
  obtain ⟨b, hbA, hbspan, hab⟩ : ∃ b ∈ fr.perp, b ∉ Submodule.span F {a} ∧ polar Q a b ≠ 0 := by
    by_cases hp : polar Q a a' = 0
    · refine ⟨a + a', fr.perp.add_mem haA ha'A, ?_, ?_⟩
      · intro hmem
        apply ha'span
        have h1 : a' = (a + a') - a := by abel
        rw [h1]
        exact (Submodule.span F {a}).sub_mem hmem (Submodule.mem_span_singleton_self a)
      · rw [polar_add_right, hp, add_zero]
        exact hapol
    · exact ⟨a', ha'A, ha'span, hp⟩
  have hb0 : b ≠ 0 := fun h => hbspan (by rw [h]; exact Submodule.zero_mem _)
  have hQb : Q b ≠ 0 := fun h => hb0 (hQ0 b hbA h)
  have hbN : b ∈ mixMod fr H hH := by
    have hr := mixMod_reflect hQ h2 fr hH hbA hQb ha
    rw [reflect_apply hQb] at hr
    have hc : polar Q b a / Q b ≠ 0 := by
      rw [polar_comm]
      exact div_ne_zero hab hQb
    have h1 : (polar Q b a / Q b) • b ∈ mixMod fr H hH := by
      have := (mixMod fr H hH).sub_mem ha hr
      rwa [sub_sub_cancel] at this
    have := (mixMod fr H hH).smul_mem (polar Q b a / Q b)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hli : LinearIndependent F ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right ha0, rfl⟩
    · exfalso
      apply hbspan
      have h1 : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
      have : b = (-(t⁻¹ * s)) • a := by
        calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • a)) := by rw [h1]
          _ = (-(t⁻¹ * s)) • a := by rw [smul_neg, smul_smul, neg_smul]
      rw [this]
      exact (Submodule.span F {a}).smul_mem _ (Submodule.mem_span_singleton_self a)
  have hspan : Module.finrank F (Submodule.span F (Set.range (![a, b] : Fin 2 → V))) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hsle : Submodule.span F (Set.range (![a, b] : Fin 2 → V)) ≤ mixMod fr H hH := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ha
    · exact hbN
  have heq : mixMod fr H hH = fr.perp := Submodule.eq_of_le_of_finrank_le hNle (by
    have := Submodule.finrank_mono hsle
    omega)
  intro x hx
  rw [heq]
  exact hx

theorem eichler_mem_of_mixed_aniso (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)} (hH : stabE fr ≤ H)
    (hdim : Module.finrank F fr.perp = 2) (hQ0 : ∀ x ∈ fr.perp, Q x = 0 → x = 0) {a : V}
    (ha : a ∈ fr.perp) (ha0 : a ≠ 0) (haH : eichler Q fr.e₁ a ∈ H) :
    ∀ w, polar Q fr.e₁ w = 0 → eichler Q fr.e₁ w ∈ H := by
  have hperp := mixMod_eq_perp_of_aniso hodd hQ fr hH hdim hQ0 (mem_mixMod.mpr ⟨ha, haH⟩) ha0
  intro w hw
  have hwAperp : w - fr.incl (fr.coords w) ∈ fr.perp := sub_incl_mem_perp fr w
  have hwWe : polar Q fr.e₁ (fr.incl (fr.coords w)) = 0 := by
    have h1 : polar Q fr.e₁ (w - fr.incl (fr.coords w)) = 0 :=
      polar_wPlane_perp hwAperp (e₁_mem_wPlane fr)
    rw [polar_sub_right, hw, zero_sub, neg_eq_zero] at h1
    exact h1
  have hsplit : w = fr.incl (fr.coords w) + (w - fr.incl (fr.coords w)) := by abel
  have hE1 : eichler Q fr.e₁ (fr.incl (fr.coords w)) ∈ H :=
    hH (eichler_mem_stabE fr (e₁_mem_wPlane fr) (incl_mem_wPlane fr _))
  have hE2 : eichler Q fr.e₁ (w - fr.incl (fr.coords w)) ∈ H :=
    (mem_mixMod.mp (hperp _ hwAperp)).2
  rw [hsplit, ← eichler_mul hwWe (polar_wPlane_perp hwAperp (e₁_mem_wPlane fr))]
  exact H.mul_mem hE1 hE2

theorem elementaryGroup_le_of_mixed_aniso (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) {H : Subgroup (V ≃ₗ[F] V)}
    (hH : stabE fr ≤ H) (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hdim : Module.finrank F fr.perp = 2) (hQ0 : ∀ x ∈ fr.perp, Q x = 0 → x = 0) {a : V}
    (ha : a ∈ fr.perp) (ha0 : a ≠ 0) (haH : eichler Q fr.e₁ a ∈ H) :
    elementaryGroup Q ≤ H := by
  have hU := eichler_mem_of_mixed_aniso hodd hQ fr hH hdim hQ0 ha ha0 haH
  have he0 : fr.e₁ ≠ 0 := fun h => by
    have := fr.polar_e₁_f₁
    rw [h] at this
    simp at this
  have hf0 : fr.f₁ ≠ 0 := fun h => by
    have := fr.polar_e₁_f₁
    rw [h] at this
    simp at this
  obtain ⟨g, hg, hge⟩ := exists_stabE_apply_eq hQ fr (e₁_mem_wPlane fr) (f₁_mem_wPlane fr) he0
    hf0 (by rw [fr.Q_e₁, fr.Q_f₁])
  exact elementaryGroup_le_of_subgroup' (P := fr.P) H hQ hHO hU
    ⟨g, hH hg, 1, one_ne_zero, by rw [one_smul]; exact hge⟩

end Mix

end CFSG.ClassicalInvolution.Q3.Q3TZ
