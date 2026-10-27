module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsLevi
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace polar_commSpace_eq_zero
  polar_sub_eq_polar_sub)

section LeviVector

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_levi_vector [CharP K 2] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {t : V ≃ₗ[K] V}
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1)
    {T : Submodule K V} (hT2 : 2 ≤ Module.finrank K T)
    (hl : Module.finrank K (commSpace t) < 2 * Module.finrank K T)
    (hTsing : ∀ x ∈ T, Q x = 0) :
    ∃ e v e' : V, e ∈ T ∧ e ≠ 0 ∧ t v - v ∈ K ∙ e ∧ polar Q e v = 0 ∧ e' ∈ T ∧
      polar Q e' v ≠ 0 := by
  set O := LinearMap.BilinForm.orthogonal (polarBilin Q) T with hO
  have hmemO : ∀ {x}, x ∈ O ↔ ∀ w ∈ T, polar Q w x = 0 := fun {x} => by
    rw [hO, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hpick : ∀ x, x ∉ O → ∃ e' ∈ T, polar Q e' x ≠ 0 := fun x hx => by
    by_contra hcon
    push Not at hcon
    exact hx (hmemO.mpr hcon)
  set C := CFSG.RankThree.OrthogonalInvolutions.fixSpace t with hC
  by_cases hCO : C ≤ O
  ·
    have hdimC : Module.finrank K (commSpace t) + Module.finrank K C = Module.finrank K V :=
      CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace t
    have hWC : commSpace t ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) C := by
      intro w hw
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
      have hx' : t x = x := CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hx
      rw [polarBilin_apply_apply, polar_comm, polar_sub_eq_polar_sub ht htt, hx', sub_self,
        polar_zero_right]
    have hWeq : commSpace t = LinearMap.BilinForm.orthogonal (polarBilin Q) C :=
      Submodule.eq_of_le_of_finrank_eq hWC (by
        rw [LinearMap.BilinForm.finrank_orthogonal hQ]
        omega)
    have hTW : T ≤ commSpace t := by
      rw [hWeq]
      intro y hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro x hx
      rw [polarBilin_apply_apply, polar_comm]
      exact hmemO.mp (hCO hx) y hy
    set Y := T.comap ((t : V →ₗ[K] V) - 1) with hY
    have hYdim : Module.finrank K Y = Module.finrank K T + Module.finrank K C :=
      finrank_comap_eq_of_le_range _ hTW
    have hOdim : Module.finrank K O = Module.finrank K V - Module.finrank K T := by
      rw [hO, LinearMap.BilinForm.finrank_orthogonal hQ]
    obtain ⟨x, hxY, hxO⟩ := exists_mem_not_mem_of_finrank_lt (A := Y) (B := O) (by omega)
    have heT : t x - x ∈ T := hxY
    obtain ⟨e', he'T, he'x⟩ := hpick x hxO
    refine ⟨t x - x, x, e', heT, fun h0 => hxO (hCO ?_), Submodule.mem_span_singleton_self _,
      ?_, he'T, he'x⟩
    · exact CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mpr (sub_eq_zero.mp h0)
    · rw [polar_sub_left, CFSG.RankThree.OrthogonalInvolutions.polar_self_eq_zero Q x, sub_zero,
        ← CFSG.RankThree.OrthogonalInvolutions.map_sub_eq_polar ht x]
      exact hTsing _ heT
  ·
    obtain ⟨x, hxC, hxO⟩ : ∃ x ∈ C, x ∉ O := by
      by_contra hcon
      push Not at hcon
      exact hCO hcon
    have hx : t x = x := CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace.mp hxC
    obtain ⟨e', he'T, he'x⟩ := hpick x hxO
    have hspan : Module.finrank K (K ∙ e') < Module.finrank K T := by
      have h1 : Module.finrank K (K ∙ e') ≤ 1 := by
        by_cases h0 : e' = 0
        · rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; omega
        · rw [finrank_span_singleton h0]
      omega
    obtain ⟨y, hyT, hye'⟩ := exists_mem_not_mem_of_finrank_lt hspan
    set c := polar Q y x / polar Q e' x with hc
    refine ⟨y - c • e', x, e', T.sub_mem hyT (T.smul_mem c he'T), fun h0 => hye' ?_, ?_, ?_,
      he'T, he'x⟩
    · rw [sub_eq_zero] at h0
      rw [h0]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e')
    · rw [hx, sub_self]
      exact Submodule.zero_mem _
    · rw [polar_sub_left, polar_smul_left, smul_eq_mul, hc, div_mul_cancel₀ _ he'x, sub_self]

end LeviVector

section Small

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_twoSubgroup_centralizer_of_finrank_lt_four
    {Q : QuadraticForm K (Fin (2 * 4) → K)} (hQ : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    {s : GL (Fin (2 * 4)) K} (hs : s ∈ matrixIsometries Q) (hss : s * s = 1)
    (hl : Module.finrank K (commSpace (matrixLinearIso s)) < 4) :
    ∃ R : Subgroup (GL (Fin (2 * 4)) K), IsPGroup 2 R ∧
      R ≤ matrixDerived Q ⊓ Subgroup.centralizer {s} ∧ Nat.card K ^ 8 ≤ Nat.card R := by
  set t := matrixLinearIso s with htdef
  have ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hs
  have htt : t * t = 1 := by rw [htdef, ← map_mul, hss, map_one]
  set W := commSpace t with hWdef
  have hWiso : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := fun x hx y hy =>
    polar_commSpace_eq_zero ht htt hx hy
  obtain ⟨a, haW, hWa⟩ := exists_le_singularPart_sup W hWiso
  set W₀ := singularPart Q W hWiso with hW₀def
  have hW₀sing : ∀ x ∈ W₀, Q x = 0 := fun x hx => hx.2
  have hW₀a : ∀ x ∈ W₀, polar Q x a = 0 := fun x hx => hWiso x hx.1 a haW
  have hWv : ∀ v, t v - v ∈ W := fun v => mem_commSpace.mpr ⟨v, rfl⟩
  have hdimV : Module.finrank K (Fin (2 * 4) → K) = 2 * 4 := Module.finrank_fin_fun K
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  by_cases h0 : Module.finrank K W₀ ≤ 2
  · obtain ⟨T, hW₀T, hTdim, hTsing, hTa⟩ := exists_totallySingular_extension (p := 2) hQ
      (r := 2) (by omega) (2 - Module.finrank K W₀) W₀ (by omega) hW₀sing hW₀a
    have hW : ∀ v, t v - v ∈ T ⊔ K ∙ a := fun v =>
      sup_le_sup_right hW₀T _ (hWa (hWv v))
    by_cases haT : a ∈ T
    ·
      obtain ⟨R, hR2, hRle, -, hRcard⟩ := exists_twoSubgroup_of_totallySingular hQ hE hs hss
        hTdim hTsing hTa hW (c := 4) (Or.inr ⟨haT, by omega⟩)
      exact ⟨R, hR2, hRle, le_trans (Nat.pow_le_pow_right hq (by norm_num)) hRcard⟩
    ·
      obtain ⟨e, v, e', heT, he0, hv, hev, he'T, he'v⟩ :=
        exists_levi_vector hQ ht htt (T := T) (by rw [hTdim]) (by rw [hTdim]; exact hl) hTsing
      obtain ⟨R, hR2, hRle, hRcard⟩ := exists_twoSubgroup_of_levi_one hQ hE hs hss hTdim hTsing
        hTa hW (c := 3) (Or.inl (by omega)) heT he0 hv hev he'T he'v
      exact ⟨R, hR2, hRle, le_trans (Nat.pow_le_pow_right hq (by norm_num)) hRcard⟩
  ·
    have hle : W₀ ≤ W := fun x hx => hx.1
    have hW₀W : W₀ = W := Submodule.eq_of_le_of_finrank_eq hle (by
      have := Submodule.finrank_mono hle
      omega)
    have hWdim : Module.finrank K W = 3 := by
      have := Submodule.finrank_mono hle
      omega
    have hWsing : ∀ x ∈ W, Q x = 0 := fun x hx => hW₀sing x (hW₀W ▸ hx)
    obtain ⟨R, hR2, hRle, -, hRcard⟩ := exists_twoSubgroup_of_totallySingular (a := 0) hQ hE hs
      hss hWdim hWsing (fun x _ => polar_zero_right Q x)
      (fun v => Submodule.mem_sup_left (hWv v)) (c := 2) (Or.inr ⟨W.zero_mem, by omega⟩)
    exact ⟨R, hR2, hRle, le_trans (Nat.pow_le_pow_right hq (by norm_num)) hRcard⟩

end Small

end CFSG.SeitzReduction.OmegaPilot
