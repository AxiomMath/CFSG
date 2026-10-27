module

public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center
public import CFSG.ClassicalInvolution.RouteD.TWS8Geo1
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.RouteD.TWS8

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Eichler

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [FiniteDimensional F V] in
theorem isRefl_polarBilin3 (Q : QuadraticForm F V) : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rw [polar_comm]
  exact h

theorem exists_smul_of_commute_eichler (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank F V) {u : V} (hu : Q u = 0) (hu0 : u ≠ 0) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hc : ∀ v, polar Q u v = 0 → g * eichler Q u v = eichler Q u v * g) :
    ∃ c : F, g u = c • u := by
  classical
  by_contra hne
  push Not at hne
  have hgu : g u ∉ Submodule.span F {u} := by
    intro h
    obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp h
    exact hne c hc'.symm
  obtain ⟨Up, hUp⟩ : ∃ Up : Submodule F V,
      Up = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span F {u}) := ⟨_, rfl⟩
  have hmemUp : ∀ x, x ∈ Up ↔ polar Q u x = 0 := by
    intro x
    rw [hUp, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have := h u (Submodule.mem_span_singleton_self u)
      rwa [polarBilin_apply_apply] at this
    · intro h z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [polarBilin_apply_apply, polar_smul_left_eq, h,
        mul_zero]
  have hpuu : polar Q u u = 0 := polar_self_eq_zero hu
  obtain ⟨x₀, hx₀, hx₀g⟩ : ∃ x₀ ∈ Up, polar Q x₀ (g u) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hgu
    have h1 : g u ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) Up := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hz
      rw [polarBilin_apply_apply]
      exact hcon z hz
    rwa [hUp, LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin3 Q)] at h1
  have hQgu : Q (g u) = 0 := by rw [map_of_mem hg, hu]
  have hx₀u : polar Q x₀ u = 0 := by rw [polar_comm]; exact (hmemUp x₀).mp hx₀
  have hmem : ∀ v ∈ Up, g v ∈ Submodule.span F {g u, u} := by
    intro v hv
    have hv' : polar Q u v = 0 := (hmemUp v).mp hv
    have hQgv : Q (g v) = Q v := map_of_mem hg v
    have hpgv : polar Q (g u) (g v) = 0 := by rw [polar_map_of_mem hg, hv']
    have hE := eichler_conj hg u v
    rw [hc v hv', mul_assoc, mul_inv_cancel, mul_one] at hE
    have hE' := LinearEquiv.congr_fun hE x₀
    rw [eichler_apply hu hv', eichler_apply hQgu hpgv] at hE'
    have h3 : polar Q x₀ (g u) • g v = (polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u -
        polar Q x₀ v • u := by
      rw [hx₀u] at hE'
      simp only [zero_smul, mul_zero, add_zero] at hE'
      calc polar Q x₀ (g u) • g v
          = (x₀ + polar Q x₀ (g u) • g v -
              (polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u) - x₀ +
              (polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u := by abel
        _ = (x₀ - polar Q x₀ v • u) - x₀ +
              (polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u := by rw [← hE']
        _ = (polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u - polar Q x₀ v • u := by abel
    have hgv : g v = (polar Q x₀ (g u))⁻¹ •
        ((polar Q x₀ (g v) + Q (g v) * polar Q x₀ (g u)) • g u - polar Q x₀ v • u) := by
      rw [← h3, smul_smul, inv_mul_cancel₀ hx₀g, one_smul]
    rw [hgv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _ (Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
  have hdimUp : 3 ≤ Module.finrank F Up := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal hQ (Submodule.span F {u})
    have h2 : Module.finrank F (Submodule.span F {u}) = 1 := finrank_span_singleton hu0
    rw [← hUp] at h1
    omega
  have hmap : Submodule.map g.toLinearMap Up ≤ Submodule.span F {g u, u} := by
    rintro _ ⟨v, hv, rfl⟩
    exact hmem v hv
  have h5 := Submodule.finrank_mono hmap
  rw [LinearEquiv.finrank_map_eq g Up] at h5
  have h6 : Module.finrank F (Submodule.span F {g u, u}) ≤ 2 := by
    have := finrank_span_finset_le_card (R := F) ({g u, u} : Finset V)
    simp only [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans Finset.card_le_two
  omega

end Eichler

section Scalar

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eq_of_singular_pair {g : V ≃ₗ[F] V}
    (hline : ∀ u, Q u = 0 → u ≠ 0 → ∃ c : F, g u = c • u) {u v u' v' : V} (hu : Q u = 0)
    (hv : Q v = 0) (huv : polar Q u v = 0) (huu' : polar Q u u' = 1) (hvu' : polar Q v u' = 0)
    (huv' : polar Q u v' = 0) (hvv' : polar Q v v' = 1) {a b : F} (ha : g u = a • u)
    (hb : g v = b • v) : a = b := by
  have hQ : Q (u + v) = 0 := by rw [QuadraticMap.map_add Q, hu, hv, huv]; ring
  have hne : u + v ≠ 0 := fun h => by
    have h0 := congrArg (fun y => polar Q y u') h
    simp [polar_add_left, huu', hvu'] at h0
  obtain ⟨c, hc⟩ := hline (u + v) hQ hne
  rw [map_add, ha, hb] at hc
  have h1 := congrArg (fun y => polar Q y u') hc
  have h2 := congrArg (fun y => polar Q y v') hc
  simp only [polar_add_left, polar_smul_left_eq, huu', hvu', huv', hvv', mul_one, mul_zero,
    add_zero, zero_add] at h1 h2
  rw [h1, h2]

theorem ne_zero_of_polar_eq_one {u u' : V} (h : polar Q u u' = 1) : u ≠ 0 := fun h0 => by
  rw [h0, polar_zero_left] at h
  exact zero_ne_one h

theorem exists_scalar_of_forall_singular (fr : OFrame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hline : ∀ u, Q u = 0 → u ≠ 0 → ∃ c : F, g u = c • u) :
    ∃ c : F, ∀ x, g x = c • x := by
  classical
  obtain ⟨c₁, h₁⟩ := hline fr.e₁ fr.Q_e₁ (ne_zero_of_polar_eq_one fr.polar_e₁_f₁)
  obtain ⟨c₂, h₂⟩ := hline fr.e₂ fr.Q_e₂ (ne_zero_of_polar_eq_one fr.polar_e₂_f₂)
  obtain ⟨c₃, h₃⟩ := hline fr.f₁ fr.Q_f₁ (ne_zero_of_polar_eq_one fr.polar_f₁_e₁)
  obtain ⟨c₄, h₄⟩ := hline fr.f₂ fr.Q_f₂ (ne_zero_of_polar_eq_one fr.polar_f₂_e₂)
  have e12 : c₁ = c₂ := eq_of_singular_pair hline fr.Q_e₁ fr.Q_e₂ fr.polar_e₁_e₂ fr.polar_e₁_f₁
    fr.polar_e₂_f₁ fr.polar_e₁_f₂ fr.polar_e₂_f₂ h₁ h₂
  have e32 : c₃ = c₂ := eq_of_singular_pair hline fr.Q_f₁ fr.Q_e₂ fr.polar_f₁_e₂ fr.polar_f₁_e₁
    fr.polar_e₂_e₁ fr.polar_f₁_f₂ fr.polar_e₂_f₂ h₃ h₂
  have e41 : c₁ = c₄ := eq_of_singular_pair hline fr.Q_e₁ fr.Q_f₂ fr.polar_e₁_f₂ fr.polar_e₁_f₁
    fr.polar_f₂_f₁ fr.polar_e₁_e₂ fr.polar_f₂_e₂ h₁ h₄
  have h₂' : g fr.e₂ = c₁ • fr.e₂ := by rw [h₂, e12]
  have h₃' : g fr.f₁ = c₁ • fr.f₁ := by rw [h₃, e32, e12]
  have h₄' : g fr.f₂ = c₁ • fr.f₂ := by rw [h₄, ← e41]
  have hf0 : fr.f₁ ≠ 0 := ne_zero_of_polar_eq_one fr.polar_f₁_e₁
  have hc0 : c₁ ≠ 0 := by
    intro h0
    apply hf0
    apply g.injective
    rw [h₃', h0, zero_smul, map_zero]
  have hperp : ∀ a ∈ fr.perp, g a = c₁ • a := by
    intro a ha
    have hae : polar Q fr.e₁ a = 0 := polar_wPlane_perp ha (e₁_mem_wPlane fr)
    have haf : polar Q fr.f₁ a = 0 := polar_wPlane_perp ha (f₁_mem_wPlane fr)
    have haf' : polar Q a fr.f₁ = 0 := polar_perp_wPlane ha (f₁_mem_wPlane fr)
    obtain ⟨q, hq⟩ : ∃ q : F, q = Q a := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : V, s = fr.e₁ + (-q) • fr.f₁ + a := ⟨_, rfl⟩
    have hQs : Q s = 0 := by
      rw [hs, QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, fr.Q_e₁, fr.Q_f₁,
        polar_add_left, polar_smul_left_eq, polar_smul_right_eq, fr.polar_e₁_f₁, hae, haf, ← hq]
      ring
    have hsf : polar Q s fr.f₁ = 1 := by
      rw [hs, polar_add_left, polar_add_left, polar_smul_left_eq, fr.polar_e₁_f₁, fr.polar_f₁_f₁,
        haf']
      ring
    have hs0 : s ≠ 0 := ne_zero_of_polar_eq_one hsf
    obtain ⟨c₅, h₅⟩ := hline s hQs hs0
    have h6 : g s = g fr.e₁ + (-q) • g fr.f₁ + g a := by
      rw [hs, map_add, map_add, map_smul]
    rw [h₅, h₁, h₃'] at h6
    have hga : g a = c₅ • s - c₁ • fr.e₁ - (-q) • (c₁ • fr.f₁) := by
      rw [h6]
      abel
    have hgaf : polar Q (g a) fr.f₁ = 0 := by
      have h7 := polar_map_of_mem hg a fr.f₁
      rw [h₃', polar_smul_right_eq, haf'] at h7
      exact (mul_eq_zero.mp h7).resolve_left hc0
    rw [hga] at hgaf
    simp only [polar_sub_left, polar_smul_left_eq, hsf, fr.polar_e₁_f₁, fr.polar_f₁_f₁] at hgaf
    have hc5 : c₅ = c₁ := by linear_combination hgaf
    rw [hga, hc5, hs]
    module
  refine ⟨c₁, fun x => ?_⟩
  have hW : g (fr.incl (fr.coords x)) = c₁ • fr.incl (fr.coords x) := by
    rw [Frame.incl_apply]
    simp only [map_add, map_smul, h₁, h₂', h₃', h₄']
    module
  have hA : g (x - fr.incl (fr.coords x)) = c₁ • (x - fr.incl (fr.coords x)) :=
    hperp _ (sub_incl_mem_perp fr x)
  calc g x = g (fr.incl (fr.coords x) + (x - fr.incl (fr.coords x))) := by rw [add_sub_cancel]
    _ = c₁ • x := by rw [map_add, hW, hA, ← smul_add, add_sub_cancel]

variable [FiniteDimensional F V]

theorem centerScalar_of_frame (hQ : (polarBilin Q).Nondegenerate) (fr : OFrame Q) :
    CenterScalar Q := by
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  have hzO : (z : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q z.2
  have h4 : 4 ≤ Module.finrank F V := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four fr
    omega
  obtain ⟨c, hc⟩ := exists_scalar_of_forall_singular fr hzO (fun u hu hu0 =>
    exists_smul_of_commute_eichler hQ h4 hu hu0 hzO (fun v _ => by
      have := Subgroup.mem_center_iff.mp hz ⟨eichler Q u v, eichler_mem_elementaryGroup Q u v⟩
      exact (congrArg Subtype.val this).symm))
  exact mem_scalars.mpr ⟨c, hc⟩

end Scalar

end CFSG.ClassicalInvolution.Q3.Q3TZ
