module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Odd

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem no_skew_adjoint_odd (h2 : (2 : F) ≠ 0) {Q : QuadraticForm F V}
    (hQ : (polarBilin Q).Nondegenerate) (hodd : Odd (Module.finrank F V)) (g : V →ₗ[F] V)
    (hg : Function.Injective g) (hskew : ∀ x y, polar Q (g x) y = - polar Q x (g y)) : False := by
  set B := polarBilin Q with hB
  let e : V ≃ₗ[F] Module.Dual F V := LinearMap.BilinForm.toDual B hQ
  have hdual : g.dualMap = -(e.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap) := by
    apply LinearMap.ext; intro f; apply LinearMap.ext; intro y
    have hf : f = e (e.symm f) := (e.apply_symm_apply f).symm
    set u := e.symm f with hu
    rw [hf]
    simp only [LinearMap.dualMap_apply, LinearMap.neg_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show B u (g y) = -(B (g u) y)
    simp only [hB, polarBilin_apply_apply]
    rw [hskew]
    ring
  have h1 : g.dualMap.det = g.det := LinearMap.det_dualMap g
  have h3 : g.det = (-1) ^ Module.finrank F V * g.det := by
    calc g.det = g.dualMap.det := h1.symm
      _ = LinearMap.det ((-1 : F) • (e.toLinearMap ∘ₗ g ∘ₗ e.symm.toLinearMap)) := by
        rw [hdual]
        congr 1
        ext x
        simp
      _ = (-1) ^ Module.finrank F (Module.Dual F V) * g.det := by
        rw [LinearMap.det_smul, LinearMap.det_conj]
      _ = (-1) ^ Module.finrank F V * g.det := by
        rw [Subspace.dual_finrank_eq]
  have h4 : g.det = 0 := by
    rw [hodd.neg_one_pow] at h3
    have : (2 : F) * g.det = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left h2
  let ge : V ≃ₗ[F] V := LinearEquiv.ofInjectiveEndo g hg
  have h5 := LinearEquiv.isUnit_det' ge
  have h6 : LinearMap.det (ge : V →ₗ[F] V) = 0 := h4
  rw [h6] at h5
  exact not_isUnit_zero h5

end Odd

section SkewRoot

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

structure SkewRoot (Q : QuadraticForm F V) (g : V →ₗ[F] V) (c : F) : Prop where
  inj : Function.Injective g
  skew : ∀ x y, polar Q (g x) y = -polar Q x (g y)
  sq : ∀ x, g (g x) = c • x
  ne : c ≠ 0

namespace SkewRoot

variable {g : V →ₗ[F] V} {c : F}

theorem polar_self_g (hg : SkewRoot Q g c) (h2 : (2 : F) ≠ 0) (x : V) : polar Q x (g x) = 0 := by
  have h := hg.skew x x
  rw [polar_comm] at h
  have : (2 : F) * polar Q x (g x) = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left h2

theorem polar_g_g (hg : SkewRoot Q g c) (x y : V) : polar Q (g x) (g y) = -c * polar Q x y := by
  rw [hg.skew, hg.sq, polar_smul_right]
  ring

theorem Q_g (hg : SkewRoot Q g c) (h2 : (2 : F) ≠ 0) (x : V) : Q (g x) = -c * Q x := by
  have h := hg.polar_g_g x x
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at h
  have : (2 : F) * (Q (g x) + c * Q x) = 0 := by linear_combination h
  have := (mul_eq_zero.mp this).resolve_left h2
  linear_combination this

end SkewRoot

end SkewRoot

section Frames

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V} {g : V →ₗ[F] V} {c : F}

theorem exists_singular_not_eigen (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hg : SkewRoot Q g c) {C : Submodule F V}
    (hC : PolarNondegOn Q C) (h3 : 3 ≤ Module.finrank F C) :
    ∃ v ∈ C, Q v = 0 ∧ v ≠ 0 ∧ ∀ a : F, g v ≠ a • v := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P, hPe, hPf⟩ := exists_hypPair_in_nondeg hodd hC h3
  have hN : PolarNondegOn Q (C ⊓ P.perp) := hC.inf_perp P hPe hPf
  have hfin := finrank_le_inf_perp_add_two hQ C P
  obtain ⟨z₀, hz₀, hz₀ne⟩ : ∃ z₀ ∈ C ⊓ P.perp, z₀ ≠ 0 := by
    have : 0 < Module.finrank F ↥(C ⊓ P.perp) := by omega
    obtain ⟨⟨z, hz⟩, hne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨z, hz, fun h => hne (Subtype.ext h)⟩
  obtain ⟨a, ha⟩ := hcon P.e hPe P.Q_e P.e_ne_zero
  obtain ⟨b, hb⟩ := hcon P.f hPf P.Q_f P.f_ne_zero
  have hba : b = -a := by
    have h := hg.skew P.e P.f
    rw [ha, hb, polar_smul_left, polar_smul_right, P.polar_ef] at h
    simp only [smul_eq_mul, mul_one] at h
    linear_combination h
  have ha0 : a ≠ 0 := by
    intro h0
    apply P.e_ne_zero
    apply hg.inj
    rw [ha, h0, zero_smul, map_zero]
  have hQz : ∀ z ∈ C ⊓ P.perp, Q z = 0 := by
    intro z hz
    obtain ⟨hzC, hzP⟩ := Submodule.mem_inf.mp hz
    obtain ⟨hze, hzf⟩ := HypPair.mem_perp.mp hzP
    have hzE : polar Q z P.e = 0 := by rw [polar_comm]; exact hze
    have hzF : polar Q z P.f = 0 := by rw [polar_comm]; exact hzf
    have hQez : Q (P.e + z) = Q z := by
      rw [QuadraticMap.map_add Q, P.Q_e, hze]; ring
    have hh : polar Q P.f (P.e + z) = 1 := by
      rw [polar_add_right, P.polar_fe, hzf]; ring
    set vz : V := (P.e + z) - Q (P.e + z) • P.f with hvz
    have hQvz : Q vz = 0 := (HypPair.ofPolarEqOne P.Q_f hh).Q_f
    have hvzC : vz ∈ C := C.sub_mem (C.add_mem hPe hzC) (C.smul_mem _ hPf)
    have hpf : polar Q vz P.f = 1 := by
      rw [hvz, polar_sub_left, polar_add_left, polar_smul_left, P.polar_ef, hzF, P.polar_ff]; ring
    have hpe : polar Q vz P.e = -Q z := by
      rw [hvz, polar_sub_left, polar_add_left, polar_smul_left, P.polar_ee, hzE, P.polar_fe, hQez]
      ring
    have hvz0 : vz ≠ 0 := by
      intro h0
      rw [h0, polar_zero_left] at hpf
      exact zero_ne_one hpf
    obtain ⟨ν, hν⟩ := hcon vz hvzC hQvz hvz0
    have e1 : polar Q (g vz) P.f = ν := by rw [hν, polar_smul_left, hpf]; ring
    have e2 : polar Q (g vz) P.f = a := by
      rw [hg.skew, hb, polar_smul_right, hpf, hba]; ring
    have e3 : polar Q (g vz) P.e = -ν * Q z := by rw [hν, polar_smul_left, hpe]; ring
    have e4 : polar Q (g vz) P.e = a * Q z := by
      rw [hg.skew, ha, polar_smul_right, hpe]; ring
    have : (2 : F) * a * Q z = 0 := by
      have hνa : ν = a := e1.symm.trans e2
      rw [hνa] at e3
      linear_combination e3 - e4
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2
      · exact absurd h ha0
    · exact h
  apply hz₀ne
  apply hN z₀ hz₀
  intro z hz
  have h1 := hQz (z₀ + z) ((C ⊓ P.perp).add_mem hz₀ hz)
  rw [QuadraticMap.map_add Q, hQz z₀ hz₀, hQz z hz, zero_add, zero_add] at h1
  exact h1

theorem exists_gstable_frame (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (hg : SkewRoot Q g c) {C : Submodule F V}
    (hC : PolarNondegOn Q C) (h3 : 3 ≤ Module.finrank F C) (hCg : ∀ y ∈ C, g y ∈ C) :
    ∃ G : OFrame Q, G.span ≤ C ∧ ∀ x ∈ G.span, g x ∈ G.span := by
  obtain ⟨v, hvC, hQv, hv0, hvne⟩ := exists_singular_not_eigen h2 hodd hQ hg hC h3
  obtain ⟨y', hy'C, hy'⟩ := hC.exists_polar_ne_zero hvC hv0
  have hhC : (polar Q v y')⁻¹ • y' ∈ C := C.smul_mem _ hy'C
  have hvh : polar Q v ((polar Q v y')⁻¹ • y') = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hy']
  let P := HypPair.ofPolarEqOne hQv hvh
  have hPe : P.e ∈ C := hvC
  have hPf : P.f ∈ C := C.sub_mem hhC (C.smul_mem _ hvC)
  have hN : PolarNondegOn Q (C ⊓ P.perp) := hC.inf_perp P hPe hPf
  have hgv0 : polar Q (g v) v = 0 := by rw [polar_comm]; exact hg.polar_self_g h2 v
  obtain ⟨z₀, hz₀, hz₀ne⟩ : ∃ z₀ ∈ C ⊓ P.perp, polar Q (g v) z₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hn : P.proj (g v) ∈ C ⊓ P.perp := by
      refine ⟨?_, P.proj_mem_perp _⟩
      rw [HypPair.proj]
      exact C.sub_mem (C.sub_mem (hCg v hvC) (C.smul_mem _ hPe)) (C.smul_mem _ hPf)
    have hn0 : P.proj (g v) = 0 := by
      apply hN _ hn
      intro z hz
      obtain ⟨-, hzP⟩ := Submodule.mem_inf.mp hz
      obtain ⟨hze, hzf⟩ := HypPair.mem_perp.mp hzP
      rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, hcon z hz,
        hze, hzf]
      ring
    apply hvne (polar Q (g v) P.f)
    have := P.eq_add_proj (g v)
    rw [hn0, add_zero] at this
    have hpe : polar Q (g v) P.e = 0 := hgv0
    rw [hpe, zero_smul, add_zero] at this
    exact this
  set s := polar Q (g v) P.f with hs
  set z : V := (-s * (polar Q (g v) z₀)⁻¹) • z₀ with hzdef
  have hzmem : z ∈ C ⊓ P.perp := (C ⊓ P.perp).smul_mem _ hz₀
  have hgz : polar Q (g v) z = -s := by
    rw [hzdef, polar_smul_right_eq]
    field_simp
  obtain ⟨hzC, hzP⟩ := Submodule.mem_inf.mp hzmem
  obtain ⟨hze, hzf⟩ := HypPair.mem_perp.mp hzP
  have hh1 : polar Q v (P.f + z) = 1 := by
    rw [polar_add_right]
    have : polar Q v P.f = 1 := P.polar_ef
    rw [this, show polar Q v z = 0 from hze]
    ring
  let P₁ := HypPair.ofPolarEqOne hQv hh1
  have hP₁f : P₁.f ∈ C := C.sub_mem (C.add_mem hPf hzC) (C.smul_mem _ hvC)
  have hgy : polar Q (g v) P₁.f = 0 := by
    show polar Q (g v) ((P.f + z) - Q (P.f + z) • v) = 0
    rw [polar_sub_right, polar_smul_right_eq, polar_add_right, hgz, hgv0]
    ring
  have hc0 := hg.ne
  have hQ₂e : Q (g v) = 0 := by rw [hg.Q_g h2, hQv, mul_zero]
  have hQ₂f : Q ((-c⁻¹) • g P₁.f) = 0 := by
    rw [QuadraticMap.map_smul, hg.Q_g h2, P₁.Q_f, mul_zero, smul_zero]
  have hpol : polar Q (g v) ((-c⁻¹) • g P₁.f) = 1 := by
    rw [polar_smul_right_eq, hg.polar_g_g]
    have h1 : polar Q v P₁.f = 1 := P₁.polar_ef
    rw [h1]
    field_simp
  let P₂ : HypPair Q := ⟨g v, (-c⁻¹) • g P₁.f, hQ₂e, hQ₂f, hpol⟩
  have hvgy : polar Q v (g P₁.f) = 0 := by
    have := hg.skew v P₁.f
    rw [hgy] at this
    linear_combination this
  have horth : P₁.Orth P₂ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show polar Q v (g v) = 0
      exact hg.polar_self_g h2 v
    · show polar Q v ((-c⁻¹) • g P₁.f) = 0
      rw [polar_smul_right_eq, hvgy, mul_zero]
    · show polar Q P₁.f (g v) = 0
      rw [polar_comm]
      exact hgy
    · show polar Q P₁.f ((-c⁻¹) • g P₁.f) = 0
      rw [polar_smul_right_eq, hg.polar_self_g h2, mul_zero]
  let G : OFrame Q := ⟨P₁, P₂, horth⟩
  refine ⟨G, span_le_of_gens hvC hP₁f (hCg v hvC) (C.smul_mem _ (hCg _ hP₁f)), ?_⟩
  have g1 : g G.e₁ = G.e₂ := rfl
  have g2 : g G.f₁ = (-c) • G.f₂ := by
    show g P₁.f = (-c) • ((-c⁻¹) • g P₁.f)
    rw [smul_smul]
    field_simp
    simp
  have g3 : g G.e₂ = c • G.e₁ := hg.sq v
  have g4 : g G.f₂ = -G.f₁ := by
    show g ((-c⁻¹) • g P₁.f) = -P₁.f
    rw [map_smul, hg.sq, smul_smul]
    field_simp
    simp
  rintro _ ⟨X, rfl⟩
  rw [Frame.incl_apply]
  simp only [map_add, map_smul, g1, g2, g3, g4]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  · exact G.span.smul_mem _ G.e₂_mem_span
  · exact G.span.smul_mem _ (G.span.smul_mem _ G.f₂_mem_span)
  · exact G.span.smul_mem _ (G.span.smul_mem _ G.e₁_mem_span)
  · exact G.span.smul_mem _ (G.span.neg_mem G.f₁_mem_span)

end Frames

section Minus

open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam)

variable {F : Type} [Field F] [Finite F]

theorem false_of_skewRoot_quadMinus_four (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) {b c₀ : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) (h4 : 4 ≤ Nat.card F)
    {g : (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F) →ₗ[F]
      (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F)} {c : F}
    (hg : SkewRoot (quadMinus (3 + 1) F b c₀) g c) : False := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite (n := 3 + 1) (K := F) hirr
  have hdim : Module.finrank F (Fin (3 + 1 - 1) ⊕ Fin (3 + 1 - 1) ⊕ Fin 2 → F) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  obtain ⟨G₁, -, hG₁g⟩ := exists_gstable_frame h2 hodd hQ hg (C := ⊤) (polarNondegOn_top hQ)
    (by rw [finrank_top]; omega) (fun _ _ => Submodule.mem_top)
  have hC1 := CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ G₁
  have hd1 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four G₁
  have hC1g : ∀ y ∈ G₁.perp, g y ∈ G₁.perp := by
    intro y hy
    rw [Frame.mem_perp_iff_forall_incl] at hy ⊢
    intro X
    obtain ⟨X', hX'⟩ := hG₁g _ ⟨X, rfl⟩
    rw [hg.skew, ← hX', hy X', neg_zero]
  obtain ⟨G₂, hG₂C, -⟩ := exists_gstable_frame h2 hodd hQ hg hC1 (by omega) hC1g
  obtain ⟨o01, o02, o03, o04⟩ := orth_pairs_of_span_le_perp hG₂C
  let P : Fin 4 → HypPair (quadMinus (3 + 1) F b c₀) := ![G₁.P, G₁.P', G₂.P, G₂.P']
  have hP : ∀ i j, i ≠ j → (P i).Orth (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [P] <;>
      first
      | exact absurd rfl hij
      | exact G₁.orth | exact G₁.orth.symm | exact G₂.orth | exact G₂.orth.symm
      | exact o01 | exact o01.symm | exact o02 | exact o02.symm
      | exact o03 | exact o03.symm | exact o04 | exact o04.symm
  exact false_of_isHypFam_quadMinus (m := 3) h2 hirr h4 _ (isHypFam_of_pairs P hP)

end Minus

end CFSG.ClassicalInvolution.RouteD.Exotic
