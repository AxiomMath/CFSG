module

public import CFSG.LieType.ChevTwo.OppCl.Defs
import CFSG.LieType.ChevTwo.OppCl.Toolkit
import CFSG.LieType.ChevTwo.OppCl.FormsCasesBase
import CFSG.LieType.ChevTwo.OppCl.FormsCasesSplit
import CFSG.LieType.ChevTwo.OppCl.FormsCasesCtx

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section ZDual

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

theorem split3_kernel_M {Φ : ReflForm F V} {TS : Submodule F V → Prop}
    {W M W' : Submodule F V} (hS : Split3 Φ TS W M W') :
    ∀ u ∈ M, (∀ m' ∈ M, Φ.β m' u = 0) → u = 0 := by
  intro u hu hu0
  apply Φ.nondeg
  intro v
  obtain ⟨w, hw, m', hm', w', hw', rfl⟩ := split3_decomp hS v
  have h1 : Φ.β u w = 0 := Φ.refl _ _ (hS.perp_WM w hw u hu)
  have h2 : Φ.β u m' = 0 := Φ.refl _ _ (hu0 m' hm')
  have h3 : Φ.β u w' = 0 := hS.perp_MW' u hu w' hw'
  rw [Φ.add_right, Φ.add_right, h1, h2, h3, add_zero, add_zero]

theorem vec_add_self (K : Type) [Field K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
    (u : W) : u + u = 0 := by
  rw [← two_smul K u, CharTwo.two_eq_zero, zero_smul]

theorem zdual_abs {Φ : ReflForm F V} {TS : Submodule F V → Prop} {Sing : V → Prop} (E2 : Prop)
    {W M W' : Submodule F V} (hS : Split3 Φ TS W M W') (hW : Φ.IsTotallyIsotropic W)
    (hW' : Φ.IsTotallyIsotropic W') (hsing : ∀ v ∈ W, Sing v) (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (Rh : Subgroup (Equiv.Perm V)) (hs : Rh ≤ semilinGroup F V)
    (hiso : ∀ r ∈ Rh, SemiIso Φ r) (hR : IsPGroup p Rh)
    (hW'inv : ∀ r ∈ Rh, ∀ v ∈ W', r v ∈ W') (c : V →ₗ[F] V)
    (hcc : ∀ r ∈ Rh, ∀ v, r (c v) = c (r v)) (hcW : ∀ v, c v ∈ W)
    (hc0 : ∀ v ∈ W ⊔ M, c v = 0) (hsa : ∀ u v, Φ.β (c u) v = Φ.β u (c v))
    (hne : ∃ w ∈ W', c w ≠ 0) (hdiag : E2 ∨ ∀ s ∈ W', Sing (c s) → Φ.β s (c s) = 0) :
    ∃ c' : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (c' v) = c' (r v)) ∧ (∀ v, c' v ∈ W') ∧
      (∀ v ∈ M ⊔ W', c' v = 0) ∧ (∀ u v, Φ.β (c' u) v = Φ.β u (c' v)) ∧
      (∃ w ∈ W, c' w ≠ 0) ∧ (E2 ∨ ∀ u, Φ.β u (c' u) = 0) := by
  classical
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  obtain ⟨K', hK'mem⟩ : ∃ K' : Submodule F V, ∀ v, v ∈ K' ↔ v ∈ W' ∧ c v = 0 :=
    ⟨W' ⊓ LinearMap.ker c, fun v => by simp [Submodule.mem_inf, LinearMap.mem_ker]⟩
  have hK'inv : ∀ r ∈ Rh, ∀ v ∈ K', r v ∈ K' := by
    intro r hr v hv
    obtain ⟨hv1, hv2⟩ := (hK'mem v).mp hv
    refine (hK'mem _).mpr ⟨hW'inv r hr v hv1, ?_⟩
    rw [← hcc r hr v, hv2, semilin_zero (hs hr)]
  obtain ⟨C₀, hC₀, hC₀inv⟩ := exists_invariant_compl p hp2 Rh hs hR K' hK'inv
  obtain ⟨W₁', hW₁'mem⟩ : ∃ W₁' : Submodule F V, ∀ v, v ∈ W₁' ↔ v ∈ W' ∧ v ∈ C₀ :=
    ⟨W' ⊓ C₀, fun v => Submodule.mem_inf⟩
  have hW₁'W' : ∀ v ∈ W₁', v ∈ W' := fun v hv => ((hW₁'mem v).mp hv).1
  have hW₁'inv : ∀ r ∈ Rh, ∀ v ∈ W₁', r v ∈ W₁' := fun r hr v hv =>
    (hW₁'mem _).mpr ⟨hW'inv r hr v ((hW₁'mem v).mp hv).1, hC₀inv r hr v ((hW₁'mem v).mp hv).2⟩
  have hdec : ∀ w' ∈ W', ∃ k ∈ K', ∃ s ∈ W₁', w' = k + s := by
    intro w' hw'
    have hmem : w' ∈ K' ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, γ, hγ, hkγ⟩ := Submodule.mem_sup.mp hmem
    refine ⟨k, hk, γ, (hW₁'mem γ).mpr ⟨?_, hγ⟩, hkγ.symm⟩
    have : γ = w' - k := by rw [← hkγ]; abel
    rw [this]
    exact sub_mem hw' ((hK'mem k).mp hk).1
  have hinjc : ∀ s ∈ W₁', c s = 0 → s = 0 := by
    intro s hs0 hc
    have h1 : s ∈ K' := (hK'mem s).mpr ⟨hW₁'W' s hs0, hc⟩
    exact Submodule.disjoint_def.mp hC₀.disjoint s h1 ((hW₁'mem s).mp hs0).2
  have hrange : ∀ a ∈ LinearMap.range c, ∃ s ∈ W₁', c s = a := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨w₀, hw₀, μ, hμ, w', hw', rfl⟩ := split3_decomp hS v
    obtain ⟨k, hk, s, hs', rfl⟩ := hdec w' hw'
    refine ⟨s, hs', ?_⟩
    have h1 : c (w₀ + μ) = 0 := hc0 _ (Submodule.add_mem_sup hw₀ hμ)
    have h2 : c k = 0 := ((hK'mem k).mp hk).2
    have h3 : c (w₀ + μ + (k + s)) = c s := by
      rw [map_add c (w₀ + μ) (k + s), h1, map_add c k s, h2, zero_add, zero_add]
    exact h3.symm
  let f : W₁' →ₗ[F] LinearMap.range c :=
    LinearMap.codRestrict (LinearMap.range c) (c.domRestrict W₁') (fun s => ⟨(s : V), rfl⟩)
  have hfval : ∀ s : W₁', ((f s : LinearMap.range c) : V) = c s := fun s => rfl
  have hfinj : Function.Injective f := by
    intro s t hst
    have h1 : c (s : V) = c (t : V) := by
      rw [← hfval s, ← hfval t, hst]
    have h2 : c ((s : V) - t) = 0 := by rw [map_sub, h1, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hinjc _ (sub_mem s.2 t.2) h2))
  have hfsurj : Function.Surjective f := by
    intro a
    obtain ⟨s, hs', hcs⟩ := hrange a a.2
    exact ⟨⟨s, hs'⟩, Subtype.ext hcs⟩
  let e : W₁' ≃ₗ[F] LinearMap.range c := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  have hev : ∀ s : W₁', ((e s : LinearMap.range c) : V) = c s := fun s => rfl
  have hW₁W : ∀ a ∈ LinearMap.range c, a ∈ W := by
    rintro _ ⟨v, rfl⟩
    exact hcW v
  have hW₁inv : ∀ r ∈ Rh, ∀ v ∈ LinearMap.range c, r v ∈ LinearMap.range c := by
    rintro r hr _ ⟨v, rfl⟩
    exact ⟨r v, (hcc r hr v).symm⟩
  have hD₁inv : ∀ r ∈ Rh, ∀ v ∈ Φ.perp W₁', r v ∈ Φ.perp W₁' :=
    perp_invariant Φ Rh hiso W₁' hW₁'inv
  have hMW'D : ∀ v ∈ M ⊔ W', v ∈ Φ.perp W₁' := by
    intro v hv s hs
    obtain ⟨μ, hμ, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    have hs' : s ∈ W' := hW₁'W' s hs
    have h1 : Φ.β s μ = 0 := Φ.refl _ _ (hS.perp_MW' μ hμ s hs')
    have h2 : Φ.β s w' = 0 := (Φ.mem_perp.mp (hW' hw')) s hs'
    rw [Φ.add_right, h1, h2, add_zero]
  have hdisj : Disjoint (LinearMap.range c) (Φ.perp W₁') := by
    rw [Submodule.disjoint_def]
    intro a ha haD
    obtain ⟨s₀, hs₀, hcs₀⟩ := hrange a ha
    have haW : a ∈ W := hW₁W a ha
    apply Φ.nondeg
    intro v
    obtain ⟨w₀, hw₀, μ, hμ, w', hw', rfl⟩ := split3_decomp hS v
    obtain ⟨k, hk, s, hs', rfl⟩ := hdec w' hw'
    have h1 : Φ.β a w₀ = 0 := (Φ.mem_perp.mp (hW hw₀)) a haW
    have h2 : Φ.β a μ = 0 := hS.perp_WM a haW μ hμ
    have h3 : Φ.β a k = 0 := by
      rw [← hcs₀, hsa, ((hK'mem k).mp hk).2, Φ.β_zero_right]
    have h4 : Φ.β a s = 0 := Φ.refl _ _ ((Φ.mem_perp.mp haD) s hs')
    rw [Φ.add_right, Φ.add_right, Φ.add_right, h1, h2, h3, h4]
    simp
  have hdim : Module.finrank F (LinearMap.range c) = Module.finrank F W₁' :=
    (LinearEquiv.finrank_eq e).symm
  have hsup : LinearMap.range c ⊔ Φ.perp W₁' = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range c) (Φ.perp W₁')
    rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at h1
    have h2 := Φ.finrank_perp W₁'
    omega
  have hcompl : IsCompl (LinearMap.range c) (Φ.perp W₁') := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  obtain ⟨pr, hpr_left, hpr_right⟩ : ∃ pr : V →ₗ[F] LinearMap.range c,
      (∀ a : LinearMap.range c, pr (a : V) = a) ∧ (∀ d ∈ Φ.perp W₁', pr d = 0) :=
    ⟨Submodule.projectionOnto _ _ hcompl, fun a => Submodule.projectionOnto_apply_left hcompl a,
      fun d hd => Submodule.projectionOnto_apply_of_mem_right hcompl hd⟩
  have hdecomp : ∀ v : V, ∃ a : LinearMap.range c, ∃ d ∈ Φ.perp W₁', v = (a : V) + d ∧
      pr v = a := by
    intro v
    have hv : v ∈ LinearMap.range c ⊔ Φ.perp W₁' := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨a, ha⟩, d, hd, rfl, ?_⟩
    rw [map_add, hpr_left ⟨a, ha⟩, hpr_right d hd, add_zero]
  obtain ⟨c', hc'⟩ : ∃ c' : V →ₗ[F] V, ∀ v, c' v = ((e.symm (pr v) : W₁') : V) :=
    ⟨W₁'.subtype.comp (e.symm.toLinearMap.comp pr), fun v => rfl⟩
  have hc'mem : ∀ v, c' v ∈ W₁' := fun v => by rw [hc']; exact (e.symm (pr v)).2
  have hcc' : ∀ v, c (c' v) = (pr v : V) := by
    intro v
    rw [hc', ← hev, e.apply_symm_apply]
  have hpr_eq : ∀ r ∈ Rh, ∀ v, (pr (r v) : V) = r (pr v : V) := by
    intro r hr v
    obtain ⟨a, d, hd, hv, hpra⟩ := hdecomp v
    have hra : r (a : V) ∈ LinearMap.range c := hW₁inv r hr _ a.2
    have hrd : r d ∈ Φ.perp W₁' := hD₁inv r hr d hd
    have h1 : r v = r (a : V) + r d := by rw [hv, (hs hr).1]
    have h2 : pr (r v) = ⟨r (a : V), hra⟩ := by
      rw [h1, map_add]
      have : pr (r (a : V)) = ⟨r (a : V), hra⟩ := hpr_left ⟨r (a : V), hra⟩
      rw [this, hpr_right _ hrd, add_zero]
    rw [h2, hpra]
  have hP1 : ∀ r ∈ Rh, ∀ v, r (c' v) = c' (r v) := by
    intro r hr v
    have hs1 : r (c' v) ∈ W₁' := hW₁'inv r hr _ (hc'mem v)
    have hs2 : c' (r v) ∈ W₁' := hc'mem _
    have h1 : c (r (c' v)) = c (c' (r v)) := by
      rw [← hcc r hr, hcc', hcc', hpr_eq r hr v]
    have h2 : c (r (c' v) - c' (r v)) = 0 := by rw [map_sub, h1, sub_self]
    exact sub_eq_zero.mp (hinjc _ (sub_mem hs1 hs2) h2)
  have hP3 : ∀ v ∈ M ⊔ W', c' v = 0 := by
    intro v hv
    have : pr v = 0 := hpr_right v (hMW'D v hv)
    rw [hc', this, map_zero]
    rfl
  have hP4 : ∀ u v, Φ.β (c' u) v = Φ.β u (c' v) := by
    intro u v
    obtain ⟨a, d, hd, hu, hpa⟩ := hdecomp u
    obtain ⟨b, e', he', hv, hpb⟩ := hdecomp v
    have L : Φ.β (c' u) v = Φ.β (c' u) (c (c' v)) := by
      have h0 : Φ.β (c' u) e' = 0 := (Φ.mem_perp.mp he') (c' u) (hc'mem u)
      calc Φ.β (c' u) v = Φ.β (c' u) ((b : V) + e') := by rw [← hv]
        _ = Φ.β (c' u) (c (c' v)) := by rw [Φ.add_right, h0, add_zero, hcc' v, hpb]
    have R : Φ.β u (c' v) = Φ.β (c (c' u)) (c' v) := by
      have h0 : Φ.β d (c' v) = 0 := Φ.refl _ _ ((Φ.mem_perp.mp hd) (c' v) (hc'mem v))
      calc Φ.β u (c' v) = Φ.β ((a : V) + d) (c' v) := by rw [← hu]
        _ = Φ.β (c (c' u)) (c' v) := by rw [Φ.add_left, h0, add_zero, hcc' u, hpa]
    rw [L, R]
    exact (hsa (c' u) (c' v)).symm
  have hP5 : ∃ w ∈ W, c' w ≠ 0 := by
    obtain ⟨w', hw', hcw'⟩ := hne
    have ha : c w' ∈ LinearMap.range c := ⟨w', rfl⟩
    refine ⟨c w', hcW w', fun h0 => hcw' ?_⟩
    have h1 : pr (c w') = ⟨c w', ha⟩ := hpr_left ⟨c w', ha⟩
    have h2 : c (c' (c w')) = c w' := by rw [hcc', h1]
    rw [h0, map_zero] at h2
    exact h2.symm
  have hP6 : E2 ∨ ∀ u, Φ.β u (c' u) = 0 := by
    rcases hdiag with h | h
    · exact Or.inl h
    · right
      intro u
      obtain ⟨a, d, hd, hu, hpa⟩ := hdecomp u
      have hsmem := hc'mem u
      have h0 : Φ.β d (c' u) = 0 := Φ.refl _ _ ((Φ.mem_perp.mp hd) (c' u) hsmem)
      have h1 : Φ.β u (c' u) = Φ.β (c (c' u)) (c' u) := by
        calc Φ.β u (c' u) = Φ.β ((a : V) + d) (c' u) := by rw [← hu]
          _ = Φ.β (c (c' u)) (c' u) := by rw [Φ.add_left, h0, add_zero, hcc' u, hpa]
      rw [h1, hsa]
      exact h (c' u) (hW₁'W' _ hsmem) (hsing _ (hcW _))
  exact ⟨c', hP1, fun v => hW₁'W' _ (hc'mem v), hP3, hP4, hP5, hP6⟩

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem caseZ_dual_core (hp2 : p ≠ 2) (C : RaiseCtx Φ Sing TS ρ p Rh X m M W')
    (hZtype : EA2 Φ Sing ρ ∨
      ∀ (h : H) (w : V), Sing (ρ h w - w) → Φ.β w (ρ h w - w) = 0)
    (x : H) (hx : x ∈ flagKernel ρ (isoCompletion Φ X m)) (hxc : CommR ρ Rh x)
    (hZ : (∀ w ∈ X m, ρ x w = w) ∧ (∀ y ∈ M, ρ x y = y) ∧ ∃ w ∈ W', ρ x w ≠ w) :
    ∃ c : V →ₗ[F] V, (∀ r ∈ Rh, ∀ v, r (c v) = c (r v)) ∧ (∀ v, c v ∈ W') ∧
      (∀ v ∈ M ⊔ W', c v = 0) ∧ (∀ u v, Φ.β (c u) v = Φ.β u (c v)) ∧ (∃ w ∈ X m, c w ≠ 0) ∧
      (EA2 Φ Sing ρ ∨ ∀ u, Φ.β u (c u) = 0) := by
  obtain ⟨hWfix, hMfix, w₀, hw₀, hw₀ne⟩ := hZ
  have hW := ctx_hW C
  have hW' := ctx_hW' C
  have hS := C.hsplit
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  obtain ⟨c, hcapp⟩ : ∃ c : V →ₗ[F] V, ∀ v, c v = ρ x v - v :=
    ⟨ρ x - 1, fun v => by simp⟩
  have hc0 : ∀ v ∈ X m ⊔ M, c v = 0 := by
    intro v hv
    obtain ⟨w, hw, μ, hμ, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hcapp, map_add, hWfix w hw, hMfix μ hμ, sub_self]
  have hinvapp : ∀ w, ρ x⁻¹ (ρ x w) = w := fun w => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hinvW : ∀ w ∈ X m, ρ x⁻¹ w = w := by
    intro w hw
    have := congrArg (ρ x⁻¹) (hWfix w hw)
    rw [hinvapp] at this
    exact this.symm
  have hcperp : ∀ v, c v ∈ Φ.perp (X m) := by
    intro v w hw
    rw [hcapp, Φ.β_sub_right]
    have h1 := beta_rho_inv C.hρ x⁻¹ w v
    rw [hinvW w hw, inv_inv] at h1
    rw [← h1, sub_self]
  have hcWM : ∀ v, c v ∈ X m ⊔ M := fun v => by
    rw [← split3_perp_W hS hW hW']
    exact hcperp v
  have hρρ : ∀ v, ρ x (ρ x v) = v := by
    intro v
    have h1 : ρ x (c v) = c v := by
      have := hc0 (c v) (hcWM v)
      rw [hcapp] at this
      exact sub_eq_zero.mp this
    have h2 : ρ x v = v + c v := by rw [hcapp]; abel
    have h3 : ρ x (ρ x v) = ρ x v + c v := by
      calc ρ x (ρ x v) = ρ x (v + c v) := by rw [← h2]
        _ = ρ x v + ρ x (c v) := by rw [map_add]
        _ = ρ x v + c v := by rw [h1]
    rw [h3, h2, add_assoc, vec_add_self F, add_zero]
  have hρinv : ∀ v, ρ x⁻¹ v = ρ x v := by
    intro v
    have := congrArg (ρ x⁻¹) (hρρ v)
    rw [hinvapp] at this
    exact this.symm
  have hsa : ∀ u v, Φ.β (c u) v = Φ.β u (c v) := by
    intro u v
    rw [hcapp, hcapp, Φ.β_sub_left, Φ.β_sub_right, beta_rho_inv C.hρ x u v, hρinv]
  have hcW : ∀ v, c v ∈ X m := by
    intro v
    obtain ⟨w, hw, μ, hμ, hcv⟩ := Submodule.mem_sup.mp (hcWM v)
    have hμ0 : μ = 0 := by
      refine split3_kernel_M hS μ hμ fun m' hm' => ?_
      have h1 : Φ.β (c v) m' = 0 := by
        rw [hsa, hc0 m' (Submodule.mem_sup_right hm'), Φ.β_zero_right]
      rw [← hcv, Φ.add_left, hS.perp_WM w hw m' hm', zero_add] at h1
      exact Φ.refl _ _ h1
    rw [← hcv, hμ0, add_zero]
    exact hw
  have hne : ∃ w ∈ W', c w ≠ 0 := ⟨w₀, hw₀, by rw [hcapp]; exact sub_ne_zero.mpr hw₀ne⟩
  have hdiag : EA2 Φ Sing ρ ∨ ∀ s ∈ W', Sing (c s) → Φ.β s (c s) = 0 := by
    rcases hZtype with h | h
    · exact Or.inl h
    · exact Or.inr fun s _ hs => by rw [hcapp] at hs ⊢; exact h x s hs
  have hcc : ∀ r ∈ Rh, ∀ v, r (c v) = c (r v) := fun r hr v => by
    rw [hcapp, hcapp, semilin_sub (C.hs hr), hxc r hr v]
  exact zdual_abs (EA2 Φ Sing ρ) hS hW hW' (fun v hv => C.hTSsing _ (C.hXts m) v hv) p hp2 Rh C.hs
    C.hiso C.hR C.hW'inv c hcc hcW hc0 hsa hne hdiag

end ZDual

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
