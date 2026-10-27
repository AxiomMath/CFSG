module

public import CFSG.LargeExtraspecial.S3cTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_le_of_forall_mem {P : Submodule (ZMod 2) V} (S : Submodule (ZMod 2) P)
    (T : Submodule (ZMod 2) V) [FiniteDimensional (ZMod 2) T]
    (h : ∀ x ∈ S, (x : V) ∈ T) : finrank (ZMod 2) S ≤ finrank (ZMod 2) T := by
  rw [← Submodule.finrank_map_subtype_eq P S]
  exact Submodule.finrank_mono (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

noncomputable def perpSpan (q : QuadraticForm (ZMod 2) V) (a : V)
    (L : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V where
  carrier := {x | polar q a x = 0 ∧ ∀ s ∈ L, s x - x ∈ (ZMod 2) ∙ a}
  add_mem' {x y} hx hy := ⟨by rw [polar_add_right, hx.1, hy.1, add_zero], fun s hs => by
    rw [map_add, show s x + s y - (x + y) = (s x - x) + (s y - y) by abel]
    exact Submodule.add_mem _ (hx.2 s hs) (hy.2 s hs)⟩
  zero_mem' := ⟨polar_zero_right _ _, fun s _ => by simp⟩
  smul_mem' c x hx := ⟨by rw [polar_smul_right, hx.1, smul_zero], fun s hs => by
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (hx.2 s hs)⟩

namespace TransvectionConfig

variable {q : QuadraticForm (ZMod 2) V} {a : V} {W : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)} (C : TransvectionConfig q a W L)
include C

noncomputable def rad (v : V) : Submodule (ZMod 2) C.K where
  carrier := {φ | ∀ ψ χ, C.theta v φ ψ χ = 0}
  add_mem' {φ φ'} hφ hφ' ψ χ := by
    rw [(C.isAltTrilin_theta v).add_left, hφ ψ χ, hφ' ψ χ, add_zero]
  zero_mem' ψ χ := by
    have h := (C.isAltTrilin_theta v).add_left 0 0 ψ χ
    rw [add_zero] at h
    exact left_eq_add.mp h
  smul_mem' c φ hφ ψ χ := by
    rw [map_smul_of_map_add_zmod2 (f := fun φ => C.theta v φ ψ χ)
      (fun φ φ' => (C.isAltTrilin_theta v).add_left φ φ' ψ χ), hφ ψ χ, mul_zero]

theorem mem_rad {v : V} {φ : C.K} : φ ∈ C.rad v ↔ ∀ ψ χ, C.theta v φ ψ χ = 0 := Iff.rfl

theorem formOf_a {x : V} (hx : polar q a x = 0) : (q.polarBilin x ∘ₗ W.subtype) ⟨a, C.haW⟩ = 0 := by
  simp [polarBilin_apply_apply, polar_comm q x a, hx]

noncomputable def formMap (P : Submodule (ZMod 2) V) (hP : ∀ x ∈ P, polar q a x = 0) :
    P →ₗ[ZMod 2] C.K where
  toFun x := C.formK (q.polarBilin (x : V) ∘ₗ W.subtype) (C.formOf_a (hP x x.2))
  map_add' x y := C.lineW.linearMap_qext (LinearMap.ext fun w => by
    simp [C.formK_apply, polarBilin_apply_apply])
  map_smul' c x := C.lineW.linearMap_qext (LinearMap.ext fun w => by
    simp [C.formK_apply, polarBilin_apply_apply])

theorem formMap_apply (P : Submodule (ZMod 2) V) (hP : ∀ x ∈ P, polar q a x = 0) (x : P)
    (w : W) : C.formMap P hP x (Submodule.Quotient.mk w) = polar q (x : V) (w : V) := by
  simp [formMap, C.formK_apply, polarBilin_apply_apply]

theorem polar_sOf_sub {v : V} (hv : polar q a v = 1) (φ : C.K) (w : W) :
    polar q (C.sOf φ v - v) (w : V) = φ (Submodule.Quotient.mk w) := by
  rw [C.polar_sub_left (C.sOf_mem φ), C.sOf_apply, add_sub_cancel_left, polar_smul_right,
    polar_comm q v a, hv, smul_eq_mul, mul_one]

theorem sub_sOf_formOf_mem {v : V} (hv : polar q a v = 1) {x : V} (hx : polar q a x = 0) :
    x - (C.sOf (C.formK _ (C.formOf_a hx)) v - v) ∈ W := by
  refine C.perp_le _ fun w hw => ?_
  rw [QuadraticMap.polar_sub_left, show w = ((⟨w, hw⟩ : W) : V) from rfl, C.polar_sOf_sub hv,
    C.formK_apply]
  simp [polarBilin_apply_apply]

theorem sub_eq_zero_of_mem_span {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) {x : V}
    (hx : x ∈ (ZMod 2) ∙ a) : s x - x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, C.fix s hs, sub_self]

theorem mem_span_of_forall_K {w : V} (hw : w ∈ W)
    (h : ∀ φ : C.K, φ (Submodule.Quotient.mk ⟨w, hw⟩) = 0) : w ∈ (ZMod 2) ∙ a := by
  have h0 : (Submodule.Quotient.mk ⟨w, hw⟩ : W ⧸ C.lineW) = 0 :=
    (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.Quotient.mk_eq_zero C.lineW).mp h0)
  exact Submodule.mem_span_singleton.mpr ⟨c, by simpa using congrArg Subtype.val hc⟩

theorem exists_K_apply_eq_one [FiniteDimensional (ZMod 2) V] (hW2 : 2 ≤ finrank (ZMod 2) W) :
    ∃ (w : W) (φ : C.K), φ (Submodule.Quotient.mk w) = 1 := by
  by_contra h
  push Not at h
  have hall : ∀ w : W, (w : V) ∈ (ZMod 2) ∙ a := fun w =>
    C.mem_span_of_forall_K w.2 fun φ => (zmod2_eq_zero_or_eq_one _).resolve_right (h w φ)
  have hle : W ≤ (ZMod 2) ∙ a := fun w hw => hall ⟨w, hw⟩
  have := Submodule.finrank_mono hle
  rw [finrank_span_singleton C.ha0] at this
  omega

theorem polar_a_of_fix [FiniteDimensional (ZMod 2) V] (hW2 : 2 ≤ finrank (ZMod 2) W) {x : V}
    (hx : ∀ s ∈ L, s x = x) : polar q a x = 0 := by
  obtain ⟨w, φ, hφw⟩ := C.exists_K_apply_eq_one hW2
  have h1 : C.sOf φ w - w = a := by rw [C.sOf_apply, hφw, one_smul, add_sub_cancel_left]
  rw [polar_comm, ← h1, ← C.polar_sub_left (C.sOf_mem φ), hx _ (C.sOf_mem φ), sub_self,
    polar_zero_left]

theorem finrank_fix_le [FiniteDimensional (ZMod 2) V] {v : V} (hv : polar q a v = 1)
    (hW2 : 2 ≤ finrank (ZMod 2) W) (F : Submodule (ZMod 2) V)
    (hF : ∀ x, x ∈ F ↔ ∀ s ∈ L, s x = x) :
    finrank (ZMod 2) F ≤ finrank (ZMod 2) (C.rad v) + 1 := by
  have hFa : ∀ x ∈ F, polar q a x = 0 := fun x hx => C.polar_a_of_fix hW2 ((hF x).mp hx)
  set Ψ := C.formMap F hFa with hΨ
  have hrange : LinearMap.range Ψ ≤ C.rad v := by
    rintro _ ⟨x, rfl⟩ ψ χ
    have hx := (hF x).mp x.2
    have hw := C.sub_sOf_formOf_mem hv (hFa x x.2)
    set y := C.sOf (C.formK _ (C.formOf_a (hFa x x.2))) v - v with hy
    have hΨx : Ψ x = C.formK _ (C.formOf_a (hFa x x.2)) := rfl
    rw [hΨx, (C.isAltTrilin_theta v).swap₁₂, theta_def, ← hy]
    have e : C.sOf ψ y - y = -(C.sOf ψ ((x : V) - y) - ((x : V) - y)) := by
      rw [map_sub (C.sOf ψ) (x : V) y, hx _ (C.sOf_mem ψ)]
      abel
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.onW _ (C.sOf_mem ψ) _ hw)
    rw [e, ← hc, polar_neg_right, polar_smul_right, polar_comm,
      C.polar_a_sub (C.sOf_mem χ) v, smul_zero, neg_zero]
  have hker : ∀ x ∈ LinearMap.ker Ψ, ((x : F) : V) ∈ (ZMod 2) ∙ a := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxW : (x : V) ∈ W := C.perp_le _ fun w hw => by
      have := LinearMap.congr_fun hx (Submodule.Quotient.mk ⟨w, hw⟩)
      rwa [hΨ, C.formMap_apply] at this
    refine C.mem_span_of_forall_K hxW fun φ => ?_
    have h1 := (hF x).mp x.2 _ (C.sOf_mem φ)
    rw [show (x : V) = ((⟨x, hxW⟩ : W) : V) from rfl, C.sOf_apply] at h1
    rcases zmod2_eq_zero_or_eq_one (φ (Submodule.Quotient.mk ⟨x, hxW⟩)) with h | h
    · exact h
    · rw [h, one_smul] at h1
      exact absurd (add_eq_left.mp h1) C.ha0
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (V := F) (V₂ := C.K) Ψ
  have h2 := Submodule.finrank_mono hrange
  have h3 : finrank (ZMod 2) (LinearMap.ker Ψ) ≤ 1 := by
    have := finrank_le_of_forall_mem (LinearMap.ker Ψ) _ hker
    rwa [finrank_span_singleton C.ha0] at this
  omega

theorem W_le_Pa : W ≤ perpSpan q a L := fun w hw =>
  ⟨C.polar_W C.haW hw, fun s hs => C.onW s hs w hw⟩

theorem sOf_sub_mem_Pa [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {v : V} (hv : polar q a v = 1) {φ : C.K} (hφ : φ ∈ C.rad v) :
    C.sOf φ v - v ∈ perpSpan q a L := by
  have hN := C.mem_pointRadical_of_theta_eq_zero hq hv hφ
  refine ⟨C.polar_a_sub (C.sOf_mem φ) v, fun t ht => ?_⟩
  have e : t (C.sOf φ v - v) - (C.sOf φ v - v) = C.sOf φ (t v - v) - (t v - v) := by
    rw [map_sub, map_sub, C.apply_comm ht (C.sOf_mem φ)]
    abel
  rw [e]
  exact (mem_pointRadical.mp hN).2.2.1 _ (C.polar_a_sub ht v)

theorem mu_add {v : V} {x : V} (hx : x ∈ perpSpan q a L) (φ φ' : C.K) :
    polar q v (C.sOf (φ + φ') x - x) =
      polar q v (C.sOf φ x - x) + polar q v (C.sOf φ' x - x) := by
  rw [C.sOf_add_sub, C.sub_eq_zero_of_mem_span (C.sOf_mem φ) (hx.2 _ (C.sOf_mem φ')),
    add_zero, polar_add_right]

@[expose] noncomputable def muBilin (v : V) : C.K →ₗ[ZMod 2] perpSpan q a L →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) (fun φ x => polar q v (C.sOf φ x - x))
    (fun φ φ' x => C.mu_add x.2 φ φ')
    (fun c φ x => by
      rw [smul_eq_mul]
      exact map_smul_of_map_add_zmod2 (f := fun φ => polar q v (C.sOf φ x - x))
        (C.mu_add x.2) c φ)
    (fun φ x y => by
      simp only [Submodule.coe_add, map_add]
      rw [show C.sOf φ x + C.sOf φ y - (x + y) = (C.sOf φ x - x) + (C.sOf φ y - y) by abel,
        polar_add_right])
    (fun c φ x => by
      simp only [Submodule.coe_smul, map_smul]
      rw [← smul_sub, polar_smul_right])

theorem muBilin_apply (v : V) (φ : C.K) (x : perpSpan q a L) :
    C.muBilin v φ x = polar q v (C.sOf φ x - x) := rfl

theorem le_finrank_fix [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {v : V} (hv : polar q a v = 1) (F : Submodule (ZMod 2) V)
    (hF : ∀ x, x ∈ F ↔ ∀ s ∈ L, s x = x) :
    finrank (ZMod 2) (C.rad v) + 1 ≤ finrank (ZMod 2) F := by
  set Ψ := C.formMap (perpSpan q a L) (fun x hx => hx.1) with hΨ
  have hrange : C.rad v ≤ LinearMap.range Ψ := by
    intro φ hφ
    refine ⟨⟨_, C.sOf_sub_mem_Pa hq hv hφ⟩, C.lineW.linearMap_qext (LinearMap.ext fun w => ?_)⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [hΨ, C.formMap_apply]
    exact C.polar_sOf_sub hv φ w
  have hker : W.comap (perpSpan q a L).subtype ≤ LinearMap.ker Ψ := by
    intro x hx
    rw [LinearMap.mem_ker]
    refine C.lineW.linearMap_qext (LinearMap.ext fun w => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [hΨ, C.formMap_apply]
    exact C.polar_W hx w.2
  have hWdim : finrank (ZMod 2) (W.comap (perpSpan q a L).subtype) = finrank (ZMod 2) W :=
    (Submodule.comapSubtypeEquivOfLe C.W_le_Pa).finrank_eq
  have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) (V := perpSpan q a L)
    (V₂ := C.K) Ψ
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_mono hker
  set μ : perpSpan q a L →ₗ[ZMod 2] Module.Dual (ZMod 2) C.K := (C.muBilin v).flip with hμ
  have hkerμ : ∀ x ∈ LinearMap.ker μ, ((x : perpSpan q a L) : V) ∈ F := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (hF _).mpr fun t ht => ?_
    obtain ⟨φ, rfl⟩ := C.exists_sOf_eq ht
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (x.2.2 _ (C.sOf_mem φ))
    have h0 : polar q v (C.sOf φ x - x) = 0 := by
      have := LinearMap.congr_fun hx φ
      rwa [hμ, LinearMap.flip_apply, C.muBilin_apply] at this
    rw [← hc, polar_smul_right, polar_comm, hv, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul] at hc
    exact sub_eq_zero.mp hc.symm
  have h4 := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2)
    (V := perpSpan q a L)
    (V₂ := Module.Dual (ZMod 2) C.K) μ
  have h5 : finrank (ZMod 2) (LinearMap.range μ) ≤ finrank (ZMod 2) C.K := by
    have := Submodule.finrank_le (LinearMap.range μ)
    rwa [Subspace.dual_finrank_eq (K := ZMod 2) (V := C.K)] at this
  have h6 := finrank_le_of_forall_mem (LinearMap.ker μ) F hkerμ
  have h7 := C.finrank_K_add_one
  omega

theorem finrank_fix_eq [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {v : V} (hv : polar q a v = 1) (hW2 : 2 ≤ finrank (ZMod 2) W) (F : Submodule (ZMod 2) V)
    (hF : ∀ x, x ∈ F ↔ ∀ s ∈ L, s x = x) :
    finrank (ZMod 2) F = finrank (ZMod 2) (C.rad v) + 1 :=
  le_antisymm (C.finrank_fix_le hv hW2 F hF) (C.le_finrank_fix hq hv F hF)

end TransvectionConfig

end CFSG.LargeExtraspecial
