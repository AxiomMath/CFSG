module

public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S3cForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure TransvectionConfig (q : QuadraticForm (ZMod 2) V) (a : V) (W : Submodule (ZMod 2) V)
    (L : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop where
  haW : a ∈ W
  ha0 : a ≠ 0
  totallySingular : ∀ w ∈ W, q w = 0
  perp_le : ∀ x, (∀ w ∈ W, polar q x w = 0) → x ∈ W
  iso : ∀ s ∈ L, ∀ x, q (s x) = q x
  fix : ∀ s ∈ L, s a = a
  sq : ∀ s ∈ L, s * s = 1
  comm : ∀ s ∈ L, ∀ t ∈ L, s * t = t * s
  perp : ∀ s ∈ L, ∀ x, polar q a x = 0 → s x - x ∈ W
  onW : ∀ s ∈ L, ∀ w ∈ W, s w - w ∈ (ZMod 2) ∙ a
  trans : ∀ φ : W →ₗ[ZMod 2] ZMod 2, φ ⟨a, haW⟩ = 0 → ∃ s ∈ L, ∀ w : W, s w = w + φ w • a
  faithful : ∀ s ∈ L, (∀ w ∈ W, s w = w) → s = 1

namespace TransvectionConfig

variable {q : QuadraticForm (ZMod 2) V} {a : V} {W : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)} (C : TransvectionConfig q a W L)
include C

theorem q_a : q a = 0 := C.totallySingular a C.haW

theorem polar_W {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W) : polar q w w' = 0 := by
  rw [polar, C.totallySingular _ (W.add_mem hw hw'), C.totallySingular _ hw,
    C.totallySingular _ hw']
  simp

theorem mem_orthogonalGroup {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) : s ∈ orthogonalGroup q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (C.iso s hs)

theorem polar_apply_apply {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x y : V) :
    polar q (s x) (s y) = polar q x y :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (C.mem_orthogonalGroup hs) x y

theorem apply_apply {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x : V) : s (s x) = x := by
  rw [← LinearEquiv.mul_apply, C.sq s hs]
  rfl

theorem polar_sub_left {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x y : V) :
    polar q (s x - x) y = polar q x (s y - y) := by
  have h1 : polar q (s x) y = polar q x (s y) := by
    rw [← C.polar_apply_apply hs, C.apply_apply hs]
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right, h1]

theorem sub_sub_eq_zero {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x : V) :
    s (s x - x) - (s x - x) = 0 := by
  rw [map_sub, C.apply_apply hs, vec_sub, vec_sub, vec_sub, add_comm (s x) x]
  rw [show x + s x + (x + s x) = 0 from vec_add_self _]

theorem polar_a_sub {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (x : V) : polar q a (s x - x) = 0 := by
  have h1 : polar q a (s x) = polar q a x := by
    calc polar q a (s x) = polar q (s a) (s x) := by rw [C.fix s hs]
      _ = polar q a x := C.polar_apply_apply hs a x
  rw [QuadraticMap.polar_sub_right, h1, sub_self]

theorem apply_comm {s t : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (ht : t ∈ L) (x : V) :
    s (t x) = t (s x) := by
  rw [← LinearEquiv.mul_apply, C.comm s hs t ht, LinearEquiv.mul_apply]

theorem sub_sub_mem_span {s t : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (ht : t ∈ L) {x : V}
    (hx : polar q a x = 0) : s (t x - x) - (t x - x) ∈ (ZMod 2) ∙ a :=
  C.onW s hs _ (C.perp t ht x hx)

theorem eq_of_eqOn {s t : V ≃ₗ[ZMod 2] V} (hs : s ∈ L) (ht : t ∈ L)
    (h : ∀ w ∈ W, s w = t w) : s = t := by
  have h1 : t * s = 1 := by
    refine C.faithful _ (mul_mem ht hs) fun w hw => ?_
    rw [LinearEquiv.mul_apply, h w hw, C.apply_apply ht]
  calc s = t * t * s := by rw [C.sq t ht, one_mul]
    _ = t := by rw [mul_assoc, h1, mul_one]

@[expose] def lineW : Submodule (ZMod 2) W := (ZMod 2) ∙ (⟨a, C.haW⟩ : W)

abbrev K : Type _ := Module.Dual (ZMod 2) (W ⧸ C.lineW)

@[expose] def formW (φ : C.K) : Module.Dual (ZMod 2) W := φ ∘ₗ C.lineW.mkQ

theorem formW_apply (φ : C.K) (w : W) : C.formW φ w = φ (Submodule.Quotient.mk w) := rfl

theorem mk_a_eq_zero : (Submodule.Quotient.mk ⟨a, C.haW⟩ : W ⧸ C.lineW) = 0 :=
  (Submodule.Quotient.mk_eq_zero C.lineW).mpr (Submodule.mem_span_singleton_self _)

theorem formW_a (φ : C.K) : C.formW φ ⟨a, C.haW⟩ = 0 := by
  rw [formW_apply, C.mk_a_eq_zero, map_zero]

noncomputable def sOf (φ : C.K) : V ≃ₗ[ZMod 2] V :=
  Classical.choose (C.trans (C.formW φ) (C.formW_a φ))

theorem sOf_mem (φ : C.K) : C.sOf φ ∈ L :=
  (Classical.choose_spec (C.trans (C.formW φ) (C.formW_a φ))).1

theorem sOf_apply (φ : C.K) (w : W) :
    C.sOf φ w = w + φ (Submodule.Quotient.mk w) • a :=
  (Classical.choose_spec (C.trans (C.formW φ) (C.formW_a φ))).2 w

theorem sOf_add (φ ψ : C.K) : C.sOf (φ + ψ) = C.sOf φ * C.sOf ψ := by
  refine C.eq_of_eqOn (C.sOf_mem _) (mul_mem (C.sOf_mem φ) (C.sOf_mem ψ)) fun w hw => ?_
  rw [LinearEquiv.mul_apply, show w = ((⟨w, hw⟩ : W) : V) from rfl, C.sOf_apply,
    C.sOf_apply, map_add, map_smul, C.fix _ (C.sOf_mem φ), C.sOf_apply, LinearMap.add_apply,
    add_smul]
  abel

theorem sOf_zero : C.sOf 0 = 1 :=
  C.faithful _ (C.sOf_mem 0) fun w hw => by
    rw [show w = ((⟨w, hw⟩ : W) : V) from rfl, C.sOf_apply]
    simp

theorem sOf_eq_one_iff (φ : C.K) : C.sOf φ = 1 ↔ φ = 0 := by
  constructor
  · intro h
    refine C.lineW.linearMap_qext (LinearMap.ext fun w => ?_)
    have h1 := C.sOf_apply φ w
    rw [h] at h1
    simp only [LinearEquiv.coe_one, id, left_eq_add, smul_eq_zero, C.ha0, or_false] at h1
    simpa using h1
  · rintro rfl
    exact C.sOf_zero

theorem sOf_injective : Function.Injective C.sOf := by
  intro φ ψ h
  have h1 : C.sOf (φ + ψ) = 1 := by
    rw [C.sOf_add, h, C.sq _ (C.sOf_mem ψ)]
  have h2 := (C.sOf_eq_one_iff _).mp h1
  calc φ = φ + ψ - ψ := by abel
    _ = ψ := by rw [h2, zero_sub, vec_neg]

@[expose] def formK (ψ : Module.Dual (ZMod 2) W) (hψ : ψ ⟨a, C.haW⟩ = 0) : C.K :=
  C.lineW.liftQ ψ ((Submodule.span_singleton_le_iff_mem _ _).mpr (LinearMap.mem_ker.mpr hψ))

theorem formK_apply (ψ : Module.Dual (ZMod 2) W) (hψ : ψ ⟨a, C.haW⟩ = 0) (w : W) :
    C.formK ψ hψ (Submodule.Quotient.mk w) = ψ w := rfl

theorem exists_sOf_eq {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ L) : ∃ φ : C.K, C.sOf φ = t := by
  obtain ⟨ℓ, hℓa, -⟩ := Submodule.exists_le_ker_of_notMem (p := (⊥ : Submodule (ZMod 2) V))
    (v := a) (by rw [Submodule.mem_bot]; exact C.ha0)
  have hℓ : ℓ a = 1 := zmod2_eq_one_of_ne_zero hℓa
  set φ : Module.Dual (ZMod 2) W :=
    ℓ ∘ₗ ((t : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ W.subtype with hφ
  have hφa : φ ⟨a, C.haW⟩ = 0 := by
    rw [hφ]
    simp [C.fix t ht]
  refine ⟨C.formK φ hφa, C.eq_of_eqOn (C.sOf_mem _) ht fun w hw => ?_⟩
  rw [show w = ((⟨w, hw⟩ : W) : V) from rfl, C.sOf_apply, C.formK_apply]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.onW t ht w hw)
  have hφw : φ ⟨w, hw⟩ = c := by
    rw [hφ]
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    rw [← hc, map_smul, hℓ, smul_eq_mul, mul_one]
  rw [hφw, hc]
  abel

noncomputable def theta (v : V) (φ ψ χ : C.K) : ZMod 2 :=
  polar q (C.sOf χ v - v) (C.sOf φ (C.sOf ψ v - v) - (C.sOf ψ v - v))

theorem theta_def (v : V) (φ ψ χ : C.K) : C.theta v φ ψ χ =
    polar q (C.sOf χ v - v) (C.sOf φ (C.sOf ψ v - v) - (C.sOf ψ v - v)) := by
  rw [theta]

theorem sOf_add_sub (φ φ' : C.K) (x : V) :
    C.sOf (φ + φ') x - x = (C.sOf φ x - x) + (C.sOf φ' x - x) +
      (C.sOf φ (C.sOf φ' x - x) - (C.sOf φ' x - x)) := by
  rw [C.sOf_add, LinearEquiv.mul_apply, map_sub]
  abel

theorem isAltTrilin_theta (v : V) : IsAltTrilin (C.theta v) where
  add_left φ φ' ψ χ := by
    have hy : polar q a (C.sOf ψ v - v) = 0 := C.polar_a_sub (C.sOf_mem ψ) v
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (C.sub_sub_mem_span (C.sOf_mem φ) (C.sOf_mem φ') hy)
    have hχ : polar q (C.sOf χ v - v) a = 0 := by
      rw [polar_comm]
      exact C.polar_a_sub (C.sOf_mem χ) v
    simp only [theta]
    rw [C.sOf_add_sub, polar_add_right, polar_add_right, ← hc, polar_smul_right, hχ, smul_zero,
      add_zero]
  swap₁₂ φ ψ χ := by
    simp only [theta]
    congr 1
    rw [map_sub, map_sub, C.apply_comm (C.sOf_mem φ) (C.sOf_mem ψ)]
    abel
  swap₂₃ φ ψ χ := by
    simp only [theta]
    rw [← C.polar_sub_left (C.sOf_mem φ), polar_comm]
  self₁₂ φ χ := by
    simp only [theta]
    rw [C.sub_sub_eq_zero (C.sOf_mem φ), polar_zero_right]

theorem exists_sub_mem_W {v : V} (hv : polar q a v = 1) {x : V} (hx : polar q a x = 0) :
    ∃ ψ : C.K, x - (C.sOf ψ v - v) ∈ W := by
  set ψ : Module.Dual (ZMod 2) W := q.polarBilin x ∘ₗ W.subtype with hψ
  have hψa : ψ ⟨a, C.haW⟩ = 0 := by
    rw [hψ]
    simp [polarBilin_apply_apply, polar_comm q x a, hx]
  refine ⟨C.formK ψ hψa, C.perp_le _ fun w hw => ?_⟩
  rw [QuadraticMap.polar_sub_left, C.polar_sub_left (C.sOf_mem _),
    show w = ((⟨w, hw⟩ : W) : V) from rfl, C.sOf_apply, add_sub_cancel_left, polar_smul_right,
    polar_comm q v a, hv, C.formK_apply]
  simp [hψ, polarBilin_apply_apply]

theorem theta_eq_zero_of_mem_pointRadical (v : V) {φ : C.K} (h : C.sOf φ ∈ pointRadical q a)
    (ψ χ : C.K) : C.theta v φ ψ χ = 0 := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((mem_pointRadical.mp h).2.2.1 _ (C.polar_a_sub (C.sOf_mem ψ) v))
  rw [theta, ← hc, polar_smul_right, polar_comm, C.polar_a_sub (C.sOf_mem χ) v, smul_zero]

theorem mem_pointRadical_of_theta_eq_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {v : V} (hv : polar q a v = 1) {φ : C.K}
    (h : ∀ ψ χ, C.theta v φ ψ χ = 0) : C.sOf φ ∈ pointRadical q a := by
  set s := C.sOf φ with hs
  have hsL : s ∈ L := C.sOf_mem φ
  refine ⟨C.mem_orthogonalGroup hsL, C.fix s hsL, fun x hx => ?_, fun v' => C.polar_a_sub hsL v'⟩
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) ((ZMod 2) ∙ a),
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [mem_orthogonal_span_singleton_iff] at hy
  rw [polarBilin_apply_apply]
  obtain ⟨ψ, hψ⟩ := C.exists_sub_mem_W hv hx
  obtain ⟨χ, hχ⟩ := C.exists_sub_mem_W hv hy
  set w := x - (C.sOf ψ v - v) with hw
  set w' := y - (C.sOf χ v - v) with hw'
  have hx' : x = (C.sOf ψ v - v) + w := by rw [hw]; abel
  have hy' : y = (C.sOf χ v - v) + w' := by rw [hw']; abel
  have hD : s x - x = (s (C.sOf ψ v - v) - (C.sOf ψ v - v)) + (s w - w) := by
    conv_lhs => rw [hx']
    rw [map_add]
    abel
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (C.onW s hsL w hψ)
  have hyψ : polar q a (C.sOf ψ v - v) = 0 := C.polar_a_sub (C.sOf_mem ψ) v
  have hDW : s (C.sOf ψ v - v) - (C.sOf ψ v - v) ∈ W := C.perp s hsL _ hyψ
  rw [hD, hy', polar_add_left, polar_add_right, polar_add_right, ← hc, polar_smul_right,
    polar_smul_right, polar_comm q (C.sOf χ v - v) a, C.polar_a_sub (C.sOf_mem χ) v,
    C.polar_W hχ hDW, C.polar_W hχ C.haW]
  have := h ψ χ
  rw [theta] at this
  rw [this]
  simp

theorem finrank_K_add_one [FiniteDimensional (ZMod 2) V] :
    finrank (ZMod 2) C.K + 1 = finrank (ZMod 2) W := by
  have h1 := Submodule.finrank_quotient_add_finrank C.lineW
  have h2 : finrank (ZMod 2) C.lineW = 1 :=
    finrank_span_singleton (fun h => C.ha0 (congrArg Subtype.val h))
  have h3 : finrank (ZMod 2) C.K = finrank (ZMod 2) (W ⧸ C.lineW) := Subspace.dual_finrank_eq
  omega

end TransvectionConfig

end CFSG.LargeExtraspecial
