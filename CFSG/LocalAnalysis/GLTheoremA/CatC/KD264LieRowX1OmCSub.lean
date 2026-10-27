module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCMax
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open TauCeti.QuadraticMap
open scoped commutatorElement

section Ext

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
  (W : Submodule (ZMod 2) V)

abbrev perpOf : Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) W

variable {Q W}
variable (hW : IsCompl W (perpOf Q W))
include hW

@[expose] noncomputable def extHom :
    orthogonalGroup (Q.restrict (perpOf Q W)) →* orthogonalGroup Q :=
  ((orthogonalGroupCongr (IsometryEquiv.prodRestrictOrthogonal Q W hW)).toMonoidHom.comp
    (orthogonalGroupProd (Q.restrict W) (Q.restrict (perpOf Q W)))).comp (MonoidHom.inr _ _)

theorem extHom_apply (φ : orthogonalGroup (Q.restrict (perpOf Q W))) (v : V) :
    ((extHom hW φ).1 : V ≃ₗ[ZMod 2] V) v =
      ((W.projectionOnto _ hW v : W) : V) +
        ((φ.1 ((perpOf Q W).projectionOnto W hW.symm v) : perpOf Q W) : V) := by
  simp [extHom]

theorem extHom_apply_of_mem_W (φ : orthogonalGroup (Q.restrict (perpOf Q W))) {w : V}
    (hw : w ∈ W) : ((extHom hW φ).1 : V ≃ₗ[ZMod 2] V) w = w := by
  rw [extHom_apply hW, Submodule.projectionOnto_apply_of_mem_left hW hw,
    Submodule.projectionOnto_apply_of_mem_right hW.symm hw]
  simp

theorem extHom_apply_of_mem_U (φ : orthogonalGroup (Q.restrict (perpOf Q W))) {u : V}
    (hu : u ∈ perpOf Q W) :
    ((extHom hW φ).1 : V ≃ₗ[ZMod 2] V) u = ((φ.1 ⟨u, hu⟩ : perpOf Q W) : V) := by
  rw [extHom_apply hW, Submodule.projectionOnto_apply_of_mem_right hW hu,
    Submodule.projectionOnto_apply_of_mem_left hW.symm hu]
  simp

theorem extHom_injective : Function.Injective (extHom hW) :=
  ((orthogonalGroupCongr (IsometryEquiv.prodRestrictOrthogonal Q W hW)).injective.comp
    (orthogonalGroupProd_injective (Q.restrict W) (Q.restrict (perpOf Q W)))).comp
    (fun a b h => by simpa using congrArg Prod.snd h)

end Ext

section Fix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V)
  (W : Submodule (ZMod 2) V)

@[expose] def fixW : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g ∈ orthogonalGroup Q ∧ ∀ w ∈ W, g w = w}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun w hw => by
    rw [LinearEquiv.mul_apply, hb.2 w hw, ha.2 w hw]⟩
  one_mem' := ⟨one_mem _, fun w _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun w hw =>
    (LinearEquiv.symm_apply_eq a).2 (ha.2 w hw).symm⟩

variable {Q W}

theorem mem_fixW {g : V ≃ₗ[ZMod 2] V} : g ∈ fixW Q W ↔ g ∈ orthogonalGroup Q ∧ ∀ w ∈ W, g w = w :=
  Iff.rfl

theorem fixW_le_orthogonalGroup : fixW Q W ≤ orthogonalGroup Q := fun _ hg => hg.1

theorem map_mem_perpOf {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ fixW Q W) {u : V} (hu : u ∈ perpOf Q W) :
    g u ∈ perpOf Q W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
  intro n hn
  have h1 := polar_apply_of_mem_orthogonalGroup hg.1 n u
  rw [hg.2 n hn] at h1
  rw [QuadraticMap.polarBilin_apply_apply, h1]
  have := hu n hn
  rwa [QuadraticMap.polarBilin_apply_apply] at this

variable (hW : IsCompl W (perpOf Q W))
include hW

@[expose] noncomputable def extG :
    orthogonalGroup (Q.restrict (perpOf Q W)) →* (V ≃ₗ[ZMod 2] V) :=
  (orthogonalGroup Q).subtype.comp (extHom hW)

theorem extG_injective : Function.Injective (extG hW) :=
  Subtype.val_injective.comp (extHom_injective hW)

theorem extG_mem_fixW (φ : orthogonalGroup (Q.restrict (perpOf Q W))) : extG hW φ ∈ fixW Q W :=
  ⟨(extHom hW φ).2, fun _ hw => extHom_apply_of_mem_W hW φ hw⟩

theorem range_extG : (extG hW).range = fixW Q W := by
  ext g
  constructor
  · rintro ⟨φ, rfl⟩
    exact extG_mem_fixW hW φ
  · intro hg
    have hginv : g⁻¹ ∈ fixW Q W := inv_mem hg
    have hmap : (perpOf Q W).map (g : V →ₗ[ZMod 2] V) = perpOf Q W := by
      apply le_antisymm
      · rintro _ ⟨u, hu, rfl⟩
        exact map_mem_perpOf hg hu
      · intro u hu
        refine ⟨g⁻¹ u, map_mem_perpOf hginv hu, ?_⟩
        show g (g⁻¹ u) = u
        exact g.apply_symm_apply u
    let φ0 : perpOf Q W ≃ₗ[ZMod 2] perpOf Q W := g.ofSubmodules _ _ hmap
    have hφ0 : φ0 ∈ orthogonalGroup (Q.restrict (perpOf Q W)) := by
      rw [mem_orthogonalGroup_iff]
      intro u
      change Q ((φ0 u : perpOf Q W) : V) = Q (u : V)
      rw [show ((φ0 u : perpOf Q W) : V) = g u from LinearEquiv.ofSubmodules_apply g hmap u]
      exact map_app_of_mem_orthogonalGroup hg.1 u
    refine ⟨⟨φ0, hφ0⟩, ?_⟩
    ext v
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 (by rw [hW.sup_eq_top]; exact Submodule.mem_top :
      v ∈ W ⊔ perpOf Q W)
    show (extHom hW ⟨φ0, hφ0⟩).1 (w + u) = g (w + u)
    rw [map_add, map_add]
    rw [extHom_apply_of_mem_W hW _ hw, extHom_apply_of_mem_U hW _ hu, hg.2 w hw]
    exact congrArg (w + ·) (LinearEquiv.ofSubmodules_apply g hmap ⟨u, hu⟩)

end Fix


section Comp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem rot_mem_commutator_of {a b : V} (h : MinusPair Q a b) (S : Subgroup (V ≃ₗ[ZMod 2] V))
    (ha : reflect Q a ∈ S) (hb : reflect Q b ∈ S) : rot Q a b ∈ ⁅S, S⁆ := by
  have hc : ⁅reflect Q a, reflect Q b⁆ ∈ ⁅S, S⁆ := Subgroup.commutator_mem_commutator ha hb
  have hsq : ⁅reflect Q a, reflect Q b⁆ = rot Q a b * rot Q a b := by
    rw [commutatorElement_def, reflect_inv, reflect_inv, rot]
    simp only [mul_assoc]
  have h3 := rot_pow_three h
  have h4 : rot Q a b = (rot Q a b * rot Q a b) * (rot Q a b * rot Q a b) := by
    calc rot Q a b = rot Q a b ^ 3 * rot Q a b := by rw [h3, one_mul]
      _ = _ := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h4, ← hsq]
  exact mul_mem hc hc

theorem reflect_mem_fixW {W : Submodule (ZMod 2) V} {a : V} (ha : a ∈ perpOf Q W) :
    reflect Q a ∈ fixW Q W := by
  refine ⟨reflect_mem_orthogonalGroup Q a, fun w hw => ?_⟩
  apply reflect_apply_of_polar_eq_zero
  have := (LinearMap.BilinForm.mem_orthogonal_iff.1 ha) w hw
  rw [QuadraticMap.polarBilin_apply_apply] at this
  rw [polar_comm]
  exact this

theorem fixW_le_centralizer_torus {l : List (V × V)} (hl : IsFrame Q l) :
    fixW Q (Wspan l) ≤ Subgroup.centralizer (torus Q l : Set (V ≃ₗ[ZMod 2] V)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  suffices hc : Commute g t from hc.symm.eq
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    exact commute_rot_of_fix hg.1
      (hg.2 q.1 (planeSpan_le_Wspan hq (left_mem_planeSpan q)))
      (hg.2 q.2 (planeSpan_le_Wspan hq (right_mem_planeSpan q)))
  | one => exact Commute.one_right _
  | mul s t hs ht ihs iht => exact ihs.mul_right iht
  | inv t ht iht => exact iht.inv_right

theorem map_mem_Wspan_of_commute {l : List (V × V)} (hl : IsFrame Q l) {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ q ∈ l, Commute g (rot Q q.1 q.2)) : ∀ w ∈ Wspan l, g w ∈ Wspan l := by
  induction l with
  | nil =>
    intro w hw
    rw [Wspan_nil, Submodule.mem_bot] at hw
    rw [hw, map_zero]
    exact Submodule.zero_mem _
  | cons q l ih =>
    obtain ⟨hq, hperp, hl'⟩ := isFrame_cons.1 hl
    intro w hw
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add]
    refine Submodule.add_mem_sup ?_ (ih hl' (fun r hr => hg r (List.mem_cons_of_mem _ hr)) w' hw')
    obtain ⟨x, hx⟩ := exists_rot_sub_eq hq hu
    have hc := hg q List.mem_cons_self
    have : g u = rot Q q.1 q.2 (g x) - g x := by
      rw [← hx, map_sub]
      have := congrArg (fun φ : V ≃ₗ[ZMod 2] V => φ x) hc.eq
      simp only [LinearEquiv.mul_apply] at this
      rw [this]
    rw [this]
    exact rot_sub_mem_span hq (g x)

theorem fixW_conj_mem {l : List (V × V)} (hl : IsFrame Q l) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup Q) (hgc : g ∈ Subgroup.centralizer (torus Q l : Set (V ≃ₗ[ZMod 2] V)))
    {h : V ≃ₗ[ZMod 2] V} (hh : h ∈ fixW Q (Wspan l)) : g * h * g⁻¹ ∈ fixW Q (Wspan l) := by
  have hcomm : ∀ q ∈ l, Commute g (rot Q q.1 q.2) := fun q hq =>
    (Subgroup.mem_centralizer_iff.1 hgc _ (rot_mem_torus hq)).symm
  have hcomm' : ∀ q ∈ l, Commute g⁻¹ (rot Q q.1 q.2) := fun q hq => (hcomm q hq).inv_left
  have hs := map_mem_Wspan_of_commute hl hcomm
  have hs' := map_mem_Wspan_of_commute hl hcomm'
  refine ⟨mul_mem (mul_mem hg hh.1) (inv_mem hg), fun w hw => ?_⟩
  have h1 : g⁻¹ w ∈ Wspan l := hs' w hw
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh.2 _ h1]
  exact g.apply_symm_apply w

theorem commutator_fixW_conj {l : List (V × V)} (hl : IsFrame Q l) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup Q) (hgc : g ∈ Subgroup.centralizer (torus Q l : Set (V ≃ₗ[ZMod 2] V)))
    {n : V ≃ₗ[ZMod 2] V} (hn : n ∈ ⁅fixW Q (Wspan l), fixW Q (Wspan l)⁆) :
    g * n * g⁻¹ ∈ ⁅fixW Q (Wspan l), fixW Q (Wspan l)⁆ := by
  set ψ : (V ≃ₗ[ZMod 2] V) →* (V ≃ₗ[ZMod 2] V) := (MulAut.conj g).toMonoidHom with hψ
  have hle : (fixW Q (Wspan l)).map ψ ≤ fixW Q (Wspan l) := by
    rintro _ ⟨h, hh, rfl⟩
    exact fixW_conj_mem hl hg hgc hh
  have hmap := Subgroup.map_commutator (fixW Q (Wspan l)) (fixW Q (Wspan l)) ψ
  have : ψ n ∈ ⁅(fixW Q (Wspan l)).map ψ, (fixW Q (Wspan l)).map ψ⁆ := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem ψ hn
  exact Subgroup.commutator_mono hle hle this

theorem commutator_fixW_equiv {W : Submodule (ZMod 2) V} (hW : IsCompl W (perpOf Q W)) :
    Nonempty (↥⁅fixW Q W, fixW Q W⁆ ≃*
      ↥⁅orthogonalGroup (Q.restrict (perpOf Q W)), orthogonalGroup (Q.restrict (perpOf Q W))⁆) := by
  set O' := orthogonalGroup (Q.restrict (perpOf Q W)) with hO'
  have h1 : ⁅fixW Q W, fixW Q W⁆ = (commutator ↥O').map (extG hW) := by
    rw [← range_extG hW, commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map]
  have h2 : ⁅O', O'⁆ = (commutator ↥O').map O'.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr h1).trans
    ((Subgroup.equivMapOfInjective _ (extG hW) (extG_injective hW)).symm.trans
      ((Subgroup.equivMapOfInjective _ O'.subtype O'.subtype_injective).trans
        (MulEquiv.subgroupCongr h2.symm)))⟩

end Comp

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
