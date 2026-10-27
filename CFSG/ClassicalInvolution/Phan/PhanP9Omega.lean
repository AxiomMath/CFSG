module

public import CFSG.ClassicalInvolution.Phan.PhanP9Alg
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalInvolution.Phan.PhanD3Pairs
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix QuadraticMap
open scoped MatrixGroups

section Embed

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eq_embGrp_transportEquiv (fr : Frame Q) (h2 : (2 : F) ≠ 0) {g : V ≃ₗ[F] V}
    (hg : g * fr.La (-1) = fr.La (-1) * g) (hfix : ∀ x ∈ fr.perp, g x = x) :
    g = fr.embGrp (fr.transportEquiv h2 hg) := by
  refine LinearEquiv.ext fun x => ?_
  have hperp : x - fr.incl (fr.coords x) ∈ fr.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have h1 : g x = g (fr.incl (fr.coords x)) + (x - fr.incl (fr.coords x)) := by
    conv_lhs => rw [show x = fr.incl (fr.coords x) + (x - fr.incl (fr.coords x)) by abel]
    rw [map_add, hfix _ hperp]
  have hspan : g (fr.incl (fr.coords x)) ∈ fr.span :=
    Frame.map_mem_span h2 hg ⟨_, rfl⟩
  have h2' : g (fr.incl (fr.coords x)) = fr.incl (fr.coords (g (fr.incl (fr.coords x)))) :=
    (Frame.mem_span_iff fr).1 hspan
  rw [h1, Frame.embGrp_apply, Frame.embLin_apply]
  simp only [Frame.transportEquiv_apply, Frame.transport_apply, LinearEquiv.coe_coe]
  rw [map_sub]
  conv_lhs => rw [h2']
  abel

theorem embGrp_mem_orthogonalGroup (fr : Frame Q) {S : Matrix (Fin 2) (Fin 2) F ≃ₗ[F]
    Matrix (Fin 2) (Fin 2) F} (hS : S ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) :
    fr.embGrp S ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [Frame.embGrp_apply]
  exact fr.Q_embLin (T := (S : Module.End F (Matrix (Fin 2) (Fin 2) F))) (fun X => by
    have := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hS) X
    rwa [detQ_apply, detQ_apply] at this) x

@[expose] noncomputable def embO (fr : Frame Q) :
    TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F)) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  ((fr.embGrp).comp (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))).subtype).codRestrict _
    (fun S => embGrp_mem_orthogonalGroup fr S.2)

theorem coe_embO (fr : Frame Q) (S : TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) :
    ((embO fr S : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) =
      fr.embGrp (S : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F) := rfl

theorem embO_reflectionOrthogonal (fr : Frame Q) (v : Matrix (Fin 2) (Fin 2) F)
    [Invertible (detQ (K := F) v)] [Invertible (Q (fr.incl v))] :
    ((embO fr (TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := F)) v) :
      TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[F] V) =
        TauCeti.QuadraticMap.reflection Q (fr.incl v) := by
  refine LinearEquiv.ext fun x => ?_
  rw [coe_embO, TauCeti.QuadraticMap.coe_reflectionOrthogonal, Frame.embGrp_apply,
    Frame.embLin_apply, TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
  have hp : polar Q (fr.incl v) x = polarDet v (fr.coords x) := by
    rw [polar_comm, Frame.polar_incl_right]
    simp [polarDet]
    ring
  have hq : Q (fr.incl v) = v.det := Frame.Q_incl fr v
  rw [hp, hq]
  simp only [LinearEquiv.coe_coe]
  rw [reflection_detQ_apply]
  simp only [reflM, sub_sub_cancel_left]
  rw [sub_eq_add_neg]
  congr 1
  simp [map_neg]

end Embed

end CFSG.ClassicalInvolution.PhanP

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix QuadraticMap
open scoped MatrixGroups

section SpinorNorm

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Invertible (2 : F)] [FiniteDimensional F V]

theorem orthogonalSpinorNorm_embO (fr : Frame Q) (hQ : Q.Nondegenerate)
    (S : TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) :
    CliffordAlgebra.orthogonalSpinorNorm Q hQ (embO fr S) =
      CliffordAlgebra.orthogonalSpinorNorm (detQ (K := F)) nondegenerate_detQ S := by
  have : NeZero (2 : F) := ⟨(Invertible.ne_zero (2 : F))⟩
  have key : (CliffordAlgebra.orthogonalSpinorNorm Q hQ).comp (embO fr) =
      CliffordAlgebra.orthogonalSpinorNorm (detQ (K := F)) nondegenerate_detQ := by
    refine TauCeti.QuadraticMap.orthogonalGroup_hom_ext (detQ (K := F)) nondegenerate_detQ
      fun v hv => ?_
    have : Invertible (Q (fr.incl v)) := by
      rw [Frame.Q_incl, ← detQ_apply]
      exact hv
    have e : embO fr (TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := F)) v) =
        TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.incl v) :=
      Subtype.ext (by
        rw [embO_reflectionOrthogonal, TauCeti.QuadraticMap.coe_reflectionOrthogonal])
    rw [MonoidHom.comp_apply, e, CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal,
      CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal]
    congr 1
    refine Units.ext ?_
    rw [val_unitOfInvertible, val_unitOfInvertible, Frame.Q_incl, detQ_apply]
  exact DFunLike.congr_fun key S

end SpinorNorm

end CFSG.ClassicalInvolution.PhanP

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix QuadraticMap
  CFSG.ClassicalInvolution.PhanD4 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups

section Spans

variable {F : Type} [Field F]

theorem span0_le_perp2 {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ (frame0 (F := F)).span) :
    x ∈ (frame2 (F := F)).perp := by
  obtain ⟨X, rfl⟩ := hx
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  exact polar_incl_frame0_frame2 X Y

theorem finrank_V8 : Module.finrank F (Fin 4 ⊕ Fin 4 → F) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem perp2_eq_span0 : (frame2 (F := F)).perp = (frame0 (F := F)).span := by
  refine (Submodule.eq_of_le_of_finrank_le (fun x hx => ?_) ?_).symm
  · exact span0_le_perp2 hx
  · have := finrank_perp_add_four (frame2 (F := F))
    have h0 := (frame0 (F := F)).finrank_span
    rw [finrank_V8] at this
    omega

theorem span2_le_perp0 {x : Fin 4 ⊕ Fin 4 → F} (hx : x ∈ (frame2 (F := F)).span) :
    x ∈ (frame0 (F := F)).perp := by
  obtain ⟨X, rfl⟩ := hx
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  rw [polar_comm]
  exact polar_incl_frame0_frame2 Y X

theorem perp0_eq_span2 : (frame0 (F := F)).perp = (frame2 (F := F)).span := by
  refine (Submodule.eq_of_le_of_finrank_le (fun x hx => ?_) ?_).symm
  · exact span2_le_perp0 hx
  · have := finrank_perp_add_four (frame0 (F := F))
    have h0 := (frame2 (F := F)).finrank_span
    rw [finrank_V8] at this
    omega

theorem comm_La2_of_fix (h2 : (2 : F) ≠ 0) {g : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F))
    (hfix : ∀ x ∈ (frame0 (F := F)).span, g x = x) :
    g * (frame2 (F := F)).La (-1) = (frame2 (F := F)).La (-1) * g := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1
    (show x ∈ (frame2 (F := F)).span ⊔ (frame2 (F := F)).perp by
      rw [(Frame.isCompl_span_perp (frame2 (F := F))).sup_eq_top]; trivial)
  have hb0 : b ∈ (frame0 (F := F)).span := by rw [← perp2_eq_span0]; exact hb
  have hgb : g b = b := hfix b hb0
  have hga : g a ∈ (frame2 (F := F)).span := by
    rw [← perp0_eq_span2, Frame.mem_perp_iff_forall_incl]
    intro Y
    have h3 := (Frame.mem_perp_iff_forall_incl (frame0 (F := F))).1 (span2_le_perp0 ha) Y
    have h1 := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO a ((frame0 (F := F)).incl Y)
    rw [hfix _ ⟨Y, rfl⟩, h3] at h1
    exact h1
  have e1 : (frame2 (F := F)).La (-1) a = -a := (Frame.mem_span_iff_inv _ h2).1 ha
  have e2 : (frame2 (F := F)).La (-1) b = b := (Frame.mem_perp_iff_fix _ h2).1 hb
  have e3 : (frame2 (F := F)).La (-1) (g a) = -g a := (Frame.mem_span_iff_inv _ h2).1 hga
  simp only [LinearEquiv.mul_apply, map_add, map_neg, e1, e2, hgb, e3]

end Spans

end CFSG.ClassicalInvolution.PhanP

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix QuadraticMap
  CFSG.ClassicalInvolution.PhanD4 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.MF15
open scoped MatrixGroups

section Final

variable {F : Type} [Field F]

theorem orthogonalDet_embO {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} [Invertible (2 : F)] (fr : Frame Q)
    (S : TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) :
    QuadraticMap.orthogonalDet Q (embO fr S) = QuadraticMap.orthogonalDet (detQ (K := F)) S := by
  have : NeZero (2 : F) := ⟨Invertible.ne_zero (2 : F)⟩
  have key : (QuadraticMap.orthogonalDet Q).comp (embO fr) =
      QuadraticMap.orthogonalDet (detQ (K := F)) := by
    refine TauCeti.QuadraticMap.orthogonalGroup_hom_ext (detQ (K := F)) nondegenerate_detQ
      fun v hv => ?_
    have : Invertible (Q (fr.incl v)) := by
      rw [Frame.Q_incl, ← detQ_apply]
      exact hv
    have e : embO fr (TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := F)) v) =
        TauCeti.QuadraticMap.reflectionOrthogonal Q (fr.incl v) :=
      Subtype.ext (by
        rw [embO_reflectionOrthogonal, TauCeti.QuadraticMap.coe_reflectionOrthogonal])
    rw [MonoidHom.comp_apply, e, QuadraticMap.orthogonalDet_reflectionOrthogonal,
      QuadraticMap.orthogonalDet_reflectionOrthogonal]
  exact DFunLike.congr_fun key S

theorem exists_vecs_of_refl_list [Invertible (2 : F)]
    (l : List (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))))
    (hl : ∀ r ∈ l, ∃ (v : Matrix (Fin 2) (Fin 2) F) (_ : Invertible (detQ (K := F) v)),
      TauCeti.QuadraticMap.reflectionOrthogonal (detQ (K := F)) v = r) :
    ∃ vs : List (Matrix (Fin 2) (Fin 2) F), (∀ v ∈ vs, v.det ≠ 0) ∧ vs.length = l.length ∧
      (∀ X, ((l.prod : TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) :
        Matrix (Fin 2) (Fin 2) F ≃ₗ[F] Matrix (Fin 2) (Fin 2) F) X = reflWord vs X) ∧
      ∃ u : Fˣ, (u : F) = detProd vs ∧
        CliffordAlgebra.orthogonalSpinorNorm (detQ (K := F)) nondegenerate_detQ l.prod =
          TauCeti.squareClassHom u := by
  induction l with
  | nil =>
    refine ⟨[], by simp, by simp, fun X => by simp [reflWord], 1, by simp [detProd], ?_⟩
    rw [List.prod_nil, map_one, map_one]
  | cons r l ih =>
    obtain ⟨v, hv, hrv⟩ := hl r List.mem_cons_self
    obtain ⟨vs, hvs, hlen, hX, u, hu, hsn⟩ := ih fun r' hr' => hl r' (List.mem_cons_of_mem r hr')
    subst hrv
    have hv0 : v.det ≠ 0 := det_ne_zero_of_invertible hv
    refine ⟨v :: vs, ?_, by simp [hlen], fun X => ?_,
      Units.mk0 v.det hv0 * u, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hv0
      · exact hvs w hw
    · rw [List.prod_cons, Subgroup.coe_mul, LinearEquiv.mul_apply, hX,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal, reflection_detQ_apply]
      rfl
    · rw [Units.val_mul, hu, detProd_cons]
      rfl
    · rw [List.prod_cons, map_mul, hsn, CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal,
        map_mul]
      congr 2
      refine Units.ext ?_
      rw [val_unitOfInvertible, detQ_apply]
      rfl

theorem exists_La_mul_of_fix (h2 : (2 : F) ≠ 0) {y : spinGroup (quadPlus 4 F)}
    (hfix : ∀ x ∈ (frame0 (F := F)).span, spinAction (quadPlus 4 F) y x = x) :
    ∃ A B : SL(2, F), spinAction (quadPlus 4 F) y =
      (frame2 (F := F)).La A * (frame2 (F := F)).swap.La B := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have : NeZero (2 : F) := ⟨h2⟩
  have hQ : (quadPlus 4 F).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 4 F)
  set gSO := CliffordAlgebra.spinToSpecialOrthogonal (quadPlus 4 F) y with hgSO
  set gO : TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) :=
    QuadraticMap.specialOrthogonalToOrthogonal (quadPlus 4 F) gSO with hgO
  have hgc : (gO : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) =
      spinAction (quadPlus 4 F) y :=
    LinearEquiv.ext fun v => by
      rw [hgO, QuadraticMap.coe_specialOrthogonalToOrthogonal]
      exact coe_spinToSpecialOrthogonal_apply' (quadPlus 4 F) y v
  have hdet1 : QuadraticMap.orthogonalDet (quadPlus 4 F) gO = 1 :=
    QuadraticMap.orthogonalDet_specialOrthogonalToOrthogonal gSO
  have hsn1 : CliffordAlgebra.orthogonalSpinorNorm (quadPlus 4 F) hQ gO = 1 := by
    have := CliffordAlgebra.spinorNorm_spinToSpecialOrthogonal (quadPlus 4 F) hQ y
    rwa [CliffordAlgebra.spinorNorm_apply] at this
  have hfixg : ∀ x ∈ (frame0 (F := F)).span, (gO : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) x
      = x := fun x hx => by rw [hgc]; exact hfix x hx
  have hcomm := comm_La2_of_fix h2 gO.2 hfixg
  set S' := (frame2 (F := F)).transportEquiv h2 hcomm with hS'def
  have hS' : S' ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F)) :=
    Frame.transportEquiv_mem_orthogonalGroup h2 gO.2 hcomm
  have hgS : (gO : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) =
      (frame2 (F := F)).embGrp S' :=
    eq_embGrp_transportEquiv (frame2 (F := F)) h2 hcomm
      (fun x hx => hfixg x (by rw [← perp2_eq_span0]; exact hx))
  have hemb : embO (frame2 (F := F)) ⟨S', hS'⟩ = gO := Subtype.ext (by rw [coe_embO, hgS])
  obtain ⟨l, hl, -, hprod⟩ := TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq
    (detQ (K := F)) nondegenerate_detQ ⟨S', hS'⟩
  obtain ⟨vs, hvs, hlen, hX, u, hu, hsn⟩ := exists_vecs_of_refl_list l hl
  have heven : Even l.length := by
    have h1 : QuadraticMap.orthogonalDet (detQ (K := F)) ⟨S', hS'⟩ = 1 := by
      rw [← orthogonalDet_embO (frame2 (F := F)), hemb, hdet1]
    have h3 := TauCeti.QuadraticMap.det_list_prod_of_reflectionOrthogonal (detQ (K := F)) l hl
    rw [hprod] at h3
    rw [QuadraticMap.orthogonalDet_apply] at h1
    rw [h1] at h3
    have h4 : (-1 : Fˣ) ^ l.length = 1 := h3.symm
    exact (neg_one_pow_eq_one_iff_even (by
      intro h
      have := congrArg (fun w : Fˣ => (w : F)) h
      simp at this
      exact h2 (by linear_combination -this))).1 h4
  have hsq : IsSquare u := by
    have h1 : CliffordAlgebra.orthogonalSpinorNorm (detQ (K := F)) nondegenerate_detQ ⟨S', hS'⟩ =
        1 := by
      rw [← orthogonalSpinorNorm_embO (frame2 (F := F)) hQ, hemb, hsn1]
    rw [← hprod, hsn] at h1
    have : u ∈ (TauCeti.squareClassHom (K := F)).ker := h1
    rw [TauCeti.ker_squareClassHom] at this
    exact Subgroup.mem_square.1 this
  obtain ⟨w, hw⟩ := hsq
  obtain ⟨n, hn⟩ := heven
  obtain ⟨A, B, hAB⟩ := exists_SL_of_even n vs (by rw [hlen, hn]; ring) hvs (c := (w : F))
    (by rw [← hu, hw, Units.val_mul])
  refine ⟨A, Frame.sigmaSL B, ?_⟩
  have hS'eq : S' = lmulEquiv A * rmulEquiv B := by
    refine LinearEquiv.ext fun X => ?_
    have h1 := hX X
    rw [hprod, hAB X] at h1
    rw [LinearEquiv.mul_apply, lmulEquiv_apply, rmulEquiv_apply]
    rw [← Matrix.mul_assoc]
    exact h1
  have hfin : (frame2 (F := F)).embGrp S' =
      (frame2 (F := F)).La A * (frame2 (F := F)).swap.La (Frame.sigmaSL B) := by
    rw [hS'eq, map_mul, Frame.La_eq_embGrp, Frame.swap_La_eq_embGrp, Frame.sigmaSL_sigmaSL]
  rw [← hgc, hgS, hfin]

end Final

end CFSG.ClassicalInvolution.PhanP
