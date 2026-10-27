module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Planes
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.RankThree.Classical.OddQuadraticFrame
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Perp

theorem polarNondegOn_perp (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) :
    PolarNondegOn Q fr.perp := by
  intro x hx h
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  have hy : y ∈ fr.span ⊔ fr.perp := by
    rw [fr.isCompl_span_perp.sup_eq_top]
    trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  rw [polar_add_right, h w hw]
  have : polar Q x u = 0 := by
    obtain ⟨Y, rfl⟩ := hu
    exact (Frame.mem_perp_iff_forall_incl fr).mp hx Y
  rw [this, zero_add]

theorem finrank_perp_add_four [FiniteDimensional F V] (fr : Frame Q) :
    Module.finrank F fr.perp + 4 = Module.finrank F V := by
  have h := Submodule.finrank_add_eq_of_isCompl fr.isCompl_span_perp
  rw [fr.finrank_span] at h
  omega

end Perp

section Represent

variable [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_mem_eq_unit [Finite F] (hodd : Odd (Nat.card F)) {P : Submodule F V}
    (hP : (Q.restrict P).Nondegenerate) (h2 : 2 ≤ Module.finrank F P) (u : Fˣ) :
    ∃ v ∈ P, Q v = u := by
  have := Fintype.ofFinite F
  have hK' : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨l, hlen, hlorth, hlne, hlspan, -⟩ := exists_orthogonal_list_restrict Q P hP
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hlen
    omega
  · simp at hlen
    omega
  · have hab : polar Q a b = 0 :=
      ((List.pairwise_cons.mp hlorth).1 b List.mem_cons_self).polar_eq_zero
    have ha0 : Q a ≠ 0 := hlne a List.mem_cons_self
    have hb0 : Q b ≠ 0 := hlne b (List.mem_cons_of_mem _ List.mem_cons_self)
    have haP : a ∈ P := hlspan ▸ Submodule.subset_span List.mem_cons_self
    have hbP : b ∈ P := hlspan ▸ Submodule.subset_span (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨s, t, hst⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hK' ha0 hb0 (u : F)
    refine ⟨s • a + t • b, P.add_mem (P.smul_mem s haP) (P.smul_mem t hbP), ?_⟩
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q hab]
    linear_combination hst

end Represent

section Correction

variable [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_reflection_correction [Finite F] (hodd : Odd (Nat.card F)) (hQ : Q.Nondegenerate)
    {W P : Submodule F V} (hWP : ∀ x ∈ W, ∀ y ∈ P, polar Q y x = 0)
    (hP : (Q.restrict P).Nondegenerate) (hP2 : 2 ≤ Module.finrank F P)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ h : TauCeti.QuadraticMap.orthogonalGroup Q, (∀ x ∈ W, (h : V ≃ₗ[F] V) x = x) ∧
      QuadraticMap.orthogonalDet Q h = QuadraticMap.orthogonalDet Q g ∧
      CliffordAlgebra.orthogonalSpinorNorm Q hQ h =
        (CliffordAlgebra.orthogonalSpinorNorm Q hQ g)⁻¹ := by
  set σ' : Multiplicative (TauCeti.SquareClassGroup F) :=
    (CliffordAlgebra.orthogonalSpinorNorm Q hQ g)⁻¹ with hσ'
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, TauCeti.squareClassHom u = σ' := by
    refine ⟨Additive.toMul (Quotient.out (Multiplicative.toAdd σ')), ?_⟩
    rw [TauCeti.squareClassHom_apply, TauCeti.squareClass_toMul_out]
    rfl
  have hdet : QuadraticMap.orthogonalDet Q g = 1 ∨ QuadraticMap.orthogonalDet Q g = -1 := by
    have hsq := TauCeti.QuadraticMap.orthogonalDet_sq
      ((QuadraticMap.nondegenerate_polar_iff.mpr hQ).1) g
    have hsq' : ((QuadraticMap.orthogonalDet Q g : Fˣ) : F) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
    rcases sq_eq_one_iff.mp hsq' with h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Units.ext (by simpa using h))
  obtain ⟨v, hvP, hvu⟩ := exists_mem_eq_unit hodd hP hP2 u
  obtain ⟨w, hwP, hw1⟩ := exists_mem_eq_unit hodd hP hP2 1
  have hv0 : Q v ≠ 0 := by rw [hvu]; exact u.ne_zero
  have hw0 : Q w ≠ 0 := by rw [hw1]; exact one_ne_zero
  have := invertibleOfNonzero hv0
  have := invertibleOfNonzero hw0
  have hfixv : ∀ x ∈ W, TauCeti.QuadraticMap.reflection Q v x = x := fun x hx =>
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q v (hWP x hx v hvP)
  have hfixw : ∀ x ∈ W, TauCeti.QuadraticMap.reflection Q w x = x := fun x hx =>
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q w (hWP x hx w hwP)
  have hsv : CliffordAlgebra.orthogonalSpinorNorm Q hQ
      (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = TauCeti.squareClassHom u := by
    rw [CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal]
    congr 1
    exact Units.ext (by rw [val_unitOfInvertible, hvu])
  have hsw : CliffordAlgebra.orthogonalSpinorNorm Q hQ
      (TauCeti.QuadraticMap.reflectionOrthogonal Q w) = 1 := by
    rw [CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal]
    have : unitOfInvertible (Q w) = 1 := Units.ext (by rw [val_unitOfInvertible, hw1])
    rw [this, map_one]
  rcases hdet with hd | hd
  · refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal Q v *
      TauCeti.QuadraticMap.reflectionOrthogonal Q w, ?_, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal, hfixw x hx, hfixv x hx]
    · rw [map_mul, QuadraticMap.orthogonalDet_reflectionOrthogonal,
        QuadraticMap.orthogonalDet_reflectionOrthogonal, hd]
      norm_num
    · rw [map_mul, hsv, hsw, mul_one, hu]
  · refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal Q v, ?_, ?_, ?_⟩
    · intro x hx
      rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
      exact hfixv x hx
    · rw [QuadraticMap.orthogonalDet_reflectionOrthogonal, hd]
    · rw [hsv, hu]

theorem exists_spinAction_eq [Nontrivial V] (hQ : Q.Nondegenerate)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (hd : QuadraticMap.orthogonalDet Q g = 1)
    (hs : CliffordAlgebra.orthogonalSpinorNorm Q hQ g = 1) :
    ∃ x : spinGroup Q, spinAction Q x = (g : V ≃ₗ[F] V) := by
  have hgSO : g ∈ (QuadraticMap.specialOrthogonalToOrthogonal Q).range := by
    rw [QuadraticMap.range_specialOrthogonalToOrthogonal]
    exact QuadraticMap.mem_specialOrthogonalWithin_iff.mpr (by
      rw [← QuadraticMap.orthogonalDet_apply]
      exact hd)
  obtain ⟨s, hs'⟩ := hgSO
  have hsn : CliffordAlgebra.spinorNorm Q hQ s = 1 := by
    rw [CliffordAlgebra.spinorNorm_apply, hs']
    exact hs
  have hmem : s ∈ (CliffordAlgebra.spinToSpecialOrthogonal Q).range := by
    rw [CliffordAlgebra.range_spinToSpecialOrthogonal_eq_ker_spinorNorm]
    exact hsn
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, LinearEquiv.ext fun v => ?_⟩
  rw [← coe_spinToSpecialOrthogonal_apply', hx, ← hs',
    QuadraticMap.coe_specialOrthogonalToOrthogonal]

end Correction

@[expose] noncomputable def spanEquiv (fr : Frame Q) : Matrix (Fin 2) (Fin 2) F ≃ₗ[F] fr.span :=
  LinearEquiv.ofInjective fr.incl fr.incl_injective

theorem spanEquiv_apply (fr : Frame Q) (Y : Matrix (Fin 2) (Fin 2) F) :
    ((spanEquiv fr Y : fr.span) : V) = fr.incl Y := rfl

section Witt

variable [Invertible (2 : F)] [FiniteDimensional F V]

@[expose] noncomputable def spanIsometry (fr fr' : Frame Q) :
    (Q.restrict fr.span).IsometryEquiv (Q.restrict fr'.span) where
  toLinearEquiv := (spanEquiv fr).symm.trans (spanEquiv fr')
  map_app' x := by
    obtain ⟨Y, rfl⟩ := (spanEquiv fr).surjective x
    have h1 : ((spanEquiv fr).symm.trans (spanEquiv fr')) (spanEquiv fr Y) = spanEquiv fr' Y := by
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    change Q ((((spanEquiv fr).symm.trans (spanEquiv fr')) (spanEquiv fr Y) : fr'.span) : V) =
      Q ((spanEquiv fr Y : fr.span) : V)
    rw [h1, spanEquiv_apply, spanEquiv_apply, Frame.Q_incl, Frame.Q_incl]

omit [Invertible (2 : F)] [FiniteDimensional F V] in
theorem spanIsometry_spanEquiv (fr fr' : Frame Q) (Y : Matrix (Fin 2) (Fin 2) F) :
    spanIsometry fr fr' (spanEquiv fr Y) = spanEquiv fr' Y := by
  change ((spanEquiv fr).symm.trans (spanEquiv fr')) (spanEquiv fr Y) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

theorem exists_isometry_incl_eq (fr fr' : Frame Q) :
    ∃ g : V ≃ₗ[F] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ∀ Y, g (fr.incl Y) = fr'.incl Y := by
  have hW : (Q.restrict fr.span).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (Frame.polarNondegOn_span fr))
  obtain ⟨e, he⟩ := (spanIsometry fr fr').exists_extension hW
  refine ⟨e.toLinearEquiv, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => e.map_app x,
    fun Y => ?_⟩
  have h := he (spanEquiv fr Y)
  rw [spanIsometry_spanEquiv, spanEquiv_apply, spanEquiv_apply] at h
  exact h

end Witt

section Ext

theorem Frame.e₁_eq_incl (fr : Frame Q) : fr.e₁ = fr.incl !![1, 0; 0, 0] := by
  simp [Frame.incl_apply]

theorem Frame.f₁_eq_incl (fr : Frame Q) : fr.f₁ = fr.incl !![0, 0; 0, 1] := by
  simp [Frame.incl_apply]

theorem Frame.e₂_eq_incl (fr : Frame Q) : fr.e₂ = fr.incl !![0, -1; 0, 0] := by
  simp [Frame.incl_apply]

theorem Frame.f₂_eq_incl (fr : Frame Q) : fr.f₂ = fr.incl !![0, 0; 1, 0] := by
  simp [Frame.incl_apply]

theorem Frame.ext_vec {fr fr' : Frame Q} (h1 : fr.e₁ = fr'.e₁) (h2 : fr.f₁ = fr'.f₁)
    (h3 : fr.e₂ = fr'.e₂) (h4 : fr.f₂ = fr'.f₂) : fr = fr' := by
  obtain ⟨⟨e, f, a, b, c⟩, ⟨e', f', a', b', c'⟩, o⟩ := fr
  obtain ⟨⟨e₀, f₀, a₀, b₀, c₀⟩, ⟨e₀', f₀', a₀', b₀', c₀'⟩, o₀⟩ := fr'
  simp only [Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem Frame.map_eq_of_incl {fr fr' : Frame Q} {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : ∀ Y, g (fr.incl Y) = fr'.incl Y) :
    fr.map hg = fr' := by
  refine Frame.ext_vec ?_ ?_ ?_ ?_
  · rw [Frame.e₁_eq_incl, Frame.map_incl, h, ← Frame.e₁_eq_incl]
  · rw [Frame.f₁_eq_incl, Frame.map_incl, h, ← Frame.f₁_eq_incl]
  · rw [Frame.e₂_eq_incl, Frame.map_incl, h, ← Frame.e₂_eq_incl]
  · rw [Frame.f₂_eq_incl, Frame.map_incl, h, ← Frame.f₂_eq_incl]

end Ext

section Conj

variable [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_spin_conj [Finite F] [Nontrivial V] (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (fr fr' : Frame Q) (hperp : 2 ≤ Module.finrank F fr.perp) :
    ∃ x : spinGroup Q, ∀ A : SL(2, F),
      fr'.La A = spinAction Q x * fr.La A * (spinAction Q x)⁻¹ := by
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  obtain ⟨g, hg, hgi⟩ := exists_isometry_incl_eq fr fr'
  have hWP : ∀ x ∈ fr.span, ∀ y ∈ fr.perp, polar Q y x = 0 := by
    rintro _ ⟨Y, rfl⟩ y hy
    exact (Frame.mem_perp_iff_forall_incl fr).mp hy Y
  have hP : (Q.restrict fr.perp).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (polarNondegOn_perp hQ fr))
  obtain ⟨h, hhfix, hhdet, hhsn⟩ :=
    exists_reflection_correction hodd hQnd hWP hP hperp ⟨g, hg⟩
  set g' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨g, hg⟩ * h with hg'
  have hd : QuadraticMap.orthogonalDet Q g' = 1 := by
    rw [hg', map_mul, hhdet, ← pow_two]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hQ.1 ⟨g, hg⟩
  have hs : CliffordAlgebra.orthogonalSpinorNorm Q hQnd g' = 1 := by
    rw [hg', map_mul, hhsn]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := exists_spinAction_eq hQnd g' hd hs
  refine ⟨x, fun A => ?_⟩
  have hg'i : ∀ Y, (g' : V ≃ₗ[F] V) (fr.incl Y) = fr'.incl Y := fun Y => by
    rw [hg', Subgroup.coe_mul, LinearEquiv.mul_apply, hhfix _ ⟨Y, rfl⟩]
    exact hgi Y
  have hmap : fr.map g'.2 = fr' := Frame.map_eq_of_incl g'.2 hg'i
  rw [hx, ← hmap]
  exact Frame.map_La fr g'.2 A

end Conj

end CFSG.ClassicalInvolution.ModelFacts
