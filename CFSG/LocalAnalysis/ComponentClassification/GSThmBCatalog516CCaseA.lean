module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CTheta
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Fac
public import CFSG.Assembly.GL83LieDefs

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Module QuadraticMap
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
open CFSG.GroupTheory.WeirSylow (IsPlusType)

section Sub

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem coe_reflect_subtype {U : Submodule K V} (e x : U) :
    ((reflect (Q.comp U.subtype) e x : U) : V) = reflect Q (e : V) (x : V) := by
  by_cases he : Q (e : V) = 0
  · rw [reflect_of_map_eq_zero (Q := Q.comp U.subtype) he, reflect_of_map_eq_zero he]
    rfl
  · rw [reflect_apply (Q := Q.comp U.subtype) he, reflect_apply he]
    rfl

theorem symm_pair_val {C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    {U U' : Submodule K V} (hcompl : IsCompl U U') (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0)
    (ι : C ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (hι : ∀ h (x : U) (y : U'), (ι.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val)
    (e₀ e₁ : U) (t : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))
    (ht : t.val = reflect (Q.comp U.subtype) e₀ * reflect (Q.comp U.subtype) e₁) :
    (ι.symm (t, 1)).val.val = reflect Q (e₀ : V) * reflect Q (e₁ : V) := by
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ U ⊔ U' := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have h1 := hι (t, 1) ⟨x, hx⟩ ⟨y, hy⟩
  simp only at h1
  rw [h1, ht, LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_add, map_add,
    reflect_apply_of_polar_eq_zero (horth _ e₁.2 y hy),
    reflect_apply_of_polar_eq_zero (horth _ e₀.2 y hy), coe_reflect_subtype,
    coe_reflect_subtype]
  rfl

end Sub

section Factor

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem isPlusType_of_split {W W' : Submodule K V} (hcompl : IsCompl W W')
    (horth : ∀ x ∈ W, ∀ y ∈ W', polar Q x y = 0) (hV : finrank K V = 8)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, (Q.comp W.subtype) x = 0)
    (hS' : ∃ S : Submodule K W', finrank K S = 2 ∧ ∀ x ∈ S, (Q.comp W'.subtype) x = 0) :
    IsPlusType Q := by
  obtain ⟨S, hS2, hSQ⟩ := hS
  obtain ⟨S', hS2', hSQ'⟩ := hS'
  set T := S.map W.subtype with hT
  set T' := S'.map W'.subtype with hT'
  have hTW : T ≤ W := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hTW' : T' ≤ W' := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hdisj : T ⊓ T' = ⊥ := eq_bot_iff.mpr fun v hv =>
    hcompl.disjoint.le_bot ⟨hTW hv.1, hTW' hv.2⟩
  have hfT : finrank K T = 2 := by
    rw [hT, Submodule.finrank_map_subtype_eq]
    exact hS2
  have hfT' : finrank K T' = 2 := by
    rw [hT', Submodule.finrank_map_subtype_eq]
    exact hS2'
  refine ⟨T ⊔ T', ?_, fun v hv => ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq T T'
    rw [hdisj, finrank_bot, add_zero, hfT, hfT'] at h
    rw [h, hV]
  · obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have h1 : Q x' = 0 := hSQ x' hx'
    have h2 : Q y' = 0 := hSQ' y' hy'
    have h3 : Q (W.subtype x' + W'.subtype y') = Q x' + Q y' + polar Q x' y' :=
      QuadraticMap.map_add Q _ _
    rw [h3, horth _ x'.2 _ y'.2, h1, h2, add_zero, add_zero]

end Factor

section Hom

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {C : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} {U U' : Submodule K V}

@[expose] def factorHom (ι : C ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  C.subtype.comp (ι.symm.toMonoidHom.comp ((MonoidHom.inl _ _).comp (commutator _).subtype))

theorem factorHom_apply (ι : C ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (a : commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype))) :
    factorHom ι a = (ι.symm (a.val, 1)).val := rfl

end Hom

variable {K : Type} [Field K] [Finite K] {b c : K}

theorem symm_mem_center {Y X : Type*} [Group Y] [Group X] (Φ : Y ≃* X) {z : X}
    (hz : ∀ x : X, Commute z x) : Φ.symm z ∈ center Y := by
  rw [mem_center_iff]
  intro g
  apply Φ.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  exact (hz (Φ g)).eq.symm

theorem exists_spin_lift {Y : Type} [Group Y] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : K) ≠ 0) (φ : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))
    (hQ0 : ∃ v, qM K b c v ≠ 0) (Φ : Y ≃* spinGroup (quadMinus 4 K b c))
    (hΦ : ∀ y : Y, φ (QuotientGroup.mk y) = spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) (Φ y))
    {e₀ e₁ : Fin (2 * 4) → K} (hq₀ : qM K b c e₀ = 1) (hq₁ : qM K b c e₁ = 1)
    (ho : polar (qM K b c) e₀ e₁ = 0) :
    ∃ y : Y, y * y ≠ 1 ∧ y * y ∈ center Y ∧ ∀ g : orthogonalDerived (qM K b c),
      g.val.val = reflect (qM K b c) e₀ * reflect (qM K b c) e₁ →
        thetaOf φ hQ0 (QuotientGroup.mk y) = QuotientGroup.mk'
          ((scalarSigns (qM K b c)).subgroupOf (orthogonalDerived (qM K b c))) g := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hR : ∀ u, quadMinus 4 K b c ((reIdx K).symm u) = qM K b c u := fun u => by
    rw [← qM_reIdx, LinearEquiv.apply_symm_apply]
  have h1 : quadMinus 4 K b c ((reIdx K).symm e₀) * quadMinus 4 K b c ((reIdx K).symm e₁) =
      1 := by rw [hR, hR, hq₀, hq₁, one_mul]
  have hpol : polar (quadMinus 4 K b c) ((reIdx K).symm e₀) ((reIdx K).symm e₁) = 0 := by
    rw [← polar_qM_reIdx, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact ho
  have hQne : quadMinus 4 K b c ≠ 0 := fun h => by
    have h3 : quadMinus 4 K b c ((reIdx K).symm e₀) = 0 := by rw [h]; rfl
    rw [hR, hq₀] at h3
    exact one_ne_zero h3
  have hss := pairElt_mul_self h1 hpol hQne
  refine ⟨Φ.symm (pairElt _ _ h1), ?_, ?_, fun g hg => ?_⟩
  · rw [← map_mul, hss, Ne, MulEquiv.map_eq_one_iff]
    exact CliffordAlgebra.spinGroup.negOne_ne_one _ hQne
  · rw [← map_mul, hss]
    exact symm_mem_center Φ LieType.Steinberg.CentralExt.SpinMinusClosed.commute_negOneM
  · have h3 : (QuotientGroup.mk (Φ.symm (pairElt _ _ h1)) : Y ⧸ center Y) =
        φ.symm (spinToStatedProj _ (range_spinMatrix_quadMinus (le_refl 4) hirr)
          (pairElt _ _ h1)) := by
      rw [MulEquiv.eq_symm_apply, hΦ, MulEquiv.apply_symm_apply]
    rw [h3]
    exact theta_pairElt hirr φ hQ0 h1 g hg

theorem caseA_core {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (center Y) = 2)
    (α : MulAut Y) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e)
    (φ : Y ⧸ center Y ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))
    (hQ0 : ∃ v, qM K b c v ≠ 0) (Φ : Y ≃* spinGroup (quadMinus 4 K b c))
    (hΦ : ∀ y : Y, φ (QuotientGroup.mk y) = spinToStatedProj (quadMinus 4 K b c)
      (range_spinMatrix_quadMinus (le_refl 4) hirr) (Φ y))
    (A : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (μ : Kˣ)
    (hsim : ∀ x, qM K b c (A x) = (μ : K) * qM K b c x)
    (hconj : ∀ x, thetaOf φ hQ0 (barAut α x) =
      projectiveConjugation (qM K b c) A μ hsim (thetaOf φ hQ0 x))
    {U U' : Submodule K (Fin (2 * 4) → K)}
    (ι : orthogonalOperatorCentralizer (qM K b c) A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup ((qM K b c).comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup ((qM K b c).comp U'.subtype))
    (hcompl : IsCompl U U') (horth : ∀ x ∈ U, ∀ y ∈ U', polar (qM K b c) x y = 0)
    (hU : ((qM K b c).comp U.subtype).polarBilin.Nondegenerate)
    (hι : ∀ h (x : U) (y : U'), (ι.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val)
    (hdim : 5 ≤ finrank K U ∨ (finrank K U = 4 ∧
      ¬ ∃ S : Submodule K U, finrank K S = 2 ∧ ∀ x ∈ S, ((qM K b c).comp U.subtype) x = 0)) :
    ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧ ⁅N, N⁆ = N ∧ center Y ≤ N := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hq : IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup
      ((qM K b c).comp U.subtype))) := by
    rcases hdim with h5 | ⟨h4, hno⟩
    · exact OddSelector.commutator_orthogonalGroup_quasisimple hodd _ hU h5
    · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd _ hU h4 hno
      exact hq
  have hd4 : 4 ≤ finrank K U := by omega
  have hF := hq.1.commutator_eq_top
  have hfA : ∀ a v, (factorHom ι a).val (A v) = A ((factorHom ι a).val v) := by
    intro a v
    rw [factorHom_apply]
    exact (ι.symm (a.val, 1)).property v
  obtain ⟨eb, heo, hQe⟩ := Catalog7Std.Om8.exists_unit_orthogonal_basis hodd hU (by omega)
  have hl0 : (0 : ℕ) < finrank K U := by omega
  have hl1 : (1 : ℕ) < finrank K U := by omega
  have hm0 : (0 : ℕ) < finrank K U - 1 := by omega
  have hm1 : (1 : ℕ) < finrank K U - 1 := by omega
  have hq₀ : qM K b c (eb ⟨0, hl0⟩ : Fin (2 * 4) → K) = 1 := hQe ⟨0, hl0⟩ hm0
  have hq₁ : qM K b c (eb ⟨1, hl1⟩ : Fin (2 * 4) → K) = 1 := hQe ⟨1, hl1⟩ hm1
  have ho : polar (qM K b c) (eb ⟨0, hl0⟩ : Fin (2 * 4) → K) (eb ⟨1, hl1⟩) = 0 :=
    heo _ _ (fun h => absurd (congrArg Fin.val h) (by simp))
  obtain ⟨y, hy2, hyZ, hyg⟩ := exists_spin_lift hirr h2 φ hQ0 Φ hΦ hq₀ hq₁ ho
  refine concl_center hZ α (imgL_perfect (thetaOf φ hQ0) hF (factorHom ι))
    (imgL_fixed (thetaOf φ hQ0) hF (factorHom ι) (barAut α) A μ hsim hconj hfA) ?_ hy2 hyZ
  set t : commutator (TauCeti.QuadraticMap.orthogonalGroup ((qM K b c).comp U.subtype)) :=
    ⟨⟨_, mul_mem (reflect_mem_orthogonalGroup _ (eb ⟨0, hl0⟩))
      (reflect_mem_orthogonalGroup _ (eb ⟨1, hl1⟩))⟩,
      Catalog7Std.Om8.reflect_mul_reflect_mem_commutator h2 hq₀ hq₁⟩
  apply mem_imgL_of_theta _ hF _ (a := t)
  apply hyg
  rw [toOmega_val, factorHom_apply]
  exact symm_pair_val hcompl horth ι hι _ _ _ rfl

end CFSG.ComponentClassification.GSThmB.Cent516
