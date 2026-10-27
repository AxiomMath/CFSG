module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4FixTop
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.D4Rigid CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
open scoped MatrixGroups commutatorElement

section Frames

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem exists_spin_incl_eq [Invertible (2 : F)] [FiniteDimensional F V] [Finite F]
    [Nontrivial V] (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (fr fr' : Frame Q) (hperp : 2 ≤ Module.finrank F fr.perp) :
    ∃ x : spinGroup Q, ∀ Y, spinAction Q x (fr.incl Y) = fr'.incl Y := by
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
  refine ⟨x, fun Y => ?_⟩
  rw [hx, hg', Subgroup.coe_mul, LinearEquiv.mul_apply, hhfix _ ⟨Y, rfl⟩]
  exact hgi Y

end Frames

section GLMat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem glLin_surjective : Function.Surjective (glLin : GL ι F →* ((ι → F) ≃ₗ[F] (ι → F))) := by
  intro a
  set A : GL ι F := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).symm a) with hA
  refine ⟨A, LinearEquiv.ext fun v => ?_⟩
  have h : Matrix.GeneralLinearGroup.toLin A =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).symm a := by simp [hA]
  rw [glLin_apply, ← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.toLin_apply, h]
  rfl

theorem glLin_injective : Function.Injective (glLin : GL ι F →* ((ι → F) ≃ₗ[F] (ι → F))) := by
  intro a b h
  refine Units.ext (Matrix.toLin'.injective (LinearMap.ext fun v => ?_))
  have := congrArg (fun e : (ι → F) ≃ₗ[F] (ι → F) => e v) h
  simpa [glLin_apply, Matrix.toLin'_apply] using this

end GLMat

section Lift

variable {p f : ℕ} [Fact p.Prime]

local notation "Q₄" => quadPlus 4 (GaloisField p f)

theorem d4FixLift_std (hp2 : p ≠ 2)
    {β : spinGroup Q₄ ≃* spinGroup Q₄}
    (h0 : ∀ g ∈ stdSL2 (GaloisField p f) 0, β g = g)
    (h1 : ∀ g ∈ stdSL2 (GaloisField p f) 1, β g = g) :
    ∃ a : (Idx → GaloisField p f) ≃ₗ[GaloisField p f] (Idx → GaloisField p f),
      (∀ v, Q₄ (a v) = Q₄ v) ∧ ∀ x v, spinAction Q₄ (β x) (a v) = a (spinAction Q₄ x v) := by
  have hd : FixData p β :=
    ⟨two_ne_zero_galoisField f hp2, Nat.Prime.odd_of_ne_two Fact.out hp2, h0, h1⟩
  exact ⟨isoA hd, Q_isoA hd, theta_alpha_isoA hd⟩

theorem d4FixLift_proved : D4FixLift p f := by
  intro hp2 hq fr' α hα
  classical
  obtain ⟨hodd, h4⟩ := card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  set θ := spinAction Q₄ with hθ
  set fr₀ : Frame Q₄ := (D4Rigid.fr (GaloisField p f)).toFrame ne01 true false with hfr₀
  have hswap : fr₀.swap = (D4Rigid.fr (GaloisField p f)).toFrame ne01 true true :=
    Frame.ext_vec rfl rfl rfl rfl
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hperp : 2 ≤ Module.finrank (GaloisField p f) fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨x, hx⟩ := exists_spin_incl_eq hodd (nondegenerate_polarBilin_quadPlus 4 _) fr₀ fr' hperp
  have hθx : θ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q₄ x v
  have hmap : fr₀.map hθx = fr' := Frame.map_eq_of_incl hθx hx
  have hmap' : fr₀.swap.map hθx = fr'.swap := by
    refine Frame.map_eq_of_incl hθx fun Y => ?_
    rw [Frame.incl_swap, Frame.incl_swap, hx]
  have hLa : ∀ A : SL(2, GaloisField p f), fr'.La A = θ x * fr₀.La A * (θ x)⁻¹ := fun A => by
    rw [← hmap, Frame.map_La]
  have hLa' : ∀ A : SL(2, GaloisField p f),
      fr'.swap.La A = θ x * fr₀.swap.La A * (θ x)⁻¹ := fun A => by
    rw [← hmap', Frame.map_La]
  set P₀ := fr₀.La.range ⊔ fr₀.swap.La.range with hP₀
  set P := fr'.La.range ⊔ fr'.swap.La.range with hP
  set c : spinGroup Q₄ ≃* spinGroup Q₄ := MulAut.conj x with hc
  have hP₀P : ∀ h ∈ P₀, θ x * h * (θ x)⁻¹ ∈ P := by
    have : P₀ ≤ P.comap (MulAut.conj (θ x)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        change θ x * fr₀.La A * (θ x)⁻¹ ∈ P
        rw [← hLa]
        exact Subgroup.mem_sup_left ⟨A, rfl⟩
      · rintro _ ⟨A, rfl⟩
        change θ x * fr₀.swap.La A * (θ x)⁻¹ ∈ P
        rw [← hLa']
        exact Subgroup.mem_sup_right ⟨A, rfl⟩
    exact fun h hh => this hh
  have hcP : ∀ g ∈ P₀.comap θ, c g ∈ P.comap θ := by
    intro g hg
    have := hP₀P _ hg
    simpa [hc, MulAut.conj_apply, map_mul, map_inv] using this
  have hcomm : ∀ g ∈ ⁅P₀.comap θ, P₀.comap θ⁆, c g ∈ ⁅P.comap θ, P.comap θ⁆ := by
    intro g hg
    have hle : (⁅P₀.comap θ, P₀.comap θ⁆).map c.toMonoidHom ≤ ⁅P.comap θ, P.comap θ⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (fun y ⟨g, hg, hgy⟩ => hgy ▸ hcP g hg)
        (fun y ⟨g, hg, hgy⟩ => hgy ▸ hcP g hg)
    exact hle ⟨g, hg, rfl⟩
  set β : spinGroup Q₄ ≃* spinGroup Q₄ := c.trans (α.trans c.symm) with hβ
  have hβfix : ∀ g ∈ ⁅P₀.comap θ, P₀.comap θ⁆, β g = g := by
    intro g hg
    have h := hα (c g) (hcomm g hg)
    show c.symm (α (c g)) = g
    rw [h]
    exact c.symm_apply_apply g
  have hperfSL : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.ClassicalInvolution.sl2_isPerfect h4
  have hstd : ∀ (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      ((D4Rigid.fr (GaloisField p f)).longSL2 hij s t).range.map θ =
        ((D4Rigid.fr (GaloisField p f)).toFrame hij s t).La.range := fun i j hij s t =>
    map_longSL2_range _ hij s t
  have hle : ∀ R : Subgroup (spinGroup Q₄), (R.map θ ≤ P₀) → ⁅R, R⁆ = R →
      ∀ g ∈ R, β g = g := by
    intro R hR hperf g hg
    refine hβfix g ?_
    have h1 : R ≤ P₀.comap θ := fun y hy => hR ⟨y, hy, rfl⟩
    rw [← hperf] at hg
    exact Subgroup.commutator_mono h1 h1 hg
  have hperf : ∀ (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      ⁅((D4Rigid.fr (GaloisField p f)).longSL2 hij s t).range,
        ((D4Rigid.fr (GaloisField p f)).longSL2 hij s t).range⁆ =
        ((D4Rigid.fr (GaloisField p f)).longSL2 hij s t).range := fun i j hij s t =>
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  have h0 : ∀ g ∈ stdSL2 (GaloisField p f) 0, β g = g := by
    have e : stdSL2 (GaloisField p f) 0 =
        ((D4Rigid.fr (GaloisField p f)).longSL2 ne01 true false).range := rfl
    rw [e]
    refine hle _ ?_ (hperf 0 1 ne01 true false)
    rw [hstd 0 1 ne01 true false]
    exact le_sup_left
  have h1 : ∀ g ∈ stdSL2 (GaloisField p f) 1, β g = g := by
    have e : stdSL2 (GaloisField p f) 1 =
        ((D4Rigid.fr (GaloisField p f)).longSL2 ne01 true true).range := rfl
    rw [e]
    refine hle _ ?_ (hperf 0 1 ne01 true true)
    rw [hstd 0 1 ne01 true true, ← hswap]
    exact le_sup_right
  obtain ⟨a, hQa, hθa⟩ := d4FixLift_std hp2 h0 h1
  have hθβ : ∀ y, θ (β y) = a * θ y * a⁻¹ := by
    intro y
    refine LinearEquiv.ext fun v => ?_
    have := hθa y (a.symm v)
    simpa [LinearEquiv.mul_apply] using this
  obtain ⟨A, hA⟩ := glLin_surjective (θ x * a * (θ x)⁻¹)
  refine ⟨A, RingEquiv.refl _, 1, fun v => ?_, fun y => ?_⟩
  · have h1 : ((A : Matrix _ _ _).mulVec (fun i => (RingEquiv.refl (GaloisField p f)) (v i))) =
        θ x (a ((θ x)⁻¹ v)) := by
      have := glLin_apply A v
      rw [hA] at this
      simpa [LinearEquiv.mul_apply] using this.symm
    rw [h1, map_spinAction, hQa, show (θ x)⁻¹ = θ x⁻¹ from (map_inv θ x).symm, map_spinAction]
    simp
  · rw [glFieldEquiv_refl]
    refine glLin_injective ?_
    rw [map_mul, map_mul, map_inv, hA, glLin_spinMatrix, glLin_spinMatrix]
    have hαy : α y = c (β (c.symm y)) := by
      show α y = c (c.symm (α (c (c.symm y))))
      rw [c.apply_symm_apply, c.apply_symm_apply]
    change θ (α y) = θ x * a * (θ x)⁻¹ * θ y * (θ x * a * (θ x)⁻¹)⁻¹
    have e2 : θ (c.symm y) = (θ x)⁻¹ * θ y * θ x := by
      rw [hc, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
    rw [hαy, hc, MulAut.conj_apply, map_mul, map_mul, map_inv, hθβ, ← hc, e2]
    group

end Lift

end CFSG.ClassicalInvolution.G2D4Models.Twin
