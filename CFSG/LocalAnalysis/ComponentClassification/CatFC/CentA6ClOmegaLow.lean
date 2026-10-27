module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaCore

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Module
open CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Subspace

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

theorem omega_exists_regular_subspace [FiniteDimensional k U] [Invertible (2 : k)]
    (B : LinearMap.BilinForm k U) (hB : LinearMap.IsSymm B) (hnd : B.Nondegenerate) {r : ℕ}
    (hr : r ≤ finrank k U) :
    ∃ W : Submodule k U, finrank k W = r ∧ (B.restrict W).Nondegenerate := by
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hne : ∀ i, B (b i) (b i) ≠ 0 := fun i =>
    (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self B b hb).mp hnd i
  let v : Fin r → U := fun i => b (Fin.castLE hr i)
  have hv : LinearIndependent k v := b.linearIndependent.comp _ (Fin.castLE_injective hr)
  refine ⟨Submodule.span k (Set.range v), ?_, ?_⟩
  · rw [finrank_span_eq_card hv, Fintype.card_fin]
  · let bW := Basis.span hv
    have hbW : (B.restrict (Submodule.span k (Set.range v))).iIsOrtho bW := by
      intro i j hij
      change B (bW i) (bW j) = 0
      rw [Basis.span_apply, Basis.span_apply]
      exact hb (fun h => hij (Fin.castLE_injective hr h))
    refine (LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self _ bW hbW).mpr
      fun i => ?_
    change B (bW i) (bW i) ≠ 0
    rw [Basis.span_apply]
    exact hne _

end Subspace

section Extend

variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]
  (P : QuadraticForm k U) (W₁ W₂ : Submodule k U) (hc : IsCompl W₁ W₂)

noncomputable def omegaExtEquiv (g : W₁ ≃ₗ[k] W₁) : U ≃ₗ[k] U :=
  (Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm.trans
    ((LinearEquiv.prodCongr g (LinearEquiv.refl k W₂)).trans
      (Submodule.prodEquivOfIsCompl W₁ W₂ hc))

theorem omegaExtEquiv_apply (g : W₁ ≃ₗ[k] W₁) (x : W₁) (y : W₂) :
    omegaExtEquiv W₁ W₂ hc g ((x : U) + y) = (g x : U) + y := by
  have h : ((x : U) + y) = Submodule.prodEquivOfIsCompl W₁ W₂ hc (x, y) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
  rw [h]
  simp [omegaExtEquiv, Submodule.coe_prodEquivOfIsCompl']

theorem omegaExtEquiv_mem (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar P x y = 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (P.comp W₁.subtype)) :
    omegaExtEquiv W₁ W₂ hc g.val ∈ TauCeti.QuadraticMap.orthogonalGroup P := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective u
  have h : ((Submodule.prodEquivOfIsCompl W₁ W₂ hc (x, y) : U)) = (x : U) + y := by
    rw [Submodule.coe_prodEquivOfIsCompl']
  rw [h, omegaExtEquiv_apply, QuadraticMap.map_add P ((g.val x : W₁) : U) (y : U),
    QuadraticMap.map_add P (x : U) (y : U), horth _ (g.val x).2 _ y.2, horth _ x.2 _ y.2]
  have := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2) x
  simp only [QuadraticMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]

noncomputable def omegaExt (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar P x y = 0) :
    TauCeti.QuadraticMap.orthogonalGroup (P.comp W₁.subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup P where
  toFun g := ⟨omegaExtEquiv W₁ W₂ hc g.val, omegaExtEquiv_mem P W₁ W₂ hc horth g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective u
    have h : ((Submodule.prodEquivOfIsCompl W₁ W₂ hc (x, y) : U)) = (x : U) + y := by
      rw [Submodule.coe_prodEquivOfIsCompl']
    rw [h]
    exact omegaExtEquiv_apply W₁ W₂ hc 1 x y
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl W₁ W₂ hc).surjective u
    have h' : ((Submodule.prodEquivOfIsCompl W₁ W₂ hc (x, y) : U)) = (x : U) + y := by
      rw [Submodule.coe_prodEquivOfIsCompl']
    rw [h']
    change omegaExtEquiv W₁ W₂ hc (g.val * h.val) ((x : U) + y) =
      omegaExtEquiv W₁ W₂ hc g.val (omegaExtEquiv W₁ W₂ hc h.val ((x : U) + y))
    rw [omegaExtEquiv_apply, omegaExtEquiv_apply]
    have := omegaExtEquiv_apply W₁ W₂ hc g.val (h.val x) y
    rw [this]
    rfl

theorem omegaExt_apply (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar P x y = 0)
    (g : TauCeti.QuadraticMap.orthogonalGroup (P.comp W₁.subtype))
    (x : W₁) (y : W₂) : (omegaExt P W₁ W₂ hc horth g).val ((x : U) + y) = (g.val x : U) + y :=
  omegaExtEquiv_apply W₁ W₂ hc g.val x y

theorem omegaExt_injective (horth : ∀ x ∈ W₁, ∀ y ∈ W₂, QuadraticMap.polar P x y = 0) :
    Function.Injective (omegaExt P W₁ W₂ hc horth) := by
  intro g g' h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h1 := omegaExt_apply P W₁ W₂ hc horth g x 0
  have h2 := omegaExt_apply P W₁ W₂ hc horth g' x 0
  rw [h] at h1
  rw [h1] at h2
  simp at h2
  exact h2

end Extend

section Models

open CFSG.ComponentClassification.CatLeafProof
open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive

theorem omega_five_model {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 5) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      StatedLieAdmissible .PSp 2 p e ∧
      Blueprint.LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
        center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) .PSp 2 p e := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' (symplecticKernel_quasisimple hodd)
    (selfAdjointSymplecticAction h2) (selfAdjointSymplecticImage_quasisimple hodd) hcomm
  have hadm : StatedLieAdmissible .PSp 2 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_⟩
    have h1 : p ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  exact ⟨hq, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)⟩

open CatalogueBOrthogonalFourNonsplit in
theorem omega_nonsplit_four_model {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    IsQuasisimple (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∧
      StatedLieAdmissible .PSL 2 p (2 * e) ∧
      Blueprint.LieModel (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⧸
        center (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))) .PSL 2 p (2 * e) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨δ, hns, -, -, e', -, -, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd Q hQ hdim hno
  have : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have : Finite (extension (δ : K)) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd (δ : K) 0).symm
  have hcard := extension_card (δ : K)
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have hE2 : Nat.card (extension (δ : K)) ≠ 2 := by
    rw [hcard]
    nlinarith
  have hE3 : Nat.card (extension (δ : K)) ≠ 3 := by
    rw [hcard]
    nlinarith
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 (extension (δ : K)) le_rfl (Or.inr hE2)
      (Or.inr hE3)) (specialRho (δ : K) h2) (hermitianSpecialImage_quasisimple (δ : K) h2)
    hcomm
  have hE : Nat.card (extension (δ : K)) = p ^ (2 * e) := by
    rw [hcard, hK, ← pow_mul, mul_comm]
  have hadm : StatedLieAdmissible .PSL 2 p (2 * e) :=
    ⟨hp, by omega, le_rfl, fun h => hE2 (hE.trans (Prod.mk.inj h).2),
      fun h => hE3 (hE.trans (Prod.mk.inj h).2)⟩
  exact ⟨hq, hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, extension (δ : K), inferInstance, inferInstance, hE,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 (extension (δ : K))⟩⟩⟩)⟩

open CatalogueBOrthogonalFourSplit in
theorem omega_split_four_model {K W : Type} [Field K] [Finite K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hK3 : Nat.card K ≠ 3) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0) :
    ∃ L R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), IsQuasisimple L ∧
      IsQuasisimple R ∧ (∀ x ∈ L, ∀ y ∈ R, x * y = y * x) ∧
      OddLieCentralQuotient p L ∧ OddLieCentralQuotient p R := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, hcomm, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  refine ⟨_, _, hq₁, hq₂, hcomm, ?_, ?_⟩
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      rfl
    exact oddLieCentralQuotient_of_equiv_psl_two hp he hK hK2 hK3 E
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) rfl
    exact oddLieCentralQuotient_of_equiv_psl_two hp he hK hK2 hK3 E

end Models

section Obstruction

@[expose] def OmegaObstruction (G : Type) [Group G] : Prop :=
  (∃ (Y : Type) (_ : Group Y) (φ : Y →* G), IsQuasisimple Y ∧ Function.Injective φ ∧
    ∃ (τ : StatedLieTag) (n e : ℕ), StatedLieAdmissible τ n 3 e ∧
      Blueprint.LieModel (Y ⧸ center Y) τ n 3 e ∧ ¬ (τ = .PSL ∧ n = 2 ∧ e = 2)) ∨
  (∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂) (φ₁ : Y₁ →* G) (φ₂ : Y₂ →* G),
    IsQuasisimple Y₁ ∧ IsQuasisimple Y₂ ∧ Function.Injective φ₁ ∧ Function.Injective φ₂ ∧
    (∀ x y, φ₁ x * φ₂ y = φ₂ y * φ₁ x) ∧ OddLieCentralQuotient 3 Y₁ ∧
    OddLieCentralQuotient 3 Y₂)

theorem OmegaObstruction.of_injective {G G' : Type} [Group G] [Group G'] (ι : G →* G')
    (hι : Function.Injective ι) (h : OmegaObstruction G) : OmegaObstruction G' := by
  rcases h with ⟨Y, _, φ, hY, hφ, hm⟩ | ⟨Y₁, Y₂, _, _, φ₁, φ₂, h₁, h₂, hφ₁, hφ₂, hc, m₁, m₂⟩
  · exact Or.inl ⟨Y, _, ι.comp φ, hY, hι.comp hφ, hm⟩
  · refine Or.inr ⟨Y₁, Y₂, _, _, ι.comp φ₁, ι.comp φ₂, h₁, h₂, hι.comp hφ₁, hι.comp hφ₂, ?_,
      m₁, m₂⟩
    intro x y
    simp only [MonoidHom.comp_apply, ← map_mul, hc x y]

theorem OmegaObstruction.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : OmegaObstruction G) : OmegaObstruction G' :=
  h.of_injective e.toMonoidHom e.injective

section Orth

variable {k U : Type} [Field k] [Finite k] [AddCommGroup U] [Module k U] [FiniteDimensional k U]

private theorem omega_regular_sub (P : QuadraticForm k U) (hQ : P.polarBilin.Nondegenerate)
    (h2 : (2 : k) ≠ 0) {r : ℕ} (hr : r ≤ Module.finrank k U) :
    ∃ W : Submodule k U, Module.finrank k W = r ∧
      (P.comp W.subtype).polarBilin.Nondegenerate ∧
      IsCompl W (LinearMap.BilinForm.orthogonal P.polarBilin W) ∧
      ∀ x ∈ W, ∀ y ∈ LinearMap.BilinForm.orthogonal P.polarBilin W, QuadraticMap.polar P x y = 0 := by
  have : Invertible (2 : k) := invertibleOfNonzero h2
  have hsym : LinearMap.IsSymm P.polarBilin := ⟨fun x y => QuadraticMap.polar_comm P x y⟩
  obtain ⟨W, hW, hWnd⟩ := omega_exists_regular_subspace P.polarBilin hsym hQ hr
  refine ⟨W, hW, ?_, LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    hsym.isRefl hWnd, ?_⟩
  · have heq : (P.comp W.subtype).polarBilin = LinearMap.BilinForm.restrict P.polarBilin W := by
      rw [QuadraticMap.polarBilin_comp]
      ext x y
      rfl
    rw [heq]
    exact hWnd
  · intro x hx y hy
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp hy x hx

theorem omega_obstruction_five {e : ℕ} (he : 1 ≤ e) (hK : Nat.card k = 3 ^ e)
    (P : QuadraticForm k U) (hQ : P.polarBilin.Nondegenerate)
    (hr : 5 ≤ Module.finrank k U) :
    OmegaObstruction (TauCeti.QuadraticMap.orthogonalGroup P) := by
  have hodd : Odd (Nat.card k) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨W, hW, hndW, hcompl, horth⟩ := omega_regular_sub P hQ h2 hr
  obtain ⟨hq, hadm, hlie⟩ := omega_five_model Nat.prime_three (by norm_num) he hK
    (P.comp W.subtype) hndW hW
  exact Or.inl ⟨↥(commutator (TauCeti.QuadraticMap.orthogonalGroup (P.comp W.subtype))),
    inferInstance, (omegaExt P W _ hcompl horth).comp (commutator _).subtype, hq,
    (omegaExt_injective P W _ hcompl horth).comp (Subgroup.subtype_injective _),
    .PSp, 2, e, hadm, hlie, by rintro ⟨h, -, -⟩; exact absurd h (by decide)⟩

theorem omega_obstruction_four {e : ℕ} (he : 2 ≤ e) (hK : Nat.card k = 3 ^ e)
    (P : QuadraticForm k U) (hQ : P.polarBilin.Nondegenerate)
    (hr : 4 ≤ Module.finrank k U) :
    OmegaObstruction (TauCeti.QuadraticMap.orthogonalGroup P) := by
  have hodd : Odd (Nat.card k) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by norm_num)).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨W, hW, hndW, hcompl, horth⟩ := omega_regular_sub P hQ h2 hr
  by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, (P.comp W.subtype) x = 0
  · have hK3 : Nat.card k ≠ 3 := by
      rw [hK]
      intro h
      have : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
      omega
    obtain ⟨L, R, hL, hR, hcomm, mL, mR⟩ := omega_split_four_model Nat.prime_three (by norm_num)
      (by omega) hK hK3 (P.comp W.subtype) hndW hW hS
    refine Or.inr ⟨↥L, ↥R, inferInstance, inferInstance,
      (omegaExt P W _ hcompl horth).comp L.subtype, (omegaExt P W _ hcompl horth).comp R.subtype,
      hL, hR, (omegaExt_injective P W _ hcompl horth).comp (Subgroup.subtype_injective _),
      (omegaExt_injective P W _ hcompl horth).comp (Subgroup.subtype_injective _), ?_, mL, mR⟩
    intro x y
    simp only [MonoidHom.comp_apply, ← map_mul]
    exact congrArg _ (hcomm x.1 x.2 y.1 y.2)
  · obtain ⟨hq, hadm, hlie⟩ := omega_nonsplit_four_model Nat.prime_three (by norm_num)
      (by omega) hK (P.comp W.subtype) hndW hW hS
    refine Or.inl ⟨↥(commutator (TauCeti.QuadraticMap.orthogonalGroup (P.comp W.subtype))),
      inferInstance, (omegaExt P W _ hcompl horth).comp (commutator _).subtype, hq,
      (omegaExt_injective P W _ hcompl horth).comp (Subgroup.subtype_injective _),
      .PSL, 2, 2 * e, hadm, hlie, ?_⟩
    rintro ⟨-, -, h⟩
    omega

end Orth

end Obstruction


section Solvable

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

theorem omega_fixed_solvable_aux {X : Type} [Group X] (Z : Subgroup X) [Z.Normal]
    (hc : Z ≤ center X) (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z)
    (h : Group.IsSolvable ↥(fixedSubgroup ψ)) :
    Group.IsSolvable ↥(fixedSubgroup (onQuotient Z ψ hinv)) := by
  have hnorm := fixedImage_normal Z ψ hinv hc
  have h2 : Group.IsSolvable ↥(fixedImage Z ψ hinv) :=
    solvable_of_surjective (fixedImageProjection_surjective Z ψ hinv)
  have h3 : Group.IsSolvable (↥(fixedSubgroup (onQuotient Z ψ hinv)) ⧸ fixedImage Z ψ hinv) := by
    have hcomm := fixed_quotient_abelian Z ψ hinv hc
    exact Group.isSolvable_of_comm fun a b => hcomm.is_comm.comm a b
  exact solvable_of_ker_le_range (fixedImage Z ψ hinv).subtype
    (QuotientGroup.mk' (fixedImage Z ψ hinv))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem omega_fixed_solvable {X : Type} [Group X] (N Z : Subgroup X) [Z.Normal]
    (hcentral : Z ≤ center X) (ψ : MulAut X) (hN : N.map ψ.toMonoidHom = N)
    (hZ : Z.map ψ.toMonoidHom = Z) (h : Group.IsSolvable ↥(fixedSubgroup ψ)) :
    Group.IsSolvable ↥(fixedSubgroup (onNormalCentralQuotient N Z ψ hN hZ)) :=
  omega_fixed_solvable_aux (Z.subgroupOf N) (central_subgroupOf N Z hcentral)
    (restrictAutomorphism N ψ hN) (restricted_central_invariant N Z ψ hN hZ)
    (solvable_of_solvable_injective (f := (fixedNormalEquiv N ψ hN).toMonoidHom)
      (fixedNormalEquiv N ψ hN).injective)

end Solvable

section Final

open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare (orthogonalOperatorCentralizer)

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)

theorem omega_not_solvable [Finite (projectiveDerived Q)]
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (h : A6Hyp (projectiveConjugation Q A μ hsim) D) :
    ¬ Group.IsSolvable ↥(orthogonalOperatorCentralizer Q A.toLinearMap) := by
  intro hF
  have h1 : Group.IsSolvable ↥(fixedSubgroup (similarityConjugation Q A μ hsim)) :=
    solvable_of_solvable_injective (f := (fixedCentralizerEquiv Q A μ hsim).toMonoidHom)
      (fixedCentralizerEquiv Q A μ hsim).injective
  exact h.not_solvable (omega_fixed_solvable (orthogonalDerived Q) (scalarSigns Q)
    (scalarSigns_central Q) (similarityConjugation Q A μ hsim)
    (orthogonalDerived_invariant Q A μ hsim) (scalarSigns_invariant Q A μ hsim) h1)

variable {Q A μ hsim} in
theorem omega_false_of_obstruction [Finite (projectiveDerived Q)] (hO : LieOrderFormulasInput)
    {D : Subgroup ↥(fixedSubgroup (projectiveConjugation Q A μ hsim))}
    (h : A6Hyp (projectiveConjugation Q A μ hsim) D)
    (hobs : OmegaObstruction ↥(orthogonalOperatorCentralizer Q A.toLinearMap)) : False := by
  rcases hobs with ⟨Y, _, φ, hY, hφ, τ, n, e, hadm, hm, hne⟩ |
    ⟨Y₁, Y₂, _, _, φ₁, φ₂, hY₁, hY₂, hφ₁, hφ₂, hc, m₁, m₂⟩
  · exact omega_false_of_witness hO h hY φ hφ hadm hm hne
  · exact omega_false_of_two_witnesses hO h hY₁ hY₂ φ₁ hφ₁ φ₂ hφ₂ hc m₁ m₂

end Final

end CFSG.ComponentClassification.CatFC
