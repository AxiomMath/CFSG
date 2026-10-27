module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovSL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
  CFSG.ComponentClassification.CatalogueBProjectiveInvolution
  CFSG.ComponentClassification.CatalogueBGeneralLinear
open scoped MatrixGroups

theorem ivk93cov_pgl_block {F : Type} [Field F] [Finite F] (htwo : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) (A : GL (Fin n) F) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
    (hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1)
    {M : Subgroup (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _))} (hM : IsPComponent 2 M) :
    (∃ a : ℕ, 2 ≤ a ∧ a < n ∧ ∃ ψ : SL(a, F) →* ↥M, Function.Surjective ψ) ∨
    (∃ (E : Type) (_ : Field E) (_ : Finite E) (m : ℕ), Nat.card E = Nat.card F ^ 2 ∧ 2 ≤ m ∧
      2 * m = n ∧ ∃ ψ : SL(m, E) →* ↥M, Function.Surjective ψ) := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨L, hL, hm⟩ := ivk93l_lift_map A hM
  obtain ⟨lambda, hsq⟩ := matrix_square_scalar A hinv
  have hsurj : ∀ {G : Type} [Group G] (φ : G ≃* ↥L), ∃ ψ : G →* ↥M, Function.Surjective ψ := by
    intro G _ φ
    refine ⟨((MulEquiv.subgroupCongr hm).toMonoidHom.comp
      ((ordinaryCentralizerProjection A).subgroupMap L)).comp φ.toMonoidHom, ?_⟩
    exact ((MulEquiv.subgroupCongr hm).surjective.comp
      ((ordinaryCentralizerProjection A).subgroupMap_surjective L)).comp φ.surjective
  by_cases hsquare : IsSquare lambda.val
  · left
    obtain ⟨b, -, hr, hs, hrs, e, -, hscal, -⟩ :=
      square_projective_centralizer_structure n hn A lambda htwo hne hsq hsquare
    rcases ivk93l_block hr hs e hL with ⟨h2r, e₁⟩ | ⟨h2s, e₁⟩
    · obtain ⟨φ⟩ := ivk93l_equiv_fst e e₁
      obtain ⟨ψ, hψ⟩ := hsurj φ
      exact ⟨_, h2r, by omega, ψ, hψ⟩
    · obtain ⟨φ⟩ := ivk93l_equiv_snd e e₁
      obtain ⟨ψ, hψ⟩ := hsurj φ
      exact ⟨_, h2s, by omega, ψ, hψ⟩
  · right
    have : Fact (¬ IsSquare lambda.val) := ⟨hsquare⟩
    have : Finite (CatalogueBProjectiveQuadratic.extension lambda.val) :=
      quadraticExtension_finite lambda.val
    have hdim := CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A lambda hsq hsquare
    let m := CatalogueBProjectiveQuadratic.matrixDimension A lambda hsq
    have hm1 : 1 ≤ m := CatalogueBProjectiveQuadratic.matrixDimension_pos A lambda hsq
    have hnm : n = 2 * m := hdim.1
    let e := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A lambda hsq
    obtain ⟨h2m, -, -, k₁, -⟩ := CatalogueBGeneralLinear.pComponent_classification m
      (CatalogueBProjectiveQuadratic.extension lambda.val) hm1 2 _
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hL)
    have hcardE : Nat.card (CatalogueBProjectiveQuadratic.extension lambda.val) = Nat.card F ^ 2 := by
      let : Fintype F := Fintype.ofFinite F
      let : Fintype (CatalogueBProjectiveQuadratic.extension lambda.val) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
        CatalogueBProjectiveQuadratic.extension_finrank]
    obtain ⟨φ⟩ : Nonempty (SL(m, CatalogueBProjectiveQuadratic.extension lambda.val) ≃* ↥L) :=
      ⟨((L.equivMapOfInjective e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr k₁).trans (rangeEquivSpecialLinear m _))).symm⟩
    obtain ⟨ψ, hψ⟩ := hsurj φ
    exact ⟨_, inferInstance, inferInstance, m, hcardE, h2m, hnm.symm, ψ, hψ⟩

theorem ivk93cov_psl_false {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) {m : ℕ}
    (hm : 2 ≤ m) (hm5 : m ≤ 5) {x : StatedProj (StatedSL m F)} {n : ℕ}
    {B : Subgroup (StatedProj (StatedSL m F))} (h : Ivk93Cov x n B) : False := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin m) F) :=
    Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective
  set φ := CatFactsL4U4.projToPGL m F with hφdef
  have hφ : Function.Injective φ := CatFactsL4U4.projToPGL_injective m
  have := projToPGL_range_normal m F
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (φ x)
  have hx2 : x ^ 2 = 1 := by rw [← h.ord, pow_orderOf_eq_one]
  have hne : Matrix.ProjGenLinGroup.mk A ≠ 1 := by
    rw [hA]
    intro h1
    exact h.ne_one (hφ (h1.trans (map_one φ).symm))
  have hinv : Matrix.ProjGenLinGroup.mk A ^ 2 = 1 := by
    rw [hA, ← map_pow, hx2, map_one]
  obtain ⟨hKle, hK⟩ := isPComponent_map_of_normal φ hφ h.le h.comp.2
  rw [← hA] at hK hKle
  have htwo : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  let χ : ↥((B.map φ).subgroupOf (centralizer ({Matrix.ProjGenLinGroup.mk A} : Set _))) →* ↥B :=
    ((B.equivMapOfInjective φ hφ).symm.toMonoidHom).comp
      (Subgroup.subgroupOfEquivOfLe hKle).toMonoidHom
  have hχ : Function.Surjective χ :=
    (B.equivMapOfInjective φ hφ).symm.surjective.comp (Subgroup.subgroupOfEquivOfLe hKle).surjective
  rcases ivk93cov_pgl_block htwo hm A hne hinv hK with
    ⟨a, ha2, ha, ψ, hψ⟩ | ⟨E, _, _, m', hE, hm2, hmm, ψ, hψ⟩
  · exact h.false_of_surj_sl hodd ha2 (by omega) (χ.comp ψ) (hχ.comp hψ)
  · have hm' : m' = 2 := by omega
    subst hm'
    have hoddE : Odd (Nat.card E) := by
      rw [hE]
      exact hodd.pow
    have h3 : 3 ≤ Nat.card F := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      obtain ⟨k, hk⟩ := hodd
      omega
    have h5 : 5 ≤ Nat.card E := by
      rw [hE]
      nlinarith
    exact h.false_of_surj_sl2 hoddE h5 (χ.comp ψ) (hχ.comp hψ)

theorem ivk93cov_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 4 p f) := by
  intro p f hp hp2 hf _
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have : Finite (StatedProj (StatedSL 4 F)) := Finite.of_equiv _ e.toEquiv
  exact ivk93cov_psl_false hodd (by norm_num) (by norm_num) (hc.of_equiv e)

theorem ivk93cov_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f hp hf hmod
  refine ivk93cov_empty_of_cfg fun J _ _ hJ x _ n B hc => ?_
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact Nat.odd_iff.mpr (by omega)
  have : Finite (StatedProj (StatedSL 5 F)) := Finite.of_equiv _ e.toEquiv
  exact ivk93cov_psl_false hodd (by norm_num) (by norm_num) (hc.of_equiv e)

end CFSG.GH74.GLS.IVK.Proofs2
