module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUMathieuVanishing
public import CFSG.LocalAnalysis.ComponentClassification.AlternatingUnbalancedDegree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLOutcome
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpVanishing
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition

public section

namespace CFSG.ComponentClassification.CatalogueU

open CFSG.Blueprint Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)

@[expose] def EvenExceptionalCheck : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags →
    ChevalleyExceptionalModel (GeneralizedFitting.subgroup X) t 2 f →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def LargeReeTitsCheck : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (f : ℕ), (t = .twistedF4 ∨ t = .Tits) →
    ReeTitsModel (GeneralizedFitting.subgroup X) t 2 f →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

@[expose] def SporadicNonJ1Check : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup (GeneralizedFitting.subgroup X) →
    (∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) →
    NativeSporadic.SporadicRep (GeneralizedFitting.subgroup X) →
    ¬ Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.J1) →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    OutcomeLocal.UOutcome X

theorem oddLieType_of_classical {Y : Type} [Group Y] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (hp2 : p ≠ 2) (h : StatedClassicalModel Y t n p f) :
    OddLieType Y :=
  ⟨t, n, p, f, h.1.1, hp2, h.1, .inl ⟨ht, h⟩⟩

theorem generalizedFitting_eq_top_of_inner {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (hinner : ∀ φ : MulAut (CFSG.generalizedFitting X), ∃ g, φ = MulAut.conj g) :
    CFSG.generalizedFitting X = ⊤ := by
  set F := CFSG.generalizedFitting X
  have : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hC := centralizer_generalizedFitting_eq_bot_of_simple hsimple hnab
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨g, hg⟩ := hinner (MulAut.conjNormal x)
  have hcent : (g : X)⁻¹ * x ∈ centralizer (F : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h3 : x * y * x⁻¹ = g * y * (g : X)⁻¹ := by
      have h1 := MulAut.conjNormal_apply x ⟨y, hy⟩
      rw [hg] at h1
      exact h1.symm
    calc y * ((g : X)⁻¹ * x) = (g : X)⁻¹ * (g * y * (g : X)⁻¹) * x := by group
      _ = (g : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h3]
      _ = (g : X)⁻¹ * x * y := by group
  rw [hC, mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact g.2

theorem generalizedFitting_eq_top_of_J1 {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a)
    (θ : CFSG.generalizedFitting X ≃* NativeSporadic.J1) : CFSG.generalizedFitting X = ⊤ := by
  refine generalizedFitting_eq_top_of_inner hsimple hnab fun φ => ?_
  obtain ⟨g, hg⟩ := Sporadic.Schreier.at_j1_schreier.2.1 ((θ.symm.trans φ).trans θ)
  refine ⟨θ.symm g, ?_⟩
  ext y
  have h := congrArg (fun ψ : MulAut NativeSporadic.J1 => ψ (θ y)) hg
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h
  congr 1
  apply θ.injective
  rw [h, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem catalogAlmostSimpleUnbalancedOutcome_of_checks (hexc : EvenExceptionalCheck)
    (hree : LargeReeTitsCheck) (hspor : SporadicNonJ1Check) :
    CatalogAlmostSimpleUnbalancedOutcome := by
  intro X _ _ hsimple hnonab hcat hz
  have hF : CFSG.generalizedFitting X = GeneralizedFitting.subgroup X :=
    CFSG.generalizedFitting_eq_componentClassification X
  have hsimple' : IsSimpleGroup (CFSG.generalizedFitting X) := hF ▸ hsimple
  have hnonab' : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := hF ▸ hnonab
  obtain ⟨z, hz2, hcore⟩ := hz
  rcases (Milestones.ct_catalog_nonabelian_type_partition _ hnonab).1 hcat with
    ⟨n, hn, hiso⟩ | hodd | ⟨t, n, f, hadm, hmodel⟩ | hsp
  · rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
    · exact .inl (oddLieType_of_classical (by decide) (by norm_num)
        (LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five _
          hiso))
    · exact .inl (oddLieType_of_classical (by decide) (by norm_num)
        (LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _
          hiso))
    · obtain ⟨hodd, hmod, -⟩ :=
        AlternatingUnbalanced.alternating_generalized_fitting_unbalanced_degree hnonab h7 hiso
          hz2 hcore
      exact .inr (.inl ⟨n, hodd, h7, hiso, hmod⟩)
  · exact .inl hodd
  · rcases hmodel with ⟨ht, hcl⟩ | ⟨-, ht, hex⟩ | ⟨-, ht, hrt⟩ | ⟨-, rfl, hsz⟩
    · have hcl' : StatedClassicalModel (CFSG.generalizedFitting X) t n 2 f := hF ▸ hcl
      simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨hlt, hcase, -, -⟩ :=
          UnbalancedCatalog.even_linear_almost_simple_unbalanced_outcome hnonab' hcl'
            ⟨z, hz2, hcore⟩
        rw [hF] at hlt hcase
        rcases hcase with hodd | h322
        · exact .inl hodd
        · exact .inr (.inr ⟨.inl (.inl ⟨by decide, h322⟩), hlt⟩)
      · exact absurd ((UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing hnonab'
          hcl').2 z hz2) hcore
      · exact absurd ((UnbalancedCatalog.even_symplectic_almost_simple_odd_core_vanishing hnonab'
          hcl').1 z hz2) hcore
      · obtain ⟨-, -, -, hp2⟩ := hcl.1
        exact absurd rfl hp2
      · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inl rfl) hcl').2 z hz2) hcore
      · exact absurd ((UnbalancedCatalog.even_orthogonal_almost_simple_odd_core_vanishing hnonab'
          _ (.inr rfl) hcl').2 z hz2) hcore
    · exact hexc X hsimple hnonab t f ht hex ⟨z, hz2, hcore⟩
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · obtain ⟨-, -, -, h23, -⟩ := hadm
        exact absurd h23 (by norm_num)
      · exact hree X hsimple hnonab _ f (.inl rfl) hrt ⟨z, hz2, hcore⟩
      · exact hree X hsimple hnonab _ f (.inr rfl) hrt ⟨z, hz2, hcore⟩
    · have hsz' : SuzukiModel (CFSG.generalizedFitting X) 2 f := hF ▸ hsz
      exact absurd (UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing hsimple' hnonab'
        hsz' z hz2).2.2 hcore
  · by_cases hJ1 : Nonempty (GeneralizedFitting.subgroup X ≃* NativeSporadic.J1)
    · exfalso
      obtain ⟨θ⟩ := hJ1
      let θ' : CFSG.generalizedFitting X ≃* NativeSporadic.J1 :=
        (MulEquiv.subgroupCongr hF).trans θ
      have htop := generalizedFitting_eq_top_of_J1 hsimple' hnonab' θ'
      let eX : X ≃* NativeSporadic.J1 :=
        (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans θ'
      exact hcore (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨eX⟩ z
        hz2).2.2.2
    · exact hspor X hsimple hnonab hsp hJ1 ⟨z, hz2, hcore⟩

end CFSG.ComponentClassification.CatalogueU
