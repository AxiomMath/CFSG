module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.CentEquiv

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

theorem noGLAP3_of_constrained {G : Type} [Group G] [Finite G] (D Q : Subgroup G) (hQD : Q ≤ D)
    (hQn : ∀ g ∈ D, ∀ n ∈ Q, g * n * g⁻¹ ∈ Q) (hQp : IsPGroup 3 Q)
    (hsol : Group.IsSolvable ↥(D ⊓ Subgroup.centralizer (Q : Set G))) :
    ∀ A : Subgroup G, ¬ GLAPComponent 3 D A := by
  intro A hA
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.AltDown.glaPComponent_commute_of_normal_isPGroup
    Nat.prime_three hA hQD hQn hQp
  have hAD : A ≤ D := hA.1
  have hAC : A ≤ D ⊓ Subgroup.centralizer (Q : Set G) := by
    refine le_inf hAD fun j hj => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hcomm j hj n hn).symm
  haveI : Group.IsSolvable ↥A :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hAC)
  have hne : A ≠ ⊥ := glaPComponent_ne_bot hA
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hne
  have hperf : ⁅A, A⁆ = A := glaPComponent_perfect hA
  haveI : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

theorem exists_glaPComponent_of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {D : Subgroup G} {D' : Subgroup G'} (e : ↥D ≃* ↥D') {A : Subgroup G}
    (hA : GLAPComponent 3 D A) :
    ∃ A' : Subgroup G', GLAPComponent 3 D' A' ∧ Nonempty (barOf 3 A ≃* barOf 3 A') := by
  have h1 := glaPComponent_subgroupOf Nat.prime_three (le_refl D) hA
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := glaPComponent_map_mulEquiv Nat.prime_three e h1
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have h3 := CFSG.HardMathSupport.Solomon.Proving.lbUp_component_top_map Nat.prime_three D' h2
  let eA : ↥A ≃* ↥(((A.subgroupOf D).map e.toMonoidHom).map D'.subtype) :=
    (Subgroup.subgroupOfEquivOfLe hA.1).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (Subgroup.equivMapOfInjective _ D'.subtype D'.subtype_injective))
  exact ⟨_, h3, ⟨barOfEquiv 3 eA⟩⟩

theorem noGLAP3_of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {D : Subgroup G} {D' : Subgroup G'} (e : ↥D ≃* ↥D') (h : ∀ A' : Subgroup G', ¬ GLAPComponent 3 D' A') :
    ∀ A : Subgroup G, ¬ GLAPComponent 3 D A := fun A hA => by
  obtain ⟨A', hA', -⟩ := exists_glaPComponent_of_equiv e hA
  exact h A' hA'

theorem noGLAP3_centralizer_conj {G : Type} [Group G] [Finite G] (h g : G)
    (H : ∀ A : Subgroup G, ¬ GLAPComponent 3 (Subgroup.centralizer ({g} : Set G)) A) :
    ∀ A : Subgroup G, ¬ GLAPComponent 3 (Subgroup.centralizer ({h * g * h⁻¹} : Set G)) A := by
  refine noGLAP3_of_equiv ?_ H
  have e := centralizerEquiv (MulAut.conj h).symm (h * g * h⁻¹)
  have hconj : (MulAut.conj h).symm (h * g * h⁻¹) = g := by
    simp [MulAut.conj_symm_apply, mul_assoc]
  rw [hconj] at e
  exact e

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
