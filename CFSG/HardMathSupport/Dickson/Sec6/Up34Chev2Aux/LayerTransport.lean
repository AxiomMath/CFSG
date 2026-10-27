module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerMore
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6.I923 CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open scoped commutatorElement

namespace Up34Chev2

theorem noL34Layer_inv_iff {P : Type} [Group P] (ψ : MulAut P) :
    NoL34Layer ψ⁻¹ ↔ NoL34Layer ψ := by
  unfold NoL34Layer
  rw [fixSubgroup_inv_eq]

theorem noL34Layer_of_conj {P : Type} [Group P] [Finite P] (γ f : MulAut P)
    (h : NoL34Layer (γ * f * γ⁻¹)) : NoL34Layer f := by
  have := noL34Layer_conj γ⁻¹ h
  have e : γ⁻¹ * (γ * f * γ⁻¹) * (γ⁻¹)⁻¹ = f := by group
  rwa [e] at this

theorem noL34Layer_of_equiv_normal_simple {P R : Type} [Group P] [Finite P] [Group R]
    (δ : MulAut P) (e : ↥(fixSubgroup δ) ≃* R) (S : Subgroup R) [S.Normal]
    (hsol : Group.IsSolvable (R ⧸ S)) (hs : IsSimpleGroup ↥S) (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (hL34 : ¬ IsLThreeFour ↥S) : NoL34Layer δ := by
  set X := fixSubgroup δ with hX
  set S' : Subgroup ↥X := S.comap e.toMonoidHom with hS'
  haveI : S'.Normal := Subgroup.normal_comap _
  set J : Subgroup P := S'.map X.subtype with hJ
  have hJC : J ≤ X := Subgroup.map_subtype_le S'
  have hJsub : J.subgroupOf X = S' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective S'
  haveI : (J.subgroupOf X).Normal := by rw [hJsub]; infer_instance
  have hsolX : Group.IsSolvable (↥X ⧸ J.subgroupOf X) := by
    refine isSolvable_quotient_of_eq' hJsub.symm ?_
    let f : (↥X ⧸ S') →* (R ⧸ S) := QuotientGroup.map S' S e.toMonoidHom (fun x hx => hx)
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H x =>
        have : e x ∈ S := (QuotientGroup.eq_one_iff _).1 hx
        exact (QuotientGroup.eq_one_iff x).2 this
    exact Group.isSolvable_of_isSolvable_injective hf
  have hSS : S'.map e.toMonoidHom = S := Subgroup.map_comap_eq_self_of_surjective e.surjective S
  let eS' : ↥S' ≃* ↥S :=
    (Subgroup.equivMapOfInjective S' e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hSS)
  let eJ : ↥J ≃* ↥S := (Subgroup.equivMapOfInjective S' X.subtype X.subtype_injective).symm.trans eS'
  haveI := hs
  refine noL34Layer_of_normal_simple δ J hJC hsolX eJ.isSimpleGroup ?_ fun hT =>
    hL34 (IsLThreeFour.of_mulEquiv eJ hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨eJ.symm a, eJ.symm b, fun h => hab (by
    have := congrArg eJ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)⟩

theorem noL34Layer_of_fixed_commutator_equiv {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    {X : Type} [Group X] (e : ↥(commutator ↥(fixSubgroup ψ)) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour X) : NoL34Layer ψ := by
  have eS : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* ↥(commutator ↥(fixSubgroup ψ)) :=
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (fixSubgroup ψ)).symm).trans
      ((commutator ↥(fixSubgroup ψ)).equivMapOfInjective (fixSubgroup ψ).subtype
        (fixSubgroup ψ).subtype_injective).symm
  let e' : ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≃* X := eS.trans e
  haveI : IsSimpleGroup ↥⁅fixSubgroup ψ, fixSubgroup ψ⁆ := e'.isSimpleGroup
  refine noL34Layer_of_simple_commutator ψ _ rfl inferInstance ?_ fun hT =>
    hL34 (IsLThreeFour.of_mulEquiv e' hT)
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e'.symm a, e'.symm b, fun h => hab (e'.symm.injective (by simpa using h))⟩

@[expose] def NoL34Sub {G : Type} [Group G] (D : Subgroup G) : Prop :=
  ∀ A : Subgroup G, GLAPComponent 3 D A → ¬ IsLThreeFour (barOf 3 A)

theorem noL34Sub_of_equiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    {D : Subgroup G} {D' : Subgroup G'} (e : ↥D ≃* ↥D') (h : NoL34Sub D') : NoL34Sub D := by
  intro A hA hT
  have h1 := glaPComponent_subgroupOf Nat.prime_three (le_refl D) hA
  rw [Subgroup.subgroupOf_self] at h1
  have h2 := glaPComponent_map_mulEquiv Nat.prime_three e h1
  rw [Subgroup.map_top_of_surjective _ e.surjective] at h2
  have h3 := CFSG.HardMathSupport.Solomon.Proving.lbUp_component_top_map Nat.prime_three D' h2
  let eA : ↥A ≃* ↥(((A.subgroupOf D).map e.toMonoidHom).map D'.subtype) :=
    (Subgroup.subgroupOfEquivOfLe hA.1).symm.trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (Subgroup.equivMapOfInjective _ D'.subtype D'.subtype_injective))
  exact h _ h3 (IsLThreeFour.of_mulEquiv (barOfEquiv 3 eA) hT)

theorem noL34Layer_of_fixEquiv {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P']
    {ψ : MulAut P} {ψ' : MulAut P'} (e : ↥(fixSubgroup ψ) ≃* ↥(fixSubgroup ψ'))
    (h : NoL34Layer ψ') : NoL34Layer ψ :=
  noL34Sub_of_equiv e h

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
