module

public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Basic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Quasithin.SmithCurtis
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open Module
open Representation
open scoped MonoidAlgebra TensorProduct

variable {F : Type*} [Field F] [Finite F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] (ρ : Representation F G V) [IsIrreducible ρ]

theorem isSimpleRep_of_isIrreducible {k G' V' : Type*} [Field k] [Group G']
    [AddCommGroup V'] [Module k V'] (σ : Representation k G' V') [IsIrreducible σ] :
    IsSimpleRep σ := by
  refine ⟨Subrepresentation.irreducible_module_nontrivial σ, fun U hU => ?_⟩
  rcases (inferInstance : IsIrreducible σ).eq_bot_or_eq_top
    (⟨U, fun g u hu => hU g u hu⟩ : Subrepresentation σ) with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

section CurtisType

variable {p : ℕ} [Fact p.Prime] [Finite G] [CharP F p]
  {B : Type*} {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] {cs : CoxeterSystem M Weyl}

omit [CharP F p] in
theorem isCurtisType_chi_mem_endField
    (D : CurtisDatum G cs p)
    (k : Type*) [Field k] [CharP k p] [Algebra (End F[G] ρ.asModule) k]
    {y : k ⊗[End F[G] ρ.asModule] ρ.asModule} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ μ) :
    ∀ h ∈ D.H, ∃ c : End F[G] ρ.asModule,
      χ h = algebraMap (End F[G] ρ.asModule) k c := by
  intro h hh
  let K := End F[G] ρ.asModule
  let W := Theory.Representation.extendScalars k (endFieldRep ρ)
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : FiniteDimensional K ρ.asModule := finiteDimensional_endField ρ
  have : IsIrreducible W := extendScalars_isIrreducible ρ k
  have hsimple : IsSimpleRep W := isSimpleRep_of_isIrreducible W
  have hdim : finrank k (fixSubGen W D.U) = 1 := by
    have hspan := D.fixU_eq_span hsimple ht
    rw [show fixSubGen W D.U = D.fixU W from rfl, hspan, finrank_span_singleton ht.2.1]
  obtain ⟨c, hc⟩ := exists_algebraMap_of_finrank_fixSubGen_eq_one ρ k D.U h
    (D.H_normU h hh) hdim
  refine ⟨c, ?_⟩
  have h1 := hc y (show y ∈ fixSubGen W D.U from ht.1)
  have h2 := ht.2.2.1 h hh
  exact ((smul_left_injective k ht.2.1) (h1.symm.trans h2)).symm

omit [CharP F p] in
theorem isCurtisType_chi_pow_card
    (D : CurtisDatum G cs p)
    (k : Type*) [Field k] [CharP k p] [Algebra (End F[G] ρ.asModule) k]
    {y : k ⊗[End F[G] ρ.asModule] ρ.asModule} {χ : G → k} {μ : B → k}
    (ht : D.IsCurtisType (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ μ)
    {h : G} (hh : h ∈ D.H) :
    χ h ^ Nat.card (End F[G] ρ.asModule) = χ h := by
  obtain ⟨c, hc⟩ := isCurtisType_chi_mem_endField ρ D k ht h hh
  let : Fintype (End F[G] ρ.asModule) := Fintype.ofFinite _
  rw [hc, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end CurtisType

section CoverType

variable {p : ℕ} [Fact p.Prime] [Finite G] [CharP F p]
  {B : Type*} {M : CoxeterMatrix B} {Weyl : Type*} [Group Weyl] [Finite Weyl]
  {cs : CoxeterSystem M Weyl}

omit [CharP F p] in
theorem isCoverType_chi_mem_endField
    {D : CurtisDatum G cs p} {C : CentralCoverData D (MonoidHom.id G) p}
    {Fam : B → Type} [∀ s, Field (Fam s)] [Fintype B] {R : CoverRankOne C Fam}
    (k : Type*) [Field k] [CharP k p] [Algebra (End F[G] ρ.asModule) k]
    (hsplit : SplitOver k D.H)
    {y : k ⊗[End F[G] ρ.asModule] ρ.asModule} {χ : G → k} {J : Finset B}
    (ht : IsCoverType R (Theory.Representation.extendScalars k (endFieldRep ρ)) y χ J) :
    ∀ h ∈ D.H, ∃ c : End F[G] ρ.asModule,
      χ h = algebraMap (End F[G] ρ.asModule) k c := by
  intro h hh
  let W := Theory.Representation.extendScalars k (endFieldRep ρ)
  have : Finite V := Module.finite_iff_finite.mp ‹FiniteDimensional F V›
  have : FiniteDimensional (End F[G] ρ.asModule) ρ.asModule :=
    finiteDimensional_endField ρ
  have : IsIrreducible W := extendScalars_isIrreducible ρ k
  have hsimple : IsSimpleRep W := isSimpleRep_of_isIrreducible W
  have hsplit' : SplitOver k C.datum.H := by
    change SplitOver k (D.H.comap (MonoidHom.id G))
    rwa [Subgroup.comap_id]
  obtain ⟨μ, ht'⟩ := ht.exists_mu (D := D) (π := MonoidHom.id G) (C := C) (R := R)
    hsimple hsplit'
  have hh' : h ∈ C.datum.H := by
    change h ∈ D.H.comap (MonoidHom.id G)
    simpa only [Subgroup.comap_id] using hh
  exact isCurtisType_chi_mem_endField ρ C.datum k ht' h hh'

end CoverType

end CFSG.HardMathSupport.GuralnickMalle
