module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts
public import CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary
public import CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryNormalizerRepresentation

open CFSG.LocalAnalysis.RankThreeUC.Section5 TensorProduct

theorem exists_faithful_image {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ)
    (hEA : CFSG.Open.IsElemAbelian p P) :
    ∃ (J : Type) (_ : Group J) (_ : Finite J) (W : Type) (_ : AddCommGroup W)
      (_ : Module (AlgebraicClosure (ZMod p)) W) (_ : Module.Finite (AlgebraicClosure (ZMod p)) W)
      (τ : Representation (AlgebraicClosure (ZMod p)) J W)
      (f : Subgroup.normalizer (P : Set G) →* J) (ι : Additive P →+ W),
      Function.Injective τ ∧ Function.Surjective f ∧
      Module.finrank (AlgebraicClosure (ZMod p)) W = CFSG.Open.pRank p P ∧
      Function.Injective ι ∧
      Submodule.span (AlgebraicClosure (ZMod p)) (Set.range ι) = ⊤ ∧
      (∀ (g : Subgroup.normalizer (P : Set G)) (x : P),
        ι (Additive.ofMul (P.normalizerMonoidHom g x)) = τ (f g) (ι (Additive.ofMul x))) ∧
      (∀ g : Subgroup.normalizer (P : Set G), f g = 1 ↔ ∀ x ∈ P, (g : G) * x * (g : G)⁻¹ = x) := by
  classical
  have hcommP : ∀ a b : ↥P, a * b = b * a := fun a b => hEA.1.is_comm.comm a b
  letI : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := hcommP }
  have hexp : ∀ x : ↥P, x ^ p = 1 := fun x => Subtype.ext (hEA.2 x x.2)
  letI : Module (ZMod p) (Additive ↥P) := CFSG.LinearAlgebra.CoprimeActions.ElementaryAbelianHyperplaneCounts.moduleOf hexp
  let F := AlgebraicClosure (ZMod p)
  let c : Representation (ZMod p) (Subgroup.normalizer (P : Set G)) (Additive ↥P) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap p
        (MonoidHom.toAdditive (P.normalizerMonoidHom g : ↥P →* ↥P))
      map_one' := by
        ext x
        simp
      map_mul' := fun g h => by
        ext x
        simp }
  let τ0 := CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend (K := F) c
  have hP : Nat.card ↥P = p ^ CFSG.Open.pRank p P := by
    obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt P
    have h1 : Nat.card ↥P ≤ p ^ CFSG.Open.pRank p P := by
      obtain ⟨rank, hrank⟩ := hEA.isPGroup.exists_card_eq
      rw [hrank]
      exact Nat.pow_le_pow_right hp.out.pos
        (CFSG.SectionRank.le_pRank hp.out.one_lt le_rfl hEA hrank)
    have hEle : Nat.card ↥P ≤ Nat.card E := by rw [hEcard]; exact h1
    have := Subgroup.eq_of_le_of_card_ge hEP hEle
    subst this
    exact hEcard
  have hfr : Module.finrank (ZMod p) (Additive ↥P) = CFSG.Open.pRank p P := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive ↥P)
    have h2 : Nat.card (Additive ↥P) = Nat.card ↥P := Nat.card_congr Additive.toMul
    rw [h2, hP, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  have hsurj : Function.Surjective
      (CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.toImage τ0) :=
    CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.toImage_surjective τ0
  haveI : Finite (CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.imageGroup τ0) :=
    Finite.of_surjective _ hsurj
  let ι : Additive ↥P →+ F ⊗[ZMod p] Additive ↥P :=
    (TensorProduct.mk (ZMod p) F (Additive ↥P) 1).toAddMonoidHom
  have hι : Function.Injective ι :=
    Module.Flat.tensorProduct_mk_injective (ZMod p) (Additive ↥P) F
  have hev : ∀ (g : Subgroup.normalizer (P : Set G)) (x : P),
      ι (Additive.ofMul (P.normalizerMonoidHom g x)) = τ0 g (ι (Additive.ofMul x)) := by
    intro g x
    show (1 : F) ⊗ₜ[ZMod p] _ = _
    rw [show ι (Additive.ofMul x) = (1 : F) ⊗ₜ[ZMod p] (Additive.ofMul x) from rfl,
      CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend_tmul]
    rfl
  refine ⟨_, inferInstance, inferInstance, F ⊗[ZMod p] Additive ↥P, inferInstance, inferInstance,
    inferInstance, CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.faithful τ0,
    CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.toImage τ0, ι,
    CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.faithful_injective τ0, hsurj, ?_, hι, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hfr]
  · rw [eq_top_iff]
    intro w _
    induction w using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k a =>
      have : k ⊗ₜ[ZMod p] a = k • ι a := by
        show _ = k • ((1 : F) ⊗ₜ[ZMod p] a)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add u v hu hv => exact Submodule.add_mem _ (hu trivial) (hv trivial)
  · intro g x
    rw [hev]
    exact (CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.faithful_toImage τ0 g).symm ▸ rfl
  · intro g
    have hτ := CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.faithful_toImage τ0 g
    constructor
    · intro h x hx
      rw [h, map_one] at hτ
      have h1 := hev g ⟨x, hx⟩
      rw [← hτ] at h1
      have h2 := hι (h1.trans (Module.End.one_apply _))
      have h3 := congrArg (fun z => ((Additive.toMul z : ↥P) : G)) h2
      exact h3
    · intro h
      apply CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary.faithful_injective τ0
      rw [hτ, map_one]
      have hc : c g = 1 := by
        refine LinearMap.ext fun a => ?_
        apply Additive.toMul.injective
        apply Subtype.ext
        exact h a.toMul a.toMul.2
      show CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend (K := F) c g = 1
      rw [CFSG.LinearAlgebra.CoprimeActions.RepresentationScalarExtensionVocabulary.extend_apply, hc]
      exact LinearMap.baseChange_one _ _

end CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryNormalizerRepresentation
