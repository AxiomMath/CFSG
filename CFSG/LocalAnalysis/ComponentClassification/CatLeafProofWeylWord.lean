module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofAdjointRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLeviFrame

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)

theorem mulAut_conj_mul_toMonoidHom {G : Type*} [Group G] (a b : G) :
    (MulAut.conj (a * b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
  ext x
  simp [mul_assoc]

@[expose] def wordReflect (τ : Tag) (ω : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ) :
    Fin τ.rank → ℤ :=
  ω.foldr (reflect τ) γ

theorem isRoot_wordReflect {τ : Tag} (ω : List (Fin τ.rank)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : IsRoot τ (wordReflect τ ω γ) := by
  induction ω with
  | nil => exact hγ
  | cons i ω ih => exact IsRoot.reflect i ih

@[expose] def weylWordElt (τ : Tag)
    (K : Type) [Field K] (ω : List (Fin τ.rank)) : adjointGroup τ K :=
  (ω.map (CFSG.LieType.Chevalley.weylElement τ K)).prod

theorem map_conj_weylWordElt_rootPair
    {τ : Tag} {K : Type} [Field K] (ω : List (Fin τ.rank)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    ((adjDatum (rootOperatorFamily τ) K).rootGroup γ ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-γ)).map
        (MulAut.conj (weylWordElt τ K ω)).toMonoidHom =
      (adjDatum (rootOperatorFamily τ) K).rootGroup (wordReflect τ ω γ) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-wordReflect τ ω γ) := by
  induction ω with
  | nil =>
    have h1 : (MulAut.conj (weylWordElt τ K [])).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [weylWordElt]
    rw [h1, Subgroup.map_id]
    rfl
  | cons i ω ih =>
    rw [show weylWordElt τ K (i :: ω) =
        CFSG.LieType.Chevalley.weylElement τ K i * weylWordElt τ K ω from List.prod_cons,
      mulAut_conj_mul_toMonoidHom, ← Subgroup.map_map, ih,
      map_conj_weylElement_rootPair_adj i (isRoot_wordReflect ω hγ)]
    rfl

theorem weylWordElt_mem_iSup
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (ι : Fin r → Fin τ.rank) (ω : List (Fin τ.rank))
    (hω : ∀ i ∈ ω, i ∈ Set.range ι) :
    weylWordElt τ K ω ∈ ⨆ k, rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup (ι k) := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  obtain ⟨k, rfl⟩ := hω i hi
  exact Subgroup.mem_iSup_of_mem k
    (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily τ) (ι k))

theorem commute_weylWordElt
    {τ : Tag} {K : Type} [Field K]
    {C : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan (adjDatum (rootOperatorFamily τ) K).isFiniteType
      (adjDatum (rootOperatorFamily τ) K).divisible)}
    (hE : ChevalleyExtras (adjDatum (rootOperatorFamily τ) K) K (xPar (rootOperatorFamily τ)) C O)
    {j : Fin τ.rank} (ω : List (Fin τ.rank))
    (hω : ∀ i ∈ ω, i ≠ j ∧ τ.cartan i j = 0 ∧ τ.cartan j i = 0) {y : adjointGroup τ K}
    (hy : y ∈ rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup j) :
    Commute (weylWordElt τ K ω) y := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hne, h1, h2⟩ := hω i hi
  exact commutes_rankOne_of_cartan_eq_zero hE rfl hne h1 h2 _
    (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily τ) i) y hy

end CFSG.ComponentClassification.CatLeafProof
