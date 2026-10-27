module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped commutatorElement

theorem commute_of_mem_rootGroup_of_noG2
    {τ : Tag} {K : Type} [Field K] (hτ : NoG2 τ) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ = 0)
    (hsum : ¬ IsRoot τ (γ + δ)) {x y : adjointGroup τ K}
    (hx : x ∈ rootGroup (rootOperatorFamily τ) K γ)
    (hy : y ∈ rootGroup (rootOperatorFamily τ) K δ) : Commute x y := by
  have hlin : LinIndepPair γ δ := by
    by_contra h
    rcases CFSG.LieType.Steinberg.TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    exacts [hne h', hne' h']
  have hcone : openCone (adjDatum (rootOperatorFamily τ) K).roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ε ⟨hε, m, n, hm, hn, hεe⟩ => ?_
    rw [mem_adjDatum_roots, hεe] at hε
    rcases exponent_pair_cases hτ hγ hδ hne hne' hm hn hε with
      ⟨rfl, rfl⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact hsum (by simpa using hε)
    · rw [h0] at h; omega
    · rw [h0] at h; omega
  have key := commutator_mem_openCone_of_linIndepPair hγ hδ hlin hx hy
  rw [hcone] at key
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at key
  exact commutatorElement_eq_one_iff_commute.1 key

theorem commutes_rootPair_of_noG2
    {τ : Tag} {K : Type} [Field K] (hτ : NoG2 τ) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ = 0)
    (hpp : ¬ IsRoot τ (γ + δ)) (hpm : ¬ IsRoot τ (γ + -δ)) :
    Commutes (rootGroup (rootOperatorFamily τ) K γ ⊔ rootGroup (rootOperatorFamily τ) K (-γ))
      (rootGroup (rootOperatorFamily τ) K δ ⊔ rootGroup (rootOperatorFamily τ) K (-δ)) := by
  have c : ∀ {a b : Fin τ.rank → ℤ}, IsRoot τ a → IsRoot τ b → a ≠ b → a ≠ -b →
      iform a b = 0 → ¬ IsRoot τ (a + b) →
      Commutes (rootGroup (rootOperatorFamily τ) K a) (rootGroup (rootOperatorFamily τ) K b) :=
    fun ha hb h1 h2 h3 h4 x hx y hy =>
      (commute_of_mem_rootGroup_of_noG2 hτ ha hb h1 h2 h3 h4 hx hy).eq
  have hneg : ∀ v : Fin τ.rank → ℤ, ¬ IsRoot τ v → ¬ IsRoot τ (-v) :=
    fun v hv h => hv (by simpa using IsRoot.neg h)
  rw [ClassicalInvolution.RouteD.commutes_sup_left, ClassicalInvolution.RouteD.commutes_sup_right,
    ClassicalInvolution.RouteD.commutes_sup_right]
  refine ⟨⟨c hγ hδ hne hne' h0 hpp, c hγ (IsRoot.neg hδ) hne' (by rwa [neg_neg])
      (by rw [iform_neg_right, h0, neg_zero]) hpm⟩,
    ⟨c (IsRoot.neg hγ) hδ (fun h => hne' (by rw [← h, neg_neg]))
      (fun h => hne (neg_injective h)) (by rw [iform_neg_left, h0, neg_zero])
      (by have := hneg _ hpm; rwa [neg_add, neg_neg] at this),
     c (IsRoot.neg hγ) (IsRoot.neg hδ) (fun h => hne (neg_injective h))
      (fun h => hne' (by rw [neg_neg] at h; rw [← h, neg_neg]))
      (by rw [iform_neg_left, iform_neg_right, h0, neg_zero, neg_zero])
      (by have := hneg _ hpp; rwa [neg_add] at this)⟩⟩

theorem adj_refl_eq_reflect
    {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    (RootSystem.ofCartan (adjDatum (rootOperatorFamily τ) K).isFiniteType
      (adjDatum (rootOperatorFamily τ) K).divisible).refl i γ = reflect τ i γ := by
  have hs : CFSG.LieType.RootSystem.weylAction (adjDatum (rootOperatorFamily τ) K).isFiniteType
      ((CFSG.LieType.RootSystem.coxeterMatrix
        (adjDatum (rootOperatorFamily τ) K).isFiniteType).toCoxeterSystem.simple i) γ =
      (RootSystem.ofCartan (adjDatum (rootOperatorFamily τ) K).isFiniteType
        (adjDatum (rootOperatorFamily τ) K).divisible).refl i γ := by
    rw [CFSG.LieType.RootSystem.weylAction_simple]
    rfl
  rw [← hs, CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
  rfl

theorem map_conj_weylElement_rootGroup_adj
    {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ((adjDatum (rootOperatorFamily τ) K).rootGroup γ).map
        (MulAut.conj (weylElement τ K i)).toMonoidHom =
      (adjDatum (rootOperatorFamily τ) K).rootGroup (reflect τ i γ) := by
  rw [CFSG.LieType.Steinberg.map_conj_rootGroup (adjDatum_isCTGroupDatum _ K) i
    (mem_adjDatum_roots.2 hγ), adj_refl_eq_reflect]

theorem map_conj_weylElement_rootPair_adj
    {τ : Tag} {K : Type} [Field K] (i : Fin τ.rank) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ((adjDatum (rootOperatorFamily τ) K).rootGroup γ ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-γ)).map
        (MulAut.conj (weylElement τ K i)).toMonoidHom =
      (adjDatum (rootOperatorFamily τ) K).rootGroup (reflect τ i γ) ⊔
        (adjDatum (rootOperatorFamily τ) K).rootGroup (-reflect τ i γ) := by
  rw [Subgroup.map_sup, map_conj_weylElement_rootGroup_adj i hγ,
    map_conj_weylElement_rootGroup_adj i (IsRoot.neg hγ), reflect_neg]

theorem map_subtype_iSup_rankOne
    {τ : Tag} {K : Type} [Field K] {r : ℕ} (ι : Fin r → Fin τ.rank) :
    (⨆ k, rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup (ι k)).map
        (adjointGroup τ K).subtype =
      subsystemGroup τ K (Set.range ι) := by
  rw [Subgroup.map_iSup]
  simp only [map_subtype_rankOne_rootGroup]
  refine le_antisymm (iSup_le fun k => (Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup (A := Set.range ι) ⟨k, rfl⟩ c
    · exact yUnit_mem_subsystemGroup (A := Set.range ι) ⟨k, rfl⟩ c
  · rintro _ ⟨i, ⟨k, rfl⟩, c, rfl | rfl⟩
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))

theorem map_conj_toralCentralizer_of_maskAct
    {τ : Tag} {K : Type} [Field K] (hK : ringChar K ≠ 2)
    (ω : List (Fin τ.rank)) (b : Fin τ.rank → Bool) :
    (toralCentralizer τ K (bitsTuple b)).map
        (MulAut.conj
          (canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω))).toMonoidHom =
      toralCentralizer τ K (bitsTuple (maskAct ω b)) := by
  refine map_conj_canonicalRep_toralCentralizer _ _ _ fun v => ?_
  rw [rootChar_eq_intUnitsMap hK (bitsTuple_mem _), rootChar_eq_intUnitsMap hK (bitsTuple_mem _),
    signTupleBits_bitsTuple hK, signTupleBits_bitsTuple hK, maskChar_maskAct, inv_smul_smul]

end CFSG.ComponentClassification.CatLeafProof
