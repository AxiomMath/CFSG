module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def b4Root : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 2]

theorem isRoot_b4Root
    : IsRoot .F4 b4Root := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem f4_refl_eq_reflect
    {K : Type} [Field K] (i : Fin (Tag.rank .F4))
    (γ : Fin (Tag.rank .F4) → ℤ) :
    (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible).refl i γ =
      reflect .F4 i γ := by
  have hs : CFSG.LieType.RootSystem.weylAction (f4Datum K).isFiniteType
      ((CFSG.LieType.RootSystem.coxeterMatrix (f4Datum K).isFiniteType).toCoxeterSystem.simple i)
        γ = (RootSystem.ofCartan (f4Datum K).isFiniteType (f4Datum K).divisible).refl i γ := by
    rw [CFSG.LieType.RootSystem.weylAction_simple]
    rfl
  rw [← hs, CFSG.LieType.RootSystem.weylAction_simple, CFSG.LieType.RootSystem.reflection_apply]
  rfl

theorem map_conj_weylElement_rootGroup_F4
    {K : Type} [Field K] (i : Fin (Tag.rank .F4))
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((f4Datum K).rootGroup γ).map (MulAut.conj (weylElement .F4 K i)).toMonoidHom =
      (f4Datum K).rootGroup (reflect .F4 i γ) := by
  rw [CFSG.LieType.Steinberg.map_conj_rootGroup (f4_isCTGroupDatum K) i
    (mem_adjDatum_roots.2 hγ), f4_refl_eq_reflect]

theorem map_conj_weylElement_rootPair_F4
    {K : Type} [Field K] (i : Fin (Tag.rank .F4))
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((f4Datum K).rootGroup γ ⊔ (f4Datum K).rootGroup (-γ)).map
        (MulAut.conj (weylElement .F4 K i)).toMonoidHom =
      (f4Datum K).rootGroup (reflect .F4 i γ) ⊔ (f4Datum K).rootGroup (-reflect .F4 i γ) := by
  rw [Subgroup.map_sup, map_conj_weylElement_rootGroup_F4 i hγ,
    map_conj_weylElement_rootGroup_F4 i (IsRoot.neg hγ), reflect_neg]

theorem reflect_two_single_zero :
    reflect .F4 (f4Node 2) (Pi.single (f4Node 0) 1) = Pi.single (f4Node 0) 1 := by decide
theorem reflect_three_single_zero :
    reflect .F4 (f4Node 3) (Pi.single (f4Node 0) 1) = Pi.single (f4Node 0) 1 := by decide
theorem reflect_three_two_single_one :
    reflect .F4 (f4Node 3) (reflect .F4 (f4Node 2) (Pi.single (f4Node 1) 1)) = b4Root := by
  decide

theorem iform_b4Root_one : iform b4Root (Pi.single (f4Node 1) 1) = 0 := by decide +kernel
theorem iform_b4Root_two : iform b4Root (Pi.single (f4Node 2) 1) = 0 := by decide +kernel
theorem iform_zero_two : iform (Pi.single (f4Node 0) 1 : Fin (Tag.rank .F4) → ℤ)
    (Pi.single (f4Node 2) 1) = 0 := by decide +kernel

theorem b4_root_ne :
    b4Root ≠ Pi.single (f4Node 1) 1 ∧ b4Root ≠ -Pi.single (f4Node 1) 1 ∧
      b4Root ≠ Pi.single (f4Node 2) 1 ∧ b4Root ≠ -Pi.single (f4Node 2) 1 ∧
      (Pi.single (f4Node 0) 1 : Fin (Tag.rank .F4) → ℤ) ≠ Pi.single (f4Node 2) 1 ∧
      (Pi.single (f4Node 0) 1 : Fin (Tag.rank .F4) → ℤ) ≠ -Pi.single (f4Node 2) 1 := by
  decide

theorem not_isRoot_b4_sums
    :
    ¬ IsRoot .F4 (b4Root + Pi.single (f4Node 1) 1) ∧
      ¬ IsRoot .F4 (b4Root + -Pi.single (f4Node 1) 1) ∧
      ¬ IsRoot .F4 (b4Root + Pi.single (f4Node 2) 1) ∧
      ¬ IsRoot .F4 (b4Root + -Pi.single (f4Node 2) 1) ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 0) 1 + Pi.single (f4Node 2) 1) ∧
      ¬ IsRoot .F4 (Pi.single (f4Node 0) 1 + -Pi.single (f4Node 2) 1) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem commutes_rootPair_F4
    {K : Type} [Field K] {γ δ : Fin (Tag.rank .F4) → ℤ}
    (hγ : IsRoot .F4 γ) (hδ : IsRoot .F4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ = 0)
    (hpp : ¬ IsRoot .F4 (γ + δ)) (hpm : ¬ IsRoot .F4 (γ + -δ)) :
    Commutes ((f4Datum K).rootGroup γ ⊔ (f4Datum K).rootGroup (-γ))
      ((f4Datum K).rootGroup δ ⊔ (f4Datum K).rootGroup (-δ)) := by
  have c : ∀ {a b : Fin (Tag.rank .F4) → ℤ}, IsRoot .F4 a → IsRoot .F4 b → a ≠ b → a ≠ -b →
      iform a b = 0 → ¬ IsRoot .F4 (a + b) →
      Commutes ((f4Datum K).rootGroup a) ((f4Datum K).rootGroup b) :=
    fun ha hb h1 h2 h3 h4 x hx y hy =>
      (ClassicalInvolution.RouteD.commute_of_mem_rootGroup_F4 ha hb h1 h2 h3 h4 hx hy).eq
  have hneg : ∀ v : Fin (Tag.rank .F4) → ℤ, ¬ IsRoot .F4 v → ¬ IsRoot .F4 (-v) :=
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

end CFSG.ComponentClassification.CatLeafProof
