module

public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.TransportU
public import CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three.Assembly
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.UnitarySplit

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField unitaryIsom3)
open CFSG.HardMathSupport.Foote.ModuleExclusions

@[expose] noncomputable def heisCubeU {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)
    (σ : F ≃+* F) (D X : unitaryIsom3 h) : Subgroup (MulAut (unitaryPSU h 3)) :=
  Subgroup.zpowers (psuField h σ) ⊔
    (Subgroup.zpowers (psuConj h D) ⊔ Subgroup.zpowers (psuConj h X))

theorem modelHyperGen_of_splitDataU {ℓ f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData ℓ f F) (hq3 : 3 ∣ ℓ ^ f + 1) (hq8 : ℓ ^ f ≠ 8) {σ : F ≃+* F}
    (hσ : orderOf σ = 3) {A B : Subgroup (MulAut (unitaryPSU h 3))} (hd : SplitDataU h σ A B)
    (hBc : Nat.card B = 3 ^ 3) : ModelHyperGen 3 B := by
  have hc := closure_hyperplane_fixed_eq_top_u h hq3 hq8 hσ hd (s := 3) (by norm_num) hBc
  unfold ModelHyperGen
  rw [eq_top_iff, ← hc]
  exact Subgroup.closure_mono fun x hx => hx.2

@[expose] def U3ThreeNormalForm : Prop :=
  ∀ (ℓ f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F), 2 < ℓ ^ f → 3 ∣ ℓ ^ f + 1 →
    ℓ ^ f ≠ 8 → ∀ B : Subgroup (MulAut (unitaryPSU h 3)), IsElemAbelian 3 B →
      Nat.card B = 3 ^ 3 →
      ∃ (α : MulAut (unitaryPSU h 3)) (σ : F ≃+* F), orderOf σ = 3 ∧
        ((∃ A : Subgroup (MulAut (unitaryPSU h 3)),
            SplitDataU h σ A (B.map (MulAut.conj α).toMonoidHom)) ∨
         (∃ (lam ω : Fˣ) (D X : unitaryIsom3 h), σ lam = lam ∧ IsPrimitiveRoot (ω : F) 3 ∧
            (D : GL (Fin 3) F) =
              CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F 1 ω (ω ^ 2) ∧
            (X : GL (Fin 3) F) =
              CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.monomGL F lam ∧
            B.map (MulAut.conj α).toMonoidHom = heisCubeU h σ D X))

@[expose] def U3ThreeHeisGen : Prop :=
  ∀ (ℓ f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData ℓ f F), 2 < ℓ ^ f → 3 ∣ ℓ ^ f + 1 →
    ℓ ^ f ≠ 8 → ∀ σ : F ≃+* F, orderOf σ = 3 → ∀ (lam ω : Fˣ) (D X : unitaryIsom3 h),
      σ lam = lam → IsPrimitiveRoot (ω : F) 3 →
      (D : GL (Fin 3) F) =
        CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.diagGL F 1 ω (ω ^ 2) →
      (X : GL (Fin 3) F) =
        CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.monomGL F lam →
      ModelHyperGen 3 (heisCubeU h σ D X)

theorem u3ThreeModelGen_of (hNF : U3ThreeNormalForm)
    (hH : U3ThreeHeisGen) : U3ThreeModelGen := by
  intro ℓ f F _ h hq2 hq3 hq8 B hB hBc
  obtain ⟨α, σ, hσ, hcase⟩ := hNF ℓ f F h hq2 hq3 hq8 B hB hBc
  refine modelHyperGen_of_map_conj α ?_
  have hc' : Nat.card (B.map (MulAut.conj α).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj α).injective, hBc]
  rcases hcase with ⟨A, hd⟩ | ⟨lam, ω, D, X, hlam, hω, hD, hX, heq⟩
  · exact modelHyperGen_of_splitDataU h hq3 hq8 hσ hd hc'
  · rw [heq]
    exact hH ℓ f F h hq2 hq3 hq8 σ hσ lam ω D X hlam hω hD hX

theorem kFactSeitzOuterCubeRankTwoAtPrime_U3_three_of_pieces
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (h3 : 3 ∣ q.card + 1) (hNF : U3ThreeNormalForm) (hH : U3ThreeHeisGen) :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    CFSG.AGLEmbedding.KFactSeitzOuterCubeRankTwoAtPrime ⟨.twistedA 2 q, hv⟩ 3 :=
  kFactSeitzOuterCubeRankTwoAtPrime_U3_three_of_model hv h3 (u3ThreeModelGen_of hNF hH)

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
