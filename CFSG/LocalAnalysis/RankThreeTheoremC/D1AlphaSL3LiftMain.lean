module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaSL3LiftInner
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactSL3LiftGenQ : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    (d : TauCeti.ValidLieTypeIndex), IsLinThreeCover3 d → Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    z ∈ Subgroup.center X → z ∈ K → orderOf z = 3 →
    (∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z) →
    Open.pRank 3 (R : Subgroup X) = 3 →
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {k : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (k : X) * f⁻¹ = k} = ⊤

@[expose] def KFactSL3LiftGenFor (c : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Sylow 3 X) (K : Subgroup X) [K.Normal] (z : X)
    (d : TauCeti.ValidLieTypeIndex), IsLinThreeCover3 d → c d → Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    z ∈ Subgroup.center X → z ∈ K → orderOf z = 3 →
    (∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = 3 →
      c ∈ Subgroup.zpowers z) →
    Open.pRank 3 (R : Subgroup X) = 3 →
    ∃ A : Subgroup X, A ≤ (R : Subgroup X) ∧ Open.IsElemAbelian 3 A ∧ 3 ≤ Open.pRank 3 A ∧
      Subgroup.closure {k : K | ∃ f ∈ A, f ∉ Subgroup.centralizer (K : Set X) ∧
        f * (k : X) * f⁻¹ = k} = ⊤

@[expose] def IsLinFourIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 3 ∣ q.card - 1 ∧ q.card = 4

@[expose] def IsLinFieldIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 3 ∣ q.card - 1 ∧ q.card ≠ 4 ∧ 3 ∣ q.exponent

@[expose] def IsLinInnerIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ 3 ∣ q.card - 1 ∧ q.card ≠ 4 ∧ ¬ 3 ∣ q.exponent

@[expose] def IsUnitaryThreeIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ 3 ∣ q.card + 1

theorem isLinThreeCover3_cases {d : TauCeti.ValidLieTypeIndex} (hd : IsLinThreeCover3 d) :
    IsLinFourIndex d ∨ IsLinFieldIndex d ∨ IsLinInnerIndex d ∨ IsUnitaryThreeIndex d := by
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  · by_cases h4 : q.card = 4
    · exact Or.inl ⟨q, hq, h3, h4⟩
    · by_cases he : 3 ∣ q.exponent
      · exact Or.inr (Or.inl ⟨q, hq, h3, h4, he⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨q, hq, h3, h4, he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨q, hq, h3⟩))

@[expose] def KFactSL3LiftGenFour : Prop := KFactSL3LiftGenFor IsLinFourIndex

@[expose] def KFactSL3LiftGenField : Prop := KFactSL3LiftGenFor IsLinFieldIndex

@[expose] def KFactSL3LiftGenUnitary : Prop := KFactSL3LiftGenFor IsUnitaryThreeIndex

theorem kFactSL3LiftGenFor_inner : KFactSL3LiftGenFor IsLinInnerIndex := by
  intro X _ _ R K _ z d _ hin hK ⟨e⟩ hzc hzK hz3 hΩ hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqd, h3, h4, h3e⟩ := hin
  simp only at hqd
  subst hqd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  obtain ⟨-, k, _, _, hkcard, ⟨e'⟩⟩ := hm
  have hcard : Nat.card k = q.card := by rw [hkcard, TauCeti.PrimePower.card_def]
  exact SL3Lift.exists_generating_elemAbelian R K z (by rw [hcard]; exact h3)
    (by rw [hcard]; exact h4) (SL3Lift.no_ringAut_order_three hkcard h3e) hK.1
    ((e'.trans (projectiveSpecialLinearGroupEquivStatedProj 3 k).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k)) hzc hzK hz3 hΩ hrank

theorem kFactSL3LiftGenQ_of_cases (h4 : KFactSL3LiftGenFour) (hf : KFactSL3LiftGenField)
    (hu : KFactSL3LiftGenUnitary) : KFactSL3LiftGenQ := by
  intro X _ _ R K _ z d hd hK he hzc hzK hz3 hΩ hrank
  rcases isLinThreeCover3_cases hd with h | h | h | h
  · exact h4 X R K z d hd h hK he hzc hzK hz3 hΩ hrank
  · exact hf X R K z d hd h hK he hzc hzK hz3 hΩ hrank
  · exact kFactSL3LiftGenFor_inner X R K z d hd h hK he hzc hzK hz3 hΩ hrank
  · exact hu X R K z d hd h hK he hzc hzK hz3 hΩ hrank

theorem kFactSL3LiftGen_of_cases (h4 : KFactSL3LiftGenFour) (hf : KFactSL3LiftGenField)
    (hu : KFactSL3LiftGenUnitary) : KFactSL3LiftGen :=
  kFactSL3LiftGenQ_of_cases h4 hf hu

end CFSG.LocalAnalysis.RankThreeTheoremC
