module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.SectionRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

namespace SQTKHypCat

variable {G : Type} [Group G]

theorem isSQTKCat (hG : SQTKHypCat G) : IsSQTKCat G := ⟨hG.sqt, hG.kgroup⟩

theorem subgroup [Finite G] (hG : SQTKHypCat G) (H : Subgroup G) : IsSQTKCat ↥H :=
  ⟨IsStronglyQuasithin.subgroup hG.sqt H, hG.kgroup.subgroup H⟩

theorem rank_top [Finite G] (hG : SQTKHypCat G) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup G) ≤ 2 :=
  isStronglyQuasithin_iff.mp hG.sqt q hq hq2

theorem pRank_le [Finite G] (hG : SQTKHypCat G) (H : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p H ≤ 2 :=
  (pRank_mono hp.one_lt (le_top : H ≤ ⊤)).trans (hG.rank_top hp hp2)

theorem pCoreOf_two_of_subnormal [Finite G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : IsSubnormal L ⊤) : pCoreOf 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := SQTKHyp.pCoreOf_le_of_subnormal 2 hL
  have h2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥ :=
    (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := G))).trans
      ((A3.pCore_eq_openCore 2 G).symm.trans hG.o2)
  rw [h2] at h1
  exact le_bot_iff.mp h1

theorem pCore_two_of_subnormal [Finite G] (hG : SQTKHypCat G) {L : Subgroup G}
    (hL : IsSubnormal L ⊤) : CFSG.pCore 2 ↥L = ⊥ := by
  have h : (CFSG.Open.pCore 2 ↥L).map L.subtype = ⊥ := hG.pCoreOf_two_of_subnormal hL
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h

theorem of_subnormal [Finite G] (hG : SQTKHypCat G) {L : Subgroup G} (hL : IsSubnormal L ⊤) :
    SQTKHypCat ↥L :=
  { finite := inferInstance
    sqt := (hG.subgroup L).1
    kgroup := (hG.subgroup L).2
    o2 := hG.pCore_two_of_subnormal hL }

end SQTKHypCat

theorem A36CoreCat.toStrong {G : Type} [Group G] {L : Subgroup G} (h : A36CoreCat L)
    (hnq : ¬ CFSG.IsQuasisimple ↥L) : A36Strong L := by
  refine ⟨?_, h.2.1, h.2.2⟩
  rcases h.1 with hc | h3 | h4
  · exact absurd hc.1 hnq
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

@[expose] def ThreeCoverFactCat : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → Nat.card (Subgroup.center X) = 3 →
    A23ListCat (X ⧸ Subgroup.center X) → A36Case2List X

@[expose] def A134For (H : Type) [Group H] [Finite H] : Prop :=
  ∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ ≠ L₂ →
    Nonempty (↥L₁ ≃* ↥L₂) →
    (∀ L : Subgroup H, CFSG.IsComponent L → Nonempty (↥L ≃* ↥L₁) → L = L₁ ∨ L = L₂) ∧
    (A134TypesCentral ↥L₁ ∨ (IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3))

@[expose] def A134SQTKFactCat : Prop :=
  ∀ (H : Type) [Group H] [Finite H], SQTKHypCat H → A134For H

@[expose] def A134RankOneFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S], A23ListCat S →
    (∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) → A134Types S

@[expose] def SchreierFactCat : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsKGroupCat X → OutSolvable X

@[expose] def SchreierFactListCat : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → A23ListCat (X ⧸ Subgroup.center X) →
    OutSolvable X

@[expose] def A312ListFactsCat : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
    ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
      A312Case B ⊤

structure A3CoreFactsCat : Prop where
  a134 : A134RankOneFact
  schreier : SchreierFactListCat
  a312list : A312ListFactsCat
  threeCover : ThreeCoverFactCat

abbrev A3FactsCat : Prop := A3CoreFactsCat

end CFSG.QuasithinUnique.Vol2Native
