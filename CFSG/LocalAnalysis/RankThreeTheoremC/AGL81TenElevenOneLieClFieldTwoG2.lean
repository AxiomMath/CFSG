module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClFieldTwoSU

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open Subgroup

@[expose] def KFactOuterThreeRankTwoG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 → 3 ∣ q.exponent →
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) → Subgroup.center X = ⊥ →
    ∀ H : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ H →
    (∃ α ∈ H, (∃ k : ℕ, α ^ 3 ^ k = 1) ∧ α ∉ (MulAut.conj : X →* MulAut X).range) →
    ∀ E : Subgroup (MulAut X), E ≤ H → IsElemAbelian 3 E → Nat.card E = 9 →
    3 ≤ Open.pRank 3 (H ⊓ centralizer (E : Set (MulAut X)))

theorem kFactOuterThreeRankTwo_of_g2 (h : KFactOuterThreeRankTwoG2) :
    KFactOuterThreeRankTwo := by
  intro X _ _ d hd hl hA2 _ hG he hc H hinn hα E hEH hE hEc
  obtain ⟨d, hv⟩ := d
  cases d with
  | A l q =>
    have h2 := hd.2
    rcases l with _ | _ | _ | _ | _ | l
    · omega
    · omega
    · exact absurd rfl (hA2 q)
    · exact LieClAut.three_le_pRank_typeA hd hl ⟨q, Or.inl rfl⟩ he hc hinn hα hEH hE hEc
    · exact LieClAut.three_le_pRank_typeA hd hl ⟨q, Or.inr rfl⟩ he hc hinn hα hEH hE hEc
    · exact hl.elim
  | twistedA l q =>
    have h2 := hd.2
    rcases l with _ | _ | _ | _ | _ | l
    · omega
    · omega
    · omega
    · exact LieClAut.three_le_pRank_typeTwistedA hd hl ⟨q, Or.inl rfl⟩ he hc hinn hα hEH hE hEc
    · exact LieClAut.three_le_pRank_typeTwistedA hd hl ⟨q, Or.inr rfl⟩ he hc hinn hα hEH hE hEc
    · exact hl.elim
  | B l q =>
    rcases l with _ | _ | _ | l
    · exact hl.elim
    · exact hl.elim
    · exact LieClAut.three_le_pRank_typeB2 hd ⟨q, rfl⟩ he hc hinn hα hEH hE hEc
    · exact hl.elim
  | G2 q => exact h X q hv hd (hG q rfl) he hc H hinn hα E hEH hE hEc
  | _ => exact hl.elim

theorem kFactTenElevenOneLieAutFieldTwo_of_g2 (h : KFactOuterThreeRankTwoG2) :
    KFactTenElevenOneLieAutFieldTwo :=
  kFactTenElevenOneLieAutFieldTwo_of_rankTwo (kFactOuterThreeRankTwo_of_g2 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
