module

import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbedding

section Orders

open CFSG.Assembly.LowTwoRank

theorem linTwoEight_data {K : Type} [Group K] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .A 1 q)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    3 ^ 2 ∣ Nat.card K ∧ ∀ E : Subgroup K, IsElementaryAbelian 3 E → Nat.card E ≤ 3 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e1 : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hF : Nat.card (GaloisField q.p q.exponent) = 2 ^ 3 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2, hq3]
  refine ⟨?_, fun E hE => ?_⟩
  · rw [Nat.card_congr e1.toEquiv,
      Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 _).toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
    decide
  · have : CharP (GaloisField q.p q.exponent) 2 := hq2 ▸ inferInstance
    have : NeZero ((3 : ℕ) : GaloisField q.p q.exponent) :=
      NeZero.of_not_dvd (R := GaloisField q.p q.exponent) (p := 2) (by norm_num)
    have := hE
    have hmap := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le Nat.prime_three (by norm_num)
      (E.map e1.toMonoidHom) (IsElementaryAbelian.map (A := E) e1.toMonoidHom)
    rwa [Subgroup.card_map_of_injective e1.injective] at hmap

end Orders

end CFSG.AGLEmbeddingD2
