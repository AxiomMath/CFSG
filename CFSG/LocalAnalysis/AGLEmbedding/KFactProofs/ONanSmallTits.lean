module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.Sporadic.Schreier.TitsCert
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Sporadic.Schreier.Tits


theorem nonempty_equiv_tits {K : Type} [Group K] (hK : IsTitsGroup K) : Nonempty (K ≃* titsD) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hK
  simp only at hd
  subst hd
  exact CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)

theorem card_of_isTitsGroup {K : Type} [Group K] (hK : IsTitsGroup K) :
    Nat.card K = 17971200 := by
  obtain ⟨e⟩ := nonempty_equiv_tits hK
  rw [Nat.card_congr e.toEquiv]
  exact card_titsD

theorem sylowSq_of_isTitsGroup {K : Type} [Group K] [Finite K] (hK : IsTitsGroup K) :
    SylowSq 5 K := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro T
  have h := card_of_isTitsGroup hK
  exact card_sylow_eq_pow_of_card_eq (k := 2) (m := 718848) (by rw [h]; norm_num)
    (by norm_num) T

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
