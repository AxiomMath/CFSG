module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporUniqueRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCentCo2
public import Certificates.Certificate833202

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.Co2Heavy CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Cert CFSG.Blueprint

theorem co2_inv_not_commute_eleven :
    ∀ t z : NativeSporadic.Co2, orderOf t = 2 → orderOf z = 11 → t * z ≠ z * t := by
  intro t z ht hz htz
  refine co2P_inv_not_commute (p := 11) (by norm_num) (by norm_num) (by norm_num)
    (co2PermEquiv t) (co2PermEquiv z) (by rw [MulEquiv.orderOf_eq]; exact ht)
    (by rw [MulEquiv.orderOf_eq]; exact hz) ?_
  rw [← map_mul, ← map_mul, htz]

theorem row_Co2_11 :
    KFactSporLocalRow .Co2 11 := by
  obtain ⟨V₀, H, hV, hHN, hsimp, hnc, hcard⟩ := Certificates.certificate833202
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have e0 : (TauCeti.CFSGIndex.sporadic .Co2).Group ≃* NativeSporadic.Co2 := b.symm
  have h10 : orderOf (2 : ZMod 11) = 10 :=
    orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)
  have k1 := row_of_uniqueRank (s := .Co2) (p := 11) (by decide) NativeSporadic.Co2 ⟨e0.symm⟩
  have k2 := k1 co2_inv_not_commute_eleven V₀ H (by rw [h10]; exact hV)
  exact k2 hHN hsimp hnc (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    (by rw [natCard_Co2]; norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
