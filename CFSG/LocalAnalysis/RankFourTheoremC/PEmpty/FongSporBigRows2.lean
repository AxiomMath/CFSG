module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigSound
public import Certificates.Certificate40342
public import CFSG.Sporadic.Bridge.LySurj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint CFSG.SectionRank

theorem row_Ly_7 :
    KFactSporLocalRow .Ly 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have hW := BClaim.exists_bigW_of_check (specP 5 111) NativeSporadic.LySeed1
    NativeSporadic.LySeed2 ly_7_claims Certificates.certificate40342
  have h11 : orderOf (2 : ZMod 11) = 10 :=
    orderOf_two_zmod_eq 11 10 (by norm_num) (by decide) (by decide)
  exact row_of_bigW (r := 11) NativeSporadic.Ly
    (fun G _ h => by obtain ⟨e⟩ := h; exact ⟨e.trans b.symm⟩) (e := 8) (m := 202207730484375)
    (by rw [CFSG.Sporadic.Ly.card_Ly]; norm_num) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by rw [h11]; norm_num) hW

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
