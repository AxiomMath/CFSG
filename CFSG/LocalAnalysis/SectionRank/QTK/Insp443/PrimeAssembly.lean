module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeSplit
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeM22
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.O3Holds
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CoverU43
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafChar2Lie
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafU5Char2
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.L52Leaf
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafM23
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafM24
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafJ3
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafJ4
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafHS
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafHe
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafRu
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafMcL
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.VacuousOdd

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank

theorem for'_itemSporadic_of
    (hM22 : For' (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M22)))
    (hM23 : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M23)))
    (hM24 : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M24)))
    (hJ3 : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J3)))
    (hJ4 : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J4)))
    (hHS : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .HS)))
    (hHe : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .He)))
    (hRu : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .Ru)))
    (hMcL : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .McL))) : For' ItemSporadic := by
  intro G _ _ T M L B Tp VB K hHyp hP
  obtain ⟨s, hs, he⟩ := hP
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (For.toPrime for_M11) G T M L B Tp VB K hHyp he
  · exact (For.toPrime for_M12) G T M L B Tp VB K hHyp he
  · exact hM22 G T M L B Tp VB K hHyp he
  · exact (For.toPrime hM23) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hM24) G T M L B Tp VB K hHyp he
  · exact (For.toPrime for_J1) G T M L B Tp VB K hHyp he
  · exact (For.toPrime for_J2) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hJ3) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hJ4) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hHS) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hHe) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hRu) G T M L B Tp VB K hHyp he
  · exact (For.toPrime hMcL) G T M L B Tp VB K hHyp he

theorem for'_itemSporadic
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : For' ItemSporadic :=
  for'_itemSporadic_of (for'_M22 h37 h38 h39) (for_M23 h37 h38 h39) (for_M24 h37 h38 h39)
    (for_J3 h37 h38 h39) (J4.for_J4 h37 h38 h39) (for_HS h37 h38 h39) (for_He h37 h38 h39)
    (Ru.for_Ru h37 h38 h39) (for_McL h37 h38 h39)

theorem insp443List'_holds :
    Insp443List' :=
  have h37 := a37ForSQTK_proved
  have h38 := a38ForSQTK_proved
  have h39 := a39ForSQTK_proved
  insp443List'_of_items
    (For.toPrime (for_itemAlt_of (Alt.for_A8 h37 h38 h39) (Alt.for_A9 h37 h38 h39)))
    (For.toPrime (for_itemOdd_of_O3 h37 h38 h39 o3Facts_holds u43Covers_holds)) (For.toPrime (for_itemChar2_of (for_L3char2 h37 h38 h39)
        (for_Sp4char2 h37 h38 h39) (for_U4char2 h37 h38 h39) (for_G2char2 h37 h38 h39)
        (for_D4char2 h37 h38 h39) (for_F4char2 h37 h38 h39) (for_U5char2 h37 h38 h39) for_Tits))
    (For.toPrime (L52.for_itemChar2Rank3 h37 h38 h39)) (for'_itemSporadic h37 h38 h39)

end CFSG.SectionRank.QTK.Insp443

end
