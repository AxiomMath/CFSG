module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A55Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58S
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A58d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Setup.Family

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace T53

theorem lemma14_5_5_of_F4 (h55 : Lemma14_5_5Q_F4) (h4 : Lemma14_7_4_two_three_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G), Ctx_F4 G T L V V₂ Y →
      pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ := by
  intro G _ _ T L V V₂ Y C
  exact h55 G T L V V₂ Y C.hyp C.hV2 C.hYo C.hYG1 C.hTY C.hS3 C.not_le_M_F4 (C.quot_xT_F4 h4).1
    (C.inf_eq_F4 h4)

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.T53.Ctx_F4

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem isSolvable_hY_F4 (h4 : Lemma14_7_4_two_three_F4) (h55 : Lemma14_5_5Q_F4) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One_F4) (hSym : Lemma14_5_8Sym_F4) : Group.IsSolvable ↥(hY T L V₂ Y) := by
  have hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥ := lemma14_5_5_of_F4 h55 h4 G T L V V₂ Y C
  by_contra hns
  obtain ⟨K, hK⟩ := CFSG.Quasithin.H13.L32A.T53.Ctx.exists_mem_cComp hns
  have hKf := C.faithful_of_mem_cComp_F4 h4 hQ h36 hK
  have hiso := C.quot_of_mem_cComp_F4 h4 hQ h36 h1434 hK
  have hO2 := C.pCoreOf_eq_of_mem_cComp_F4 h4 hQ hK hiso
  obtain ⟨hKn, hHK, ⟨eGL⟩, hXK, hYK⟩ := C.structure_of_mem_cComp_F4 h4 hQ hK hiso
  have hcard := C.card_vH_F4 h4 hQ hK hKn hHK eGL hXK hYK hO2
  have hnat := C.binaryNaturalSL_vH_F4 hQ hK eGL hO2 hcard
  have hE := C.vH_eq_conjClosure_V2_F4 hcard
  have hSL : quasithinO2QuotientIso K (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (quasithinO2QuotientIso_iff _ _).mpr ⟨eGL.trans (slEquivGL 3).symm⟩
  exact hSym G T L V V₂ Y K C.hyp C.hV2 C.hYo C.hYG1 C.hTY C.hS3 C.not_le_M_F4 hQ hK hKf hHK hSL
    hO2 C.V2_le_vH_F4 hE hnat

end Ctx_F4

end T53

end CFSG.Quasithin.H13.L32A
