module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.OverSSym
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.NatMultiDefs

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem agl81I516NatMulti_of (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hB : NatMultiBaumStab) (hC : KPCardOne) (hSym : AGL81I516SymOver) : AGL81I516NatMulti := by
  intro X _ _ T hX C₁ C₂ hP L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hnat hall
  exact parabolic_of_baum_le_gnStab' hE hK hX hP hL hch hPb
    (hB X T hX L hL hch P hPb H₁ M₁ hTH hmap hmin hF hJ hV hnat hall)
    (hC X T hX L hL hch P hPb) hSym

theorem agl81I516Hard_of_inputs (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hB : NatMultiBaumStab) (hC : KPCardOne) (hSym : AGL81I516SymOver) : AGL81I516Hard :=
  agl81I516Hard_of_branches (agl81I516NatMulti_of hE hK hB hC hSym) (agl81I516Sym_of_over hSym)

theorem agl81I516_of_inputs (hE : E23NonsolvGen) (hK : KFactChevMinParabolic)
    (hB : NatMultiBaumStab) (hLP : KFactChevMinParabolicLevi) (hSym : AGL81I516SymOver) :
    GN.AGL81I516 :=
  agl81I516_of_hard hE hK (agl81I516Hard_of_inputs hE hK hB (kPCardOne_of_levi hK hLP) hSym)

end CFSG.AGLEmbeddingD2.Tits.GN516
