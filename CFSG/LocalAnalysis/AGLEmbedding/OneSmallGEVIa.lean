module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaFi22
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaU33

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem iaResidues_of (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hShp : KFactSmallSylowShape)
    (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hKU2 : KFactUnitarySylowStructure) (hFi6 : KFactFi22GuestRank)
    (hK : CitedBlockToralThree) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInvU : KFactU33SylowInvert) (hAut9 : CitedBlockThreeAutNine)
    (hFA : KFactFi22AltSection) (hPh2 : D1SmallGEVNormalL34Ph2) :
    D1SmallGEVNormalU33 ∧ D1SmallGEVNormalL34Ph ∧ D1SmallGEVNormalFi22 :=
  ⟨d1SmallGEVNormalU33_of hUP hSch hΓ3 hOut hExp hShp hO hKU2 hInvU hK hAut9 h84 h85 h86 h93 hD2,
    d1SmallGEVNormalL34Ph_of_ph2 hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93 hD2 hPh2,
    d1SmallGEVNormalFi22_of hFA hFi6⟩

end CFSG.AGLEmbedding
