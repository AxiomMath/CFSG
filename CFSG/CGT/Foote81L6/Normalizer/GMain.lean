module

public import CFSG.CGT.Foote81L6.Normalizer.GDichotomy
public import CFSG.CGT.Foote81L6.MainL6Inputs

public section

namespace CFSG.CGT.Foote81L6

theorem footeLemma8To10_holds (hHig : Normalizer.HigmanHyp) (h3b : FooteNotConjB₀B)
    (h41 : FooteLemma4OneFour) (h5 : FooteLemma5) (h5s : FooteLemma5Sylow) :
    FooteLemma8To10 := by
  intro G _ _ T n D hnA hnAs F hF _ d₀ d₁ hd₀ hd₀F hd₀N hd₁ hd₁F hd₁N
  exact Normalizer.dichotomy D hnA hnAs hHig (h5s G T 2 n D) (h3b G T 2 n D) (h41 G T n D)
    (h5 G T 2 n D) hF hd₀ hd₀F hd₀N hd₁ hd₁F hd₁N

end CFSG.CGT.Foote81L6
