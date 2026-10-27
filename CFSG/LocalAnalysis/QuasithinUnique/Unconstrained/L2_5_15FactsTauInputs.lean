module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3Inputs

@[expose] public section

namespace CFSG.QuasithinUnique.Unc25K1

def rcof (x : R9) : R9 :=
  ⟨x.e * x.i - x.f * x.h, x.f * x.g - x.d * x.i, x.d * x.h - x.e * x.g,
   x.c * x.h - x.b * x.i, x.a * x.i - x.c * x.g, x.b * x.g - x.a * x.h,
   x.b * x.f - x.c * x.e, x.c * x.d - x.a * x.f, x.a * x.e - x.b * x.d⟩

@[expose] def d2S : S3 := ⟨!![2,0,0;0,1,0;0,0,2], by decide⟩

@[expose] def x1S : S3 := ⟨!![0,0,1;0,1,1;2,1,1], by decide⟩

@[expose] def invR : List R9 := rawList.filter fun r => r != rone && rmul r r == rone

end CFSG.QuasithinUnique.Unc25K1
