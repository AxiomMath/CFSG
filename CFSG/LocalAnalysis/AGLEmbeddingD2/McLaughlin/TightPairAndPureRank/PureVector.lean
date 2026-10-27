module

public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Quasithin.Background.A1cModuleBridge
public import CFSG.Quasithin.Background.A1cModuleHomog
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.G10FifteenRing
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.E11Stmt
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import CFSG.Quasithin.Background.E11Cent
public import CFSG.Quasithin.Background.E11End
public import CFSG.Foundations.Catalog
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.E11Scalar
public import CFSG.Quasithin.Background.G10Local

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section E11Part

variable {A B : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

open CFSG.Quasithin.G11.E11
open scoped CFSG.Quasithin.G11.E11

end E11Part

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
