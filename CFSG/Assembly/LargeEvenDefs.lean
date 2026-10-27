module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.InCatalog
public import CFSG.Open.GeneratedCore
import CFSG.Assembly.GL83LocalCore

public section

namespace CFSG.Assembly

open scoped MatrixGroups

noncomputable section

section Local

variable {G : Type*} [Group G]

@[expose] noncomputable def LargeEvenTwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] : ℕ :=
  gl83_local% CFSG.Assembly.GL83Local.twoLocalRank p G

@[expose] def LargeEvenBeta (k : ℕ) (G : Type*) [Group G] [Finite G] : Set ℕ :=
  gl83_local% CFSG.Assembly.GL83Local.beta LargeEvenTwoLocalRank k G

@[expose] def LargeEvenIsBmax [Finite G] (p : ℕ) (B : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isBmax LargeEvenTwoLocalRank p B

@[expose] def LargeEvenPPrimeCore (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  CFSG.pPrimeCore p H

instance LargeEvenPPrimeCore.normal (p : ℕ) (H : Type*) [Group H] :
    (LargeEvenPPrimeCore p H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def LargeEvenPPrimeCoreOf (p : ℕ) (H : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.pPrimeCoreOf LargeEvenPPrimeCore p H

@[expose] noncomputable def LargeEvenWeakCore [Finite G] (p : ℕ) (P : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.weakCore p P

@[expose] def LargeEvenWeakCoreLocal (G : Type*) [Group G] [Finite G] (p : ℕ) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.weakCoreLocal G LargeEvenWeakCore p

@[expose] def LargeEvenIsMaxTwoLocal (M : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isMaxTwoLocal M

@[expose] def LargeEvenGF2Type (G : Type*) [Group G] [Finite G] : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.gf2Type G LargeEvenIsMaxTwoLocal @LargeEvenSymplecticType
      @LargeEvenIsBmax

@[expose] def LargeEvenLayer (H : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.layer @IsComponentOf H

@[expose] def LargeEvenPComponent (p : ℕ) (X L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.pComponent @IsComponentOf @IsSubnormal LargeEvenPPrimeCore p X
      L

@[expose] def LargeEvenPLayer (p : ℕ) (X : Subgroup G) : Subgroup G :=
  gl83_local% CFSG.Assembly.GL83Local.pLayer LargeEvenPComponent p X

@[expose] def LargeEvenSStar [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.sStar @IsComponentOf @LargeEvenIsBmax p B x L

@[expose] def LargeEvenSHat [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.sHat @LargeEvenIsBmax LargeEvenPComponent
      LargeEvenPPrimeCoreOf p B x L

@[expose] def LargeEvenStdSubPre (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.stdSubPre @IsComponentOf LargeEvenLayer p B x L D K

@[expose] def LargeEvenStdSub (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.stdSub LargeEvenStdSubPre LargeEvenSmall p B x L D K

@[expose] def LargeEvenNeighbor (p : ℕ) (x y : G) (J D K : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.neighbor LargeEvenPLayer LargeEvenPPrimeCoreOf p x y J D K

@[expose] def LargeEvenIsNeighborOf [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (y : G)
    (J : Subgroup G) : Prop :=
  gl83_local% CFSG.Assembly.GL83Local.isNeighborOf (LargeEvenSHat p B) (LargeEvenStdSub p B x L)
      (LargeEvenNeighbor p x) y J

@[expose] def LargeEvenStandardType [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  LargeEvenStandardTypeOf p B x L (LargeEvenIsNeighborOf p B x L) (LargeEvenStdSub p B x L)
    (LargeEvenSHat p B) (LargeEvenNeighbor p x) (LargeEvenPPrimeCoreOf p)

end Local

end

namespace LargeEven

theorem kProper_inCatalog_iff_allSimple (G : Type) [Group G] [Finite G] :
    KProper InCatalog G ↔ KCore.KProperAllSimple InCatalog G :=
  KCore.kProperNonab_iff_kProperAllSimple (C := InCatalog) (X := G)
    inCatalog_isoInvariant inCatalog_containsAbelianSimple

end LargeEven
end CFSG.Assembly

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def LargeEvenRawDatum (lab : LargeEvenLabel) (Q : LargeEvenRawCont) : Prop :=
  match lab.tag with
  | .A => LargeEvenRecipeLinear (lab.rank + 1) (2 ^ lab.n) Q
  | .twA => LargeEvenRecipeUnitary (lab.rank + 1) (2 ^ lab.n) Q
  | .B | .C => LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false Q
  | .B2der => LargeEvenRecipeSymplectic 2 2 true Q
  | .D =>
    if lab.rank = 3 then LargeEvenRecipeLinear 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaPlus lab.rank (2 ^ lab.n) Q
  | .twD =>
    if lab.rank = 2 then LargeEvenRecipeLinear 2 ((2 ^ lab.n) ^ 2) Q
    else if lab.rank = 3 then LargeEvenRecipeUnitary 4 (2 ^ lab.n) Q
    else LargeEvenRecipeOmegaMinus (lab.rank - 1) (2 ^ lab.n) Q
  | .G2 => LargeEvenRecipeChevalley LargeEvenCartanG2 (2 ^ lab.n) false Q
  | .G2der => LargeEvenRecipeChevalley LargeEvenCartanG2 2 true Q
  | .F4 => LargeEvenRecipeChevalley LargeEvenCartanF4 (2 ^ lab.n) false Q
  | .E6 => LargeEvenRecipeChevalley (LargeEvenCartanE 6) (2 ^ lab.n) false Q
  | .E7 => LargeEvenRecipeChevalley (LargeEvenCartanE 7) (2 ^ lab.n) false Q
  | .E8 => LargeEvenRecipeChevalley (LargeEvenCartanE 8) (2 ^ lab.n) false Q
  | .twE6 => LargeEvenRecipeTwisted (LargeEvenCartanE 6) LargeEvenRhoE6 2 lab.n Q
  | .triD4 => LargeEvenRecipeTwisted LargeEvenCartanD4 LargeEvenRhoD4 3 lab.n Q
  | .twB2 => LargeEvenRecipeSuzuki ((lab.n - 1) / 2) Q
  | .twF4 | .twF4der => LargeEvenRecipeTwF4 ((lab.n - 1) / 2) Q

theorem largeEvenRawDatum_legacy (lab : LargeEvenLabel) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum lab Q ↔ CFSG.Assembly.LargeEvenRawDatumLegacy lab Q := Iff.rfl

abbrev LargeEvenMarking := @CFSG.Assembly.LargeEvenMarkingLegacy

@[expose] def LargeEvenStandardType {G : Type*} [Group G] [Finite G]
    (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  CFSG.Assembly.LargeEvenStandardTypeOfLegacy p B x L
    (LargeEvenIsNeighborOf p B x L) (LargeEvenStdSub p B x L)
    (LargeEvenSHat p B) (LargeEvenNeighbor p x) (LargeEvenPPrimeCoreOf p)

namespace Legacy
abbrev LargeEvenRawDatum := CFSG.StandardType.LargeEvenRawDatum
abbrev LargeEvenMarking := @CFSG.Assembly.LargeEvenMarkingLegacy
abbrev LargeEvenStandardType := @CFSG.StandardType.LargeEvenStandardType
end Legacy

namespace Canonical
abbrev LargeEvenRawDatum := CFSG.Assembly.LargeEvenRawDatum
abbrev LargeEvenMarking := @CFSG.Assembly.LargeEvenMarking
abbrev LargeEvenStandardType := @CFSG.Assembly.LargeEvenStandardType
end Canonical

end CFSG.StandardType
