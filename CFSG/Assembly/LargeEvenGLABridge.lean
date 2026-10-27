module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Open.GLADefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.Assembly.LargeEven

theorem largeEvenTwoLocalRank_eq_glaTwoLocalRank (p : ℕ) (G : Type*) [Group G] [Finite G] :
    LargeEvenTwoLocalRank p G = CFSG.Open.GLATwoLocalRank p G :=
  rfl

theorem largeEvenBeta_eq_glaBeta (k : ℕ) (G : Type*) [Group G] [Finite G] :
    LargeEvenBeta k G = CFSG.Open.GLABeta k G :=
  rfl

theorem largeEvenWeakCoreLocal_iff_glaWeakCoreLocal (G : Type*) [Group G] [Finite G] (p : ℕ) :
    LargeEvenWeakCoreLocal G p ↔ CFSG.Open.GLAWeakCoreLocal G p :=
  Iff.rfl

theorem largeEvenGF2Type_iff_glaGF2Type (G : Type*) [Group G] [Finite G] :
    LargeEvenGF2Type G ↔ CFSG.Open.GLAGF2Type G :=
  Iff.rfl

section Local

variable {G : Type*} [Group G]

theorem largeEvenLayer_eq_glaLayer (H : Subgroup G) :
    LargeEvenLayer H = CFSG.Open.GLALayer H :=
  congrArg sSup (Set.ext fun _ => isComponentOf_iff_open)

theorem largeEvenPComponent_iff_glaPComponent (p : ℕ) (X L : Subgroup G) :
    LargeEvenPComponent p X L ↔ CFSG.Open.GLAPComponent p X L :=
  and_congr_right' <| and_congr isSubnormal_iff_open <| and_congr isComponentOf_iff_open <|
    forall_congr' fun _ => imp_congr_right fun _ => imp_congr_left isSubnormal_iff_open

theorem largeEvenPLayer_eq_glaPLayer (p : ℕ) (X : Subgroup G) :
    LargeEvenPLayer p X = CFSG.Open.GLAPLayer p X :=
  congrArg sSup (Set.ext fun L => largeEvenPComponent_iff_glaPComponent p X L)

theorem largeEvenSStar_iff_glaSStar [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) :
    LargeEvenSStar p B x L ↔ CFSG.Open.GLASStar p B x L :=
  and_congr_right' <| and_congr_right' <| and_congr_right' <|
    and_congr_left' isComponentOf_iff_open

theorem largeEvenSHat_iff_glaSHat [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) :
    LargeEvenSHat p B x L ↔ CFSG.Open.GLASHat p B x L :=
  and_congr_right' <| and_congr_right' <| and_congr_right' <| and_congr_right' <|
    and_congr_left' (largeEvenPComponent_iff_glaPComponent p _ L)

theorem largeEvenStdSubPre_iff_glaStdSubPre (p : ℕ) (B : Subgroup G) (x : G)
    (L D K : Subgroup G) :
    LargeEvenStdSubPre p B x L D K ↔ CFSG.Open.GLAStdSubPre p B x L D K := by
  refine and_congr_right' <| and_congr_right' <| and_congr_right' <| and_congr_right' <|
    and_congr ?_ (and_congr_left' isComponentOf_iff_open)
  rw [largeEvenLayer_eq_glaLayer]

theorem largeEvenStdSub_iff_glaStdSub (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) :
    LargeEvenStdSub p B x L D K ↔ CFSG.Open.GLAStdSub p B x L D K :=
  and_congr (largeEvenStdSubPre_iff_glaStdSubPre p B x L D K) <|
    imp_congr_left <| and_congr_right' <| exists₂_congr fun D₁ K₁ =>
      and_congr_left' (largeEvenStdSubPre_iff_glaStdSubPre p B x L D₁ K₁)

theorem largeEvenNeighbor_iff_glaNeighbor (p : ℕ) (x y : G) (J D K : Subgroup G) :
    LargeEvenNeighbor p x y J D K ↔ CFSG.Open.GLANeighbor p x y J D K := by
  refine and_congr_right' (and_congr_left' ?_)
  rw [largeEvenPLayer_eq_glaPLayer]

theorem largeEvenIsNeighborOf_iff_glaIsNeighborOf [Finite G] (p : ℕ) (B : Subgroup G) (x : G)
    (L : Subgroup G) (y : G) (J : Subgroup G) :
    LargeEvenIsNeighborOf p B x L y J ↔ CFSG.Open.GLAIsNeighborOf p B x L y J :=
  and_congr (largeEvenSHat_iff_glaSHat p B y J) <| exists₂_congr fun D K =>
    and_congr (largeEvenStdSub_iff_glaStdSub p B x L D K)
      (largeEvenNeighbor_iff_glaNeighbor p x y J D K)

end Local

def lieTagEquiv : LargeEvenLieTag ≃ CFSG.Open.GLALieTag :=
  Equiv.refl _

def labelEquiv : LargeEvenLabel ≃ CFSG.Open.GLALabel :=
  Equiv.refl _

theorem largeEvenInLambda2_iff (lab : LargeEvenLabel) :
    LargeEvenInLambda2 lab ↔ CFSG.Open.GLAInLambda2 (labelEquiv lab) :=
  Iff.rfl

theorem largeEvenSplit_iff (p : ℕ) (lab : LargeEvenLabel) :
    LargeEvenSplit p lab ↔ CFSG.Open.GLASplit p (labelEquiv lab) :=
  Iff.rfl

theorem largeEvenHalfSplit_iff (p : ℕ) (lab : LargeEvenLabel) (centerTrivial : Prop) :
    LargeEvenHalfSplit p lab centerTrivial ↔
      CFSG.Open.GLAHalfSplit p (labelEquiv lab) centerTrivial :=
  Iff.rfl

theorem largeEvenPrimeField_iff (p : ℕ) (lab : LargeEvenLabel) {R : Type} [Group R]
    (I F : Set (MulAut R)) (isα : MulAut R → Prop) :
    LargeEvenPrimeField p lab I F isα ↔ CFSG.Open.GLAPrimeField p (labelEquiv lab) I F isα :=
  Iff.rfl

theorem largeEvenIsRoot_eq_glaIsRoot {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    LargeEvenIsRoot A = CFSG.Open.GLAIsRoot A :=
  rfl

theorem largeEvenRecipeChevalley_iff {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (q : ℕ) (d : Bool)
    (Q : LargeEvenRawCont) :
    LargeEvenRecipeChevalley A q d Q ↔ CFSG.Open.GLARecipeChevalley A q d Q :=
  Iff.rfl

theorem largeEvenRecipeTwisted_iff {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (ρ : Equiv.Perm (Fin r)) (m n : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRecipeTwisted A ρ m n Q ↔ CFSG.Open.GLARecipeTwisted A ρ m n Q :=
  Iff.rfl

theorem largeEvenRecipeTwF4_iff (a : ℕ) (Q : LargeEvenRawCont) :
    LargeEvenRecipeTwF4 a Q ↔ CFSG.Open.GLARecipeTwF4 a Q :=
  Iff.rfl

theorem largeEvenRawDatum_iff (lab : LargeEvenLabel) (Q : LargeEvenRawCont) :
    LargeEvenRawDatum lab Q ↔ CFSG.Open.GLARawDatum (labelEquiv lab) Q :=
  Iff.rfl

theorem largeEvenMarking_iff {L : Type*} [Group L] (P : LargeEvenMarkProp L)
    (P' : CFSG.Open.GLAMarkProp L)
    (hP : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : L ⧸ Subgroup.center L ≃* R), P lab R I F θ ↔ P' (labelEquiv lab) R I F θ) :
    LargeEvenMarking L P ↔ CFSG.Open.GLAMarking L P' := by
  obtain rfl : P = P' := by
    funext lab R _ I F θ
    exact propext (hP lab R I F θ)
  rfl

theorem largeEvenStandardType_iff_glaStandardType {G : Type*} [Group G] [Finite G] (p : ℕ)
    (B : Subgroup G) (x : G) (L : Subgroup G) :
    LargeEvenStandardType p B x L ↔ CFSG.Open.GLAStandardType p B x L :=
  largeEvenStandardTypeOf_congr (largeEvenIsNeighborOf_iff_glaIsNeighborOf p B x L)
    (largeEvenStdSub_iff_glaStdSub p B x L) (largeEvenSHat_iff_glaSHat p B)
    (largeEvenNeighbor_iff_glaNeighbor p x) rfl

end CFSG.Assembly.LargeEven
