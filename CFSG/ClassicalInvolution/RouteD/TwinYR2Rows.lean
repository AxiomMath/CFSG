module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

local notation "𝒞" => CoreAssembly.conjClass

@[expose] def TwinRow.large (tY : StatedLieTag) (nY : ℕ) : Prop :=
  (tY = .POmegaPlus ∧ 5 ≤ nY) ∨ (tY = .POmegaMinus ∧ 5 ≤ nY) ∨ (tY = .POmegaOdd ∧ 4 ≤ nY)

section Statements

variable (p f : ℕ) [Fact p.Prime] (P : StatedLieTag → ℕ → Prop)

@[expose] def TwinYP1On : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      P t n → LocalShapeT p f 2 t n (𝒞 K) z → ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z →
        IsClassicalMember p f T z → ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u}

@[expose] def TwinYTypeOn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      P t n → LocalShapeT p f 2 t n (𝒞 K) z → ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z →
        IsClassicalMember p f T z → ∀ e : TwinElt K T z, LocalOddCentral (𝒞 K) {e.u} →
          LocalShapeT p f 0 (twinYModel (p ^ f) t n).1 (twinYModel (p ^ f) t n).2 (𝒞 K) e.u

@[expose] def TwinYPartnerOn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (t : StatedLieTag) (n : ℕ), TwinRow t n →
      P t n → LocalShapeT p f 2 t n (𝒞 K) z →
      ∃ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
        (β : Subgroup G) (s : G), TwinYConfig p f (𝒞 K) K T z e J J' w e' β s

@[expose] def TwinYGenTOn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} → J ≠ K → J ≠ T →
        IsClassicalMember p f J t →
        CentralizerGenerationStar (𝒞 K) (Subgroup.closure ({z, e.u, t} : Set G)) t

@[expose] def TwinYTransitiveOn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ K₁ ∈ locFamily (𝒞 K) e.u, ∀ L ∈ locFamily (𝒞 K) e.u,
        ∃ g : locQuot (𝒞 K) e.u, conjSub g K₁ = L

@[expose] def TwinYRankOn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : StatedLieTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z → ∀ e : TwinElt K T z,
      ∀ D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u), D.card = 1 →
        ∀ i : Fin D.card, (∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i)) →
          D.tag i = (twinYModel (p ^ f) tY nY).1 ∧ D.rank i = (twinYModel (p ^ f) tY nY).2

variable {p f P}

theorem TwinYP1.on (h : TwinYP1 p f) : TwinYP1On p f P :=
  fun G _ _ _ hnab K z S t n hrow _ hshape T hT clsT e =>
    h G hnab K z S t n hrow hshape T hT clsT e

theorem TwinYType.on (h : TwinYType p f) : TwinYTypeOn p f P :=
  fun G _ _ _ hnab K z S t n hrow _ hshape T hT clsT e hP1 =>
    h G hnab K z S t n hrow hshape T hT clsT e hP1

theorem TwinYPartner.on (h : TwinYPartner p f) : TwinYPartnerOn p f P :=
  fun G _ _ _ hnab K z S t n hrow _ hshape => h G hnab K z S t n hrow hshape

theorem TwinYGenT.on (h : TwinYGenT p f) : TwinYGenTOn p f P :=
  fun G _ _ _ hnab K z S tY nY hrow _ hshape T hT clsT e J t hJ hJK hJT hJt =>
    h G hnab K z S tY nY hrow hshape T hT clsT e J t hJ hJK hJT hJt

theorem TwinYTransitive.on (h : TwinYTransitive p f) : TwinYTransitiveOn p f P :=
  fun G _ _ _ hnab K z S tY nY hrow _ hshape T hT clsT e =>
    h G hnab K z S tY nY hrow hshape T hT clsT e

theorem TwinYRank.on (h : TwinYRank p f) : TwinYRankOn p f P :=
  fun G _ _ _ hnab K z S tY nY hrow _ hshape T hT clsT e =>
    h G hnab K z S tY nY hrow hshape T hT clsT e

theorem TwinYP1On.of_true (h : TwinYP1On p f fun _ _ => True) : TwinYP1 p f :=
  fun G _ _ _ hnab K z S t n hrow hshape T hT clsT e =>
    h G hnab K z S t n hrow trivial hshape T hT clsT e

theorem TwinYTypeOn.of_true (h : TwinYTypeOn p f fun _ _ => True) : TwinYType p f :=
  fun G _ _ _ hnab K z S t n hrow hshape T hT clsT e hP1 =>
    h G hnab K z S t n hrow trivial hshape T hT clsT e hP1

theorem TwinYTransitiveOn.of_true (h : TwinYTransitiveOn p f fun _ _ => True) :
    TwinYTransitive p f :=
  fun G _ _ _ hnab K z S tY nY hrow hshape T hT clsT e =>
    h G hnab K z S tY nY hrow trivial hshape T hT clsT e

end Statements

end CFSG.ClassicalInvolution.RouteD.TwinY
