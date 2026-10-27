module

public import CFSG.ClassicalInvolution.Q3.TL3C11R

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

structure TypeRFam (r : ℕ) {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop where
  hyp : HypOmegaGen Φ
  cls : Q3CL.ClassicalClause Φ
  twoGroup : ∀ L ∈ Φ, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)
  quat : ∀ L ∈ Φ, ∀ P : Subgroup X, IsSylow2In P L →
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  tight : ∀ L ∈ Φ, ∀ w : X, IsUniqueInvolution L w →
    Subgroup.centralizer ({w} : Set X) ≤ Subgroup.normalizer (L : Set X)
  noTwins : ∀ L ∈ Φ, ∀ L' ∈ twinSet Φ L, L' = L

@[expose] def TightSec5CliqueR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ B : Fin 5 → Subgroup X, (∀ i, B i ∈ Φ) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) → DConnected Φ

@[expose] def TightSecTriangleR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ B : Fin 3 → Subgroup X, (∀ i, B i ∈ Φ) → Function.Injective B →
        (∀ i j, i ≠ j → B j ∈ omegaNbr Φ (B i)) → T3.DStarConnected Φ

@[expose] def TightBenderEndR : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t →
    BenderSuzuki.IsBenderGroup ↥(genFittingFStar Y) →
      Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ → False

section Cit3


@[expose] def TightConnLeafR' (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R))

theorem tightConnLeafR_of_R' {r n : ℕ} (h : TightConnLeafR' r n) : TightConnLeafR r n :=
  fun Y _ _ R S t hL _ => h Y R S t hL

structure TightStd8R (r n : ℕ) {Y : Type} [Group Y] [Finite Y] (Rd : Subgroup Y)
    (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y) (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y) :
    Prop where
  large : TightLargeHypR r n Y Rd Sd z
  hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)
  ht : IsUniqueInvolution J t
  hR : R ∈ RSet (CoreAssembly.conjClass (tightCore Rd)) ∧ R ≤ tightCore Rd ∧
    R ≤ (S : Subgroup Y)
  hT : T ∈ RSet (CoreAssembly.conjClass (tightCore Rd)) ∧ T ≤ J ∧ T ≤ (S : Subgroup Y)
  hW : W ∈ WSet (CoreAssembly.conjClass (tightCore Rd)) ∧ W ≤ (S : Subgroup Y) ∧
    ∀ s ∈ (S : Subgroup Y), conjSub s W = W

@[expose] def TightC26_2R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ¬ MuIsoS4 (CoreAssembly.conjClass (tightCore Rd)) W

@[expose] def TightC26_13R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ¬ MuIsoWylD4 (CoreAssembly.conjClass (tightCore Rd)) W

@[expose] def TightF26E4R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          Subgroup.centralizer ({z * t} : Set Y) ≤
            sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
