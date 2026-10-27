module

public import CFSG.GH74.GLS.Stage4.HexCD4Main

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem hexCoordD4tN :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
      (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
      (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ), 3 ≤ q → p.Prime → Odd q →
        RootOrdersD4a root q → PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 →
        OrthPair root → SharedInv root → LongA2 root → NondegG2 root → NondegD4X13 root →
        ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K) (hK : Nat.card K = q ^ 3)
          (hσq : ∀ c, σ c = c ^ q) (ψ : ∀ i : Fin 6, d43Par σ i → G),
          D4Coords (R.toPre hgen).toSystemOfSimple (sigma_three_of_card hK hσq) ψ := by
  intro G _ _ _ H r₁ r₂ U root R hgen p q hq3 _ hqodd hq hP h1 h4 hO _ hL hnd hnd13
  exact d4_coords R hgen hq3 hqodd hq hP h1 h4 hO hL hnd hnd13

end CFSG.GH74.GLS.Stage4.Hex
