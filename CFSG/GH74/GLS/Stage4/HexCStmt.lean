module

public import CFSG.GH74.GLS.Stage4.HexCG3

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg.TwistedD4 CFSG.Blueprint
  CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

theorem hexCoordG2tN :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (H : Subgroup G) (r₁ r₂ : G)
      (U : Subgroup G) (root : ℤ → Subgroup G) (R : RGD2 6 H r₁ r₂ U root)
      (hgen : (H ⊔ U) ⊔ R.N = ⊤) (p q : ℕ), p.Prime → Odd q → 5 ≤ q → RootOrdersG2 root q →
        PStruct p U root → SL2At H R.N root 1 → SL2At H R.N root 4 → OrthPair root → SharedInv root →
        LongA2 root → NondegG2 root → (p = 3 → NondegX15 root) →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
          ∃ ψ : Fin 6 → F → G, G2Coords (R.toPre hgen).toSystemOfSimple ψ := by
  intro G _ _ _ H r₁ r₂ U root R hgen p q hp hqodd h5 hq hP h1 h4 hO hZ hL hnd hx
  by_cases hp3 : p = 3
  · subst hp3
    exact g2_coords_p3 R hgen hqodd h5 hq hP h1 h4 hO hL hnd (hx rfl)
  · exact g2_coords_ne3 R hgen hp hqodd hq hP h1 h4 hO hL hnd hp3

end CFSG.GH74.GLS.Stage4.Hex
