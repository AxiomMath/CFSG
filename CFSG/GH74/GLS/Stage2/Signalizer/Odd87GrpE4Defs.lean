module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

structure E4Facts (G : Type) [Group G] (z : G) (k : Kind) : Prop where
  p42 : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ (p : ℕ) (X : Subgroup B),
    Sig4A b (⊤ : Subgroup B) p X → pCore p B = ⊥ → Hyp42 b X → Concl42 k b p X
  two : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J₁ J₂ J₃ : Subgroup B,
    IsComponent J₁ → IsComponent J₂ → IsComponent J₃ → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False
  f3 : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J : Subgroup B, IsComponent J →
    ∀ p n : ℕ, p.Prime → 1 ≤ n → (Odd (p ^ n) ∨ p ^ n = 4) → LieModel (Hat J) .PSL 3 p n →
      ∀ c : B, orderOf c = 2 → c ∈ centralizer (J : Set B) → False
  uinv : ∀ (B : Type) [Group B] [Finite B] (b : B), SecOfG G z B b → ∀ J : Subgroup B, IsComponent J →
    center (Hat J) ≠ ⊥ → ∀ u v : B, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 →
      u ∈ centralizer (J : Set B) → v ∈ centralizer (J : Set B) → u * v = v * u → u = v

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
