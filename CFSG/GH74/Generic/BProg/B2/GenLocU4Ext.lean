module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMain

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic

namespace GenLocU4Ext

variable {K : Type} [Field K] [Finite K]

theorem gammaAct_su4_ext {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K))
    (hA : IsRank23 A) (ρ : A → GL (Fin 4) K) (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (hab : ∀ a b, ρ a * ρ b = ρ b * ρ a) (a₀ : A) (c : K) (hc : ∀ μ : K, μ ^ (p ^ f + 1) = 1 → μ * μ ≠ c)
    (hsq : (ρ a₀ : Matrix (Fin 4) (Fin 4) K) * (ρ a₀ : Matrix (Fin 4) (Fin 4) K) = c • (1 : Matrix (Fin 4) (Fin 4) K)) :
    gammaAct α = ⊤ :=
  GenLocU4ExtMain.gammaAct_su4_ext_aux hp hp2 hK hq α hA ρ hU hρ hab a₀ c hc hsq

end GenLocU4Ext

end CFSG.GH74.Generic.BProg.B2
