module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenQ1
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Basic

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic

namespace GenLocU4Q

variable {K : Type} [Field K] [Finite K]

theorem eq_top_of_centralizers_q1 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 4 = 1) (Γ : Subgroup ↥(StatedSU 4 (p ^ f) K)) (x y : GL (Fin 4) K)
    (hx2 : x * x = 1) (hy2 : y * y = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x))
    (hxU : IsUnitaryU (p ^ f) (x : Matrix (Fin 4) (Fin 4) K)) (hyU : IsUnitaryU (p ^ f) (y : Matrix (Fin 4) (Fin 4) K))
    (hX : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * x = x * g → g ∈ Γ)
    (hY : ∀ g : ↥(StatedSU 4 (p ^ f) K), (g : GL (Fin 4) K) * y = y * g → g ∈ Γ) : Γ = ⊤ :=
  GenLocU4Q1.eq_top_of_centralizers_q1_raw hp hp2 hK hq Γ x y hx2 hy2 hxy hxU hyU hX hY

end GenLocU4Q

end CFSG.GH74.Generic.BProg.B2
