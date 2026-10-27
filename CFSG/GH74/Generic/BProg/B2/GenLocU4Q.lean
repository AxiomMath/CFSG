module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q10
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Q11

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QClass

namespace GenLocU4Q

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem su4Q10Stmt_holds :
    Su4Q10Stmt K p f := by
  intro hp hp2 hK hq A _ _ α hA hr T
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  exact GenLocU4Q10.gammaAct_class10 hp hp2 hK hq α hA hr T

theorem su4Q11Stmt_holds : Su4Q11Stmt K p f := by
  intro hp hp2 hK hq A _ _ α hA hr T
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  exact GenLocU4Q11.gammaAct_class11 hp hp2 hK hq α hA hr T

theorem gammaAct_su4_quat
    (hQ2 : Su4Q2Stmt K p f) (hQ2s : Su4Q2SplitStmt K p f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (_hinner : ∀ c : A, IsInnerDiagU4 (α c))
    (ρ : A → GL (Fin 4) K) (hU : ∀ a, IsUnitaryU (p ^ f) (ρ a : Matrix (Fin 4) (Fin 4) K))
    (hρ : ∀ (a : A) (g : ↥(StatedSU 4 (p ^ f) K)),
      (((α a g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (ρ a : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((ρ a)⁻¹ : GL (Fin 4) K))
    (a b : A) (hanti : (ρ a : Matrix (Fin 4) (Fin 4) K) * (ρ b : Matrix (Fin 4) (Fin 4) K) =
      -((ρ b : Matrix (Fin 4) (Fin 4) K) * (ρ a : Matrix (Fin 4) (Fin 4) K))) :
    gammaAct α = ⊤ :=
  gammaAct_su4_quat_of hp hp2 hK hq hQ2 hQ2s su4Q10Stmt_holds su4Q11Stmt_holds α hA ρ hU hρ a b hanti

theorem su4QuatStmt
    (hQ2 : Su4Q2Stmt K p f) (hQ2s : Su4Q2SplitStmt K p f) : GenLocU4Inner.Su4QuatStmt K p f :=
  fun hp hp2 hK hq _ _ _ α hA hinner ρ hU hρ a b hanti =>
    gammaAct_su4_quat hQ2 hQ2s hp hp2 hK hq α hA hinner ρ hU hρ a b hanti

end GenLocU4Q

end CFSG.GH74.Generic.BProg.B2
