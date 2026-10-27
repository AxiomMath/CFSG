module

public import CFSG.ClassicalInvolution.Q3.Q3NMInner
public import CFSG.ClassicalInvolution.Q3.Q3NMDiag
public import CFSG.ClassicalInvolution.Q3.Q3NMDiagSU

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Balance
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Rows

theorem autOddFreeOn_PSL {m : ℕ} (hm : 2 ≤ m) {X : Type} [Group X] [Finite X]
    (ψ : SL(m + 1, GaloisField 3 1) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center SL(m + 1, GaloisField 3 1)) :
    AutOddFreeOn X (fun τ => τ ∈ innSubgroup X ∨
      ∃ D : GL (Fin (m + 1)) (GaloisField 3 1), D * D = 1 ∧
        ∀ x, τ (ψ x) = ψ (conjSLAut D x)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .PSL (m + 1) 3 1 :=
    ⟨hp, le_rfl, by omega, fun h => by have := congrArg Prod.fst h; simp at this; omega,
      fun h => by have := congrArg Prod.fst h; simp at this; omega⟩
  have hFT : IsFundTag .PSL := trivial
  have hD4 : ¬ (StatedLieTag.PSL = .POmegaPlus ∧ m + 1 = 4) := fun h => by cases h.1
  have hT : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hKq : CFSG.Open.IsQuasisimple (modelUniv .PSL (m + 1) 3 1 hp).K :=
    (ModelFacts.modelClauseZero .PSL (m + 1) 3 1 hp hFT hadm).1
  have : Group.IsPerfect SL(m + 1, GaloisField 3 1) := ⟨hKq.1⟩
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have hinner :=
    autOddFreeInnerTag_of_not_D4 (t := .PSL) (n := m + 1) hD4 hT hp hFT hadm X ψ hψ hker
  have hodd := oddAut_inner_centralQuotient hD4 hT hp hFT hadm X ψ hψ hker
  exact (AutOddFreeInner.toOn hinner).or (autOddFreeOn_sl_involDiag hF ψ hψ hker hodd)

theorem autOddFreeOn_PSU {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] [Finite X]
    (ψ : SU (unitaryInvolution (GaloisField 3 2) 3 1) n →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 3 2) 3 1) n)) :
    AutOddFreeOn X (fun τ => τ ∈ innSubgroup X ∨
      ∃ (D : GL (Fin n) (GaloisField 3 2))
        (hDg : cT (unitaryInvolution (GaloisField 3 2) 3 1)
          (D : Matrix (Fin n) (Fin n) (GaloisField 3 2)) * antidiag n *
            (D : Matrix (Fin n) (Fin n) (GaloisField 3 2)) = antidiag n),
        D * D = 1 ∧ ∀ x, τ (ψ x) =
          ψ (conjAut (SU (unitaryInvolution (GaloisField 3 2) 3 1) n) D
            (mem_normalizer_SU hDg) x)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hadm : StatedLieAdmissible .PSU n 3 1 :=
    ⟨hp, le_rfl, hn, fun h => by have := congrArg Prod.snd h; simp at this⟩
  have hFT : IsFundTag .PSU := trivial
  have hD4 : ¬ (StatedLieTag.PSU = .POmegaPlus ∧ n = 4) := fun h => by cases h.1
  have hT : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hKq : CFSG.Open.IsQuasisimple (modelUniv .PSU n 3 1 hp).K :=
    (ModelFacts.modelClauseZero .PSU n 3 1 hp hFT hadm).1
  have : Group.IsPerfect (SU (unitaryInvolution (GaloisField 3 2) 3 1) n) := ⟨hKq.1⟩
  have hE : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hZ : IsPGroup 2 (Subgroup.center (SU (unitaryInvolution (GaloisField 3 2) 3 1) n)) :=
    (modelFiniteCenterTwoGroup3 .PSU n hp trivial hadm).2
  have hinner :=
    autOddFreeInnerTag_of_not_D4 (t := .PSU) (n := n) hD4 hT hp hFT hadm X ψ hψ hker
  have hodd := oddAut_inner_centralQuotient hD4 hT hp hFT hadm X ψ hψ hker
  exact (AutOddFreeInner.toOn hinner).or (autOddFreeOn_su_involDiag hE hZ ψ hψ hker hodd)

theorem isPerfect_modelUniv {t : StatedLieTag} {n : ℕ} (hp : Nat.Prime 3) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) : Group.IsPerfect (modelUniv t n 3 1 hp).K :=
  ⟨((ModelFacts.modelClauseZero t n 3 1 hp hFT hadm).1).1⟩

end Rows

end CFSG.ClassicalInvolution.Q3.Q3NM
