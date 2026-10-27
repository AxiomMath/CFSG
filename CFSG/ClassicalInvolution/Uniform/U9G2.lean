module

public import CFSG.ClassicalInvolution.Uniform.U5Edge
public import CFSG.ClassicalInvolution.Uniform.U7Main
public import CFSG.ClassicalInvolution.ModelFacts.G2G3Gen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement


theorem g2NonToralGenerate3_proved : G2NonToralGenerate3 := by
  intro z z' hz hz' hz1 hz1' hne hcomm _
  have hcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [hcard]
    decide
  exact G2D4Models.centralizer_sup_eq_top_g2_three (F := GaloisField 3 1) hodd hcard hz hz' hz1
    hz1' hne hcomm

theorem g2_pairGen3_proved (u v : (modelUniv .G2 0 3 1 Nat.prime_three).K) (hu : u * u = 1)
    (hv : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hcomm : u * v = v * u) :
    Subgroup.centralizer ({u} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) ⊔
      Subgroup.centralizer ({v} : Set (modelUniv .G2 0 3 1 Nat.prime_three).K) = ⊤ :=
  g2_pairGen3 g2NonToralGenerate3_proved u v hu hv hu1 hv1 huv hcomm

theorem g2D4Gen3_proved : G2D4Gen3 := g2D4Gen3_of_g2NonToral g2NonToralGenerate3_proved

theorem ih8G2D4EdgeU_proved : Ih8G2D4EdgeU := ih8G2D4EdgeU_of_g2NonToral g2NonToralGenerate3_proved

theorem thm3_proved :
    ∀ n : ℕ, CITBelowT (.sl2 3 1) n → Thm3TypedBelowExactU 3 1 n :=
  thm3_of_g2NonToral g2NonToralGenerate3_proved

theorem thm5NonGenBelowU_of_twin (hTwin : TwinGen3) {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    Q3.Disc3.Thm5NonGenBelowU n :=
  thm5NonGenBelowU_of_twin_and_g2 hTwin g2NonToralGenerate3_proved hn

end CFSG.ClassicalInvolution.Uniform
