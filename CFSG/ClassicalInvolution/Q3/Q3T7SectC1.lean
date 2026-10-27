module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeFactsCenter
public import CFSG.ClassicalInvolution.Asc77.AscR10D3a
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LinearGroups (scalar_mem_statedSU_iff)
open scoped MatrixGroups

section Center

theorem su3_center_eq_bot {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ e) ^ 2) (hq : p ^ e = 3) :
    Subgroup.center (SU (unitaryInvolution F p e) 3) = ⊥ := by
  have hnq : (3, p ^ e) ≠ (3, 2) := by rw [hq]; decide
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  set φ := equivStatedSU hF 3 with hφ
  have hxc : φ x ∈ Subgroup.center (StatedSU 3 (p ^ e) F) := by
    rw [← map_center_mulEquiv φ]
    exact ⟨x, hx, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hF (by norm_num) hnq).2] at hxc
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      ((φ x : StatedSU 3 (p ^ e) F) : GL (Fin 3) F) := hxc
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 (p ^ e) F := by
    rw [hc]
    exact (φ x).2
  obtain ⟨hc3, hc4⟩ := (scalar_mem_statedSU_iff Fact.out hF (by norm_num) c).mp hmem
  have hc1 : c = 1 := by
    rw [hq, pow_succ, hc3, one_mul] at hc4
    exact hc4
  have h1 : φ x = 1 := by
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl
  exact φ.injective (by rw [h1, map_one])

theorem isSimpleGroup_of_center_bot {K X : Type} [Group K] [Group X]
    (hK : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥) (ψ : K →* X)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) : IsSimpleGroup X := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hKq : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hKs : IsSimpleGroup K :=
    MulEquiv.isSimpleGroup
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact MulEquiv.isSimpleGroup (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm

end Center

section Model


variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}

theorem isSimpleGroup_of_ih8Model_three (M : Ih8Model 3 1 Ω t k e)
    (ht : (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) : IsSimpleGroup G := by
  have hD4 : t ≠ .trialityD4 := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have he : e = 1 := M.exp_eq_f hD4
  subst he
  have hQ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t k 3 1 Nat.prime_three
    M.isFundTag M.admissible
  have hZ : Subgroup.center (modelUniv t k 3 1 Nat.prime_three).K = ⊥ := by
    have hF : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 (by norm_num)]
      norm_num
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact CFSG.ClassicalInvolution.Asc77.T3CII.center_sl3_eq_bot (F := GaloisField 3 1) hF
    · have hF2 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
        CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
      rw [CFSG.ClassicalInvolution.RouteD.LieBridge.modelUniv_PSU_eq (n := 3) (p := 3) (f := 1)
        le_rfl]
      exact su3_center_eq_bot hF2 (by norm_num)
  exact isSimpleGroup_of_center_bot hQ.1 hZ M.ψ M.surj M.ker_le_center

end Model

end CFSG.ClassicalInvolution.Q3.Q3T7
