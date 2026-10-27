module

public import CFSG.ClassicalInvolution.Q3.Q3YModel
public import CFSG.ClassicalInvolution.Q3.Q3YComp
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Asc77.AscR10D3a

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

theorem center_unitary_su3_eq_bot :
    Subgroup.center (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 3 (2 * 1)) 3 1) 3) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  let e : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3 ≃*
      Phan.Su (GaloisField 3 (2 * 1)) 3 1 3 :=
    (Unitary.equivStatedSU hF9 3).trans
      (MulEquiv.subgroupCongr (Unitary.SUid_eq_statedSU hF9 3)).symm
  have hc : Subgroup.center (Phan.Su (GaloisField 3 (2 * 1)) 3 1 3) = ⊥ :=
    Asc77.T3CII.center_su3_eq_bot (p := 3) (f := 1) hF9 (by norm_num)
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hez : e z ∈ Subgroup.center (Phan.Su (GaloisField 3 (2 * 1)) 3 1 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [hc, Subgroup.mem_bot] at hez
  exact e.injective (hez.trans (map_one e).symm)

theorem modelPairOrCenterless3 : ModelPairOrCenterless3 := by
  intro t n hfund hadm R hR
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  by_cases ht : t = .G2 ∨ t = .F4 ∨ t = .E8 ∨ t = .trialityD4 ∨ t = .twistedE6
  · exact Or.inl (Q3Y.center_modelUniv_eq_bot_of_tag ht hadm)
  · by_cases h3a : t = .PSL ∧ n = 3
    · left
      obtain ⟨rfl, rfl⟩ := h3a
      exact Asc77.T3CII.center_sl3_eq_bot hF3
    · by_cases h3b : t = .PSU ∧ n = 3
      · left
        obtain ⟨rfl, rfl⟩ := h3b
        have hM : modelUniv .PSU 3 3 1 Nat.prime_three =
            ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) 3,
              Unitary.rootDatum (card_galoisField_two_mul 3 1 (le_refl 1)) 3⟩ :=
          ModelFacts.modelUniv_PSU (n := 3) (p := 3) (f := 1) (le_refl 1)
        rw [hM]
        exact center_unitary_su3_eq_bot
      · right
        have hG2 : t ≠ .G2 := fun h => ht (Or.inl h)
        have hD4 : t ≠ .trialityD4 := fun h => ht (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have hA1 : ¬ (t = .PSL ∧ n = 2) := by
          rintro ⟨rfl, rfl⟩
          exact hadm.2.2.2.2 rfl
        exact Uniform.exists_commuting_fund (by norm_num) hfund hadm hG2 hD4 hA1
          (by tauto) hR

end CFSG.ClassicalInvolution.Q3
