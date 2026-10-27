module

public import CFSG.GroupTheory.UniqueElemSylowProj
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.WeirSylow.UniqueE27Wreath
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.GH74.Generic.S1.RCard
import CFSG.ClassicalInvolution.Asc77.AscSCH03
import CFSG.GH74.Statements
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.RankThree.CentralLift.ClassicalScalarCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open CFSG.SectionRank.OddCover CFSG.ClassicalInvolution.Asc77.SCH

theorem uniqueElemSylow_statedSU_four {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) : UniqueElemSylow 3 3 (StatedSU 4 q K) := by
  obtain ⟨ℓ, f, hU, rfl⟩ := CFSG.GH74.Generic.S1.rcard_exists_unitaryFieldData hK
  have hq2 : 2 ≤ ℓ ^ f := by
    have : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hU.prime.pos
    obtain ⟨k, hk⟩ := h3
    omega
  have hq0 : ℓ ^ f ≠ 0 := by omega
  have ha1 : 1 ≤ (ℓ ^ f + 1).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three (by omega) h3
  have hdvd : 3 ^ (ℓ ^ f + 1).factorization 3 ∣ Nat.card K - 1 := by
    refine (Nat.ordProj_dvd _ _).trans ?_
    rw [hK]
    have key : ∀ q : ℕ, 2 ≤ q → q + 1 ∣ q ^ 2 - 1 := fun q hq =>
      ⟨q - 1, by
        have h1 : 1 ≤ q := by omega
        have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
        zify [h1, h2]
        ring⟩
    exact key _ hq2
  obtain ⟨m, hm⟩ := exists_units_orderOf_eq_of_dvd (K := K) hdvd
  have hW := isWreathThree_glFourWreathFactor ha1 hm
  have hmq : m ^ (ℓ ^ f + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hm ▸ Nat.ordProj_dvd _ _)
  have hmq' : ((m : Kˣ) : K) ^ (ℓ ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hmq, Units.val_one]
  refine uniqueElemSylow_of_isWreathThree hW cyc4GL_pow_three ?_ ?_ ?_
  · rw [glFourWreathFactor, Subgroup.zpowers_le]
    refine diagHom_mem_statedSU hq0 _ (fun i => ?_) ?_
    · fin_cases i <;> simp [hmq', inv_pow]
    · simp [Fin.prod_univ_four]
  · exact cyc4GL_mem_statedSU hq0
  · rw [card_statedSU_four hU, card_glFourWreathFactor, hm,
      Nat.Prime.factorization_pow Nat.prime_three]
    simpa using factorization_su4_two h3 hq2

theorem uniqueElemSylow_statedProj_statedSU_four {q : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) :
    UniqueElemSylow 3 3 (StatedProj (StatedSU 4 q K)) :=
  UniqueElemSylow.statedProj (d := 4) (by norm_num)
    (fun _ hc => scalar_pow_four_eq_one_of_mem_statedSL
      (StatedAPI.statedSU_le_statedSL 4 q K hc)) (uniqueElemSylow_statedSU_four hK h3)

theorem uniqueElemSylow_of_statedClassicalModel_psu_four {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSU 4 p f) (hmod : p ^ f % 3 = 2) :
    UniqueElemSylow 3 3 X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  exact UniqueElemSylow.of_mulEquiv e.symm
    (uniqueElemSylow_statedProj_statedSU_four hcard (by omega))

end CFSG.GroupTheory.WeirSylow
