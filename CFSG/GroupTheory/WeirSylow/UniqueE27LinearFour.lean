module

public import CFSG.GroupTheory.UniqueElemSylowProj
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.WeirSylow.UniqueE27Wreath
import CFSG.GroupTheory.WeirSylow.UniqueE27GLFour
import CFSG.ClassicalInvolution.Asc77.AscSCH18
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalInvolution.Asc77.AscSCH03
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open CFSG.SectionRank.OddCover CFSG.ClassicalInvolution.Asc77.SCH

theorem uniqueElemSylow_statedSL_four {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) : UniqueElemSylow 3 3 (StatedSL 4 K) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have ha1 : 1 ≤ (Nat.card K - 1).factorization 3 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_three (by omega) h3)
  obtain ⟨m, hm⟩ := exists_units_orderOf_eq_of_dvd (K := K)
    (d := 3 ^ (Nat.card K - 1).factorization 3) (Nat.ordProj_dvd _ _)
  have hW := isWreathThree_glFourWreathFactor ha1 hm
  refine uniqueElemSylow_of_isWreathThree hW cyc4GL_pow_three ?_ ?_ ?_
  · rw [glFourWreathFactor, Subgroup.zpowers_le]
    exact StatedAPI.mem_statedSL_of_det (by simp [det_diagHom, Fin.prod_univ_four])
  · exact StatedAPI.mem_statedSL_of_det det_cyc4GL
  · rw [card_statedSL_four, card_glFourWreathFactor, hm,
      Nat.Prime.factorization_pow Nat.prime_three]
    simpa using factorization_sl4_one h3 hq

theorem uniqueElemSylow_statedProj_statedSL_four {K : Type} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) : UniqueElemSylow 3 3 (StatedProj (StatedSL 4 K)) :=
  UniqueElemSylow.statedProj (d := 4) (by norm_num)
    (fun _ hc => scalar_pow_four_eq_one_of_mem_statedSL hc) (uniqueElemSylow_statedSL_four h3)

theorem uniqueElemSylow_of_statedClassicalModel_psl_four {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 4 p f) (hmod : p ^ f % 3 = 1) :
    UniqueElemSylow 3 3 X := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  exact UniqueElemSylow.of_mulEquiv e.symm
    (uniqueElemSylow_statedProj_statedSL_four (K := K) (by omega))

end CFSG.GroupTheory.WeirSylow
