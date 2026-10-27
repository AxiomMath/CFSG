module

public import CFSG.Open.StatedDefs
public import CFSG.Assembly.Defs
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open CFSG.Open
open Matrix

theorem nonempty_quotientCenter_mulEquiv_of_surjective {X Y : Type*} [Group X] [Group Y]
    (hX : Group.IsPerfect X) (f : X →* Y) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center X) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) := by
  have hc : Subgroup.center X = ((QuotientGroup.mk' (Subgroup.center Y)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (CFSG.LocalCores.comap_center_eq_of_perfect hX f hf hker).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp hf))⟩

variable {K : Type} [Field K] [Finite K] {f : ℕ}

theorem mul_comm_GL_fin_of_le_one {F : Type} [Field F] {d : ℕ} (hd : d ≤ 1)
    (a b : GL (Fin d) F) : a * b = b * a := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · apply Units.ext
    exact Subsingleton.elim _ _
  · apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]

theorem mul_comm_statedSU_of_le_one {F : Type} [Field F] {k q : ℕ} (hk : k ≤ 1)
    (a b : StatedSU k q F) : a * b = b * a := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_comm_GL_fin_of_le_one hk _ _

theorem mul_comm_statedSL_of_le_one {F : Type} [Field F] {a : ℕ} (ha : a ≤ 1)
    (x y : StatedSL a F) : x * y = y * x := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_comm_GL_fin_of_le_one ha _ _

theorem center_statedSU_eq (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) {k : ℕ} (hk : 2 ≤ k) :
    Subgroup.center (StatedSU k (2 ^ f) K) =
      (StatedScalars (Fin k) K).subgroupOf (StatedSU k (2 ^ f) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · apply le_antisymm
    · rw [CFSG.ComponentClassification.RankTwoClassical.center_statedSU_two_eq_bot hK]
      exact bot_le
    · exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  · exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) (p := 2)
      (f := f) (n := k) hK hk3
      (CFSG.ComponentClassification.RankTwoClassical.ne_three_two_of_two_le hf)).2

theorem nonempty_quotientCenter_equiv_statedProj_statedSU (hK : Nat.card K = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) {k : ℕ} (hk : 2 ≤ k) {Γ : Type*} [Group Γ] (e : Γ ≃* StatedSU k (2 ^ f) K) :
    Nonempty (Γ ⧸ Subgroup.center Γ ≃* StatedProj (StatedSU k (2 ^ f) K)) :=
  ⟨(QuotientGroup.congr (Subgroup.center Γ) (Subgroup.center (StatedSU k (2 ^ f) K)) e
      (Subgroup.map_center_eq e)).trans
    (QuotientGroup.quotientMulEquivOfEq (center_statedSU_eq hK hf hk))⟩

theorem isQuasisimple_or_isSolvable_statedSU (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (k : ℕ) :
    CFSG.Assembly.IsQuasisimple (StatedSU k (2 ^ f) K) ∨ IsSolvable (StatedSU k (2 ^ f) K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  rcases (show k ≤ 1 ∨ 2 ≤ k by omega) with hk | hk
  · exact Or.inr <| Group.isSolvable_of_comm fun a b => mul_comm_statedSU_of_le_one hk a b
  · exact Or.inl <|
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_statedSU_of_two_le hK hf hk)

theorem isQuasisimple_or_isSolvable_statedSL (hK : 4 ≤ Nat.card K) (a : ℕ) :
    CFSG.Assembly.IsQuasisimple (StatedSL a K) ∨ IsSolvable (StatedSL a K) := by
  rcases (show a ≤ 1 ∨ 2 ≤ a by omega) with ha | ha
  · exact Or.inr <| Group.isSolvable_of_comm fun x y => mul_comm_statedSL_of_le_one ha x y
  · exact Or.inl <| (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
      (CFSG.LieType.SemisimpleCentralizers.Held.hct_isQuasisimple_statedSL K ha
        (Or.inr (by omega)) (Or.inr (by omega)))

theorem two_le_of_isQuasisimple_statedSU {L : Type} [Field L] {k q : ℕ}
    (h : CFSG.Assembly.IsQuasisimple (StatedSU k q L)) : 2 ≤ k := by
  by_contra hk
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_not_isQuasisimple_of_comm
    (fun a b => mul_comm_statedSU_of_le_one (by omega) a b)
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp h)

theorem two_le_of_isQuasisimple_statedSL {L : Type} [Field L] {a : ℕ}
    (h : CFSG.Assembly.IsQuasisimple (StatedSL a L)) : 2 ≤ a := by
  by_contra ha
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_not_isQuasisimple_of_comm
    (fun x y => mul_comm_statedSL_of_le_one (by omega) x y)
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp h)

end CFSG.LieType.SemisimpleCentralizers.OrderThree
