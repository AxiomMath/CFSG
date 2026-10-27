module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open
open CFSG.LargeEvenClassification.Helpers

theorem automorphism_solvable_of_frattini_card_le_four
    (Q : Type*) [Group Q] [Finite Q] (htwo : IsPGroup 2 Q)
    (hcard : Nat.card (Q ⧸ frattini Q) ≤ 4) : Group.IsSolvable (MulAut Q) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsSolvable (Equiv.Perm (Q ⧸ frattini Q)) := Equiv.Perm.isSolvable hcard
  have hinjective : Function.Injective (MulAut.toPerm (Q ⧸ frattini Q)) := by
    intro first second hequal
    apply MulEquiv.ext
    exact fun element => congrArg (fun f : Equiv.Perm (Q ⧸ frattini Q) => f element) hequal
  let : Group.IsSolvable (MulAut (Q ⧸ frattini Q)) :=
    Group.isSolvable_of_isSolvable_injective hinjective
  let : Group.IsNilpotent (frattiniAutAction Q).ker :=
    (frattiniAutAction_isPGroup_ker Q Nat.prime_two htwo).isNilpotent
  exact Group.isSolvable_of_ker_le_range (frattiniAutAction Q).ker.subtype
    (frattiniAutAction Q) (by rw [Subgroup.subtype_range])

theorem quaternion_power_two_isPGroup (exponent : ℕ) :
    IsPGroup 2 (QuaternionGroup (2 ^ exponent)) := by
  apply IsPGroup.of_card (n := exponent + 2)
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card, pow_add]
  norm_num
  omega

theorem quaternion_frattini_quotient_card_le_four (exponent : ℕ) :
    Nat.card (QuaternionGroup (2 ^ exponent) ⧸
      frattini (QuaternionGroup (2 ^ exponent))) ≤ 4 := by
  let Q := QuaternionGroup (2 ^ exponent)
  let pi := QuotientGroup.mk' (frattini Q)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 Q) := ⟨quaternion_power_two_isPGroup exponent⟩
  have hpow : (pi (QuaternionGroup.a 1)) ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr
      (CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (QuaternionGroup.a 1))
  have hcoordinate (coordinate : ZMod (2 * 2 ^ exponent)) :
      pi (QuaternionGroup.a coordinate) =
        pi (QuaternionGroup.a 1) ^ (coordinate.val % 2) := by
    have hpower : QuaternionGroup.a coordinate =
        (QuaternionGroup.a 1 : Q) ^ coordinate.val := by
      rw [QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    rw [hpower, map_pow]
    exact pow_eq_pow_of_modEq (Nat.mod_modEq coordinate.val 2).symm hpow
  let representatives : Fin 2 × Fin 2 → Q ⧸ frattini Q := fun pair =>
    if pair.1.val = 0 then pi (QuaternionGroup.a 1) ^ pair.2.val
    else pi (QuaternionGroup.xa 0) * pi (QuaternionGroup.a 1) ^ pair.2.val
  have hsurjective : Function.Surjective representatives := by
    intro element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) element
    cases original with
    | a coordinate =>
      refine ⟨(0, ⟨coordinate.val % 2, Nat.mod_lt _ (by decide)⟩), ?_⟩
      exact (hcoordinate coordinate).symm
    | xa coordinate =>
      refine ⟨(1, ⟨coordinate.val % 2, Nat.mod_lt _ (by decide)⟩), ?_⟩
      change pi (QuaternionGroup.xa 0) * pi (QuaternionGroup.a 1) ^
        (coordinate.val % 2) = pi (QuaternionGroup.xa coordinate)
      rw [← hcoordinate, ← map_mul, QuaternionGroup.xa_mul_a, zero_add]
  simpa only [Nat.card_prod, Nat.card_fin] using
    Nat.card_le_card_of_surjective representatives hsurjective

theorem quaternion_power_two_automorphism_solvable (exponent : ℕ) :
    Group.IsSolvable (MulAut (QuaternionGroup (2 ^ exponent))) :=
  automorphism_solvable_of_frattini_card_le_four _
    (quaternion_power_two_isPGroup exponent)
    (quaternion_frattini_quotient_card_le_four exponent)

theorem cyclic_automorphism_solvable (Q : Type*) [Group Q] [IsCyclic Q] :
    Group.IsSolvable (MulAut Q) := by
  exact Group.isSolvable_of_isSolvable_injective
    (f := (IsCyclic.mulAutMulEquiv Q).toMonoidHom) (IsCyclic.mulAutMulEquiv Q).injective

theorem rank_one_two_group_automorphism_solvable
    (Q : Type*) [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hrank : CFSG.Open.twoRank Q ≤ 1) :
    Group.IsSolvable (MulAut Q) := by
  obtain hcyclic | ⟨exponent, _, ⟨equivalence⟩⟩ :=
    CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion Q htwo hrank
  · let := hcyclic
    exact cyclic_automorphism_solvable Q
  · let : Group.IsSolvable (MulAut (QuaternionGroup (2 ^ (exponent - 2)))) :=
      quaternion_power_two_automorphism_solvable (exponent - 2)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MulAut.congr equivalence).toMonoidHom) (MulAut.congr equivalence).injective

end CFSG.ProperTwoGeneratedCore
