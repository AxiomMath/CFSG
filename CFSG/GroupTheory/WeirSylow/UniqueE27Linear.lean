module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.UniqueElemSylowProj
import CFSG.GroupTheory.WeirSylow.GL
import CFSG.GroupTheory.WeirSylow.SigmaThree
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.Open.StatedAPI

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open

theorem uniqueElemSylow_gl_of_div_eq_three (K : Type) [Field K] [Finite K]
    (hK : ¬ 3 ∣ Nat.card K) {n : ℕ} (hn : n / orderOf (Nat.card K : ZMod 3) = 3) :
    UniqueElemSylow 3 3 (GL (Fin n) K) := by
  letI := Fintype.ofFinite K
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  rw [hcard] at hK hn
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  exact uniqueElemSylow_of_sigmaModel (one_le_padicValNat_three_pow_orderOf_sub_one hK hq2) hn
    fun P => sylow_GL (by decide) K hK n P

theorem uniqueElemSylow_gl_of_mod_three_eq_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (GL (Fin n) K) :=
  uniqueElemSylow_gl_of_div_eq_three K (by omega)
    (by rw [orderOf_natCast_zmod_three_of_mod_eq_two hK]; omega)

private theorem units_pow_card_sub_one {K : Type} [Field K] [Finite K] (c : Kˣ) :
    c ^ (Nat.card K - 1) = 1 := by
  rw [← Nat.card_units K]
  exact pow_card_eq_one'

theorem uniqueElemSylow_statedSL_of_mod_three_eq_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (StatedSL n K) := by
  refine UniqueElemSylow.subgroup_of_pow_mem (StatedSL n K) (m := Nat.card K - 1) (by omega)
    (fun g => ?_) (uniqueElemSylow_gl_of_mod_three_eq_two K hK hn)
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, Units.val_pow_eq_pow_val, Matrix.det_pow]
  have := congrArg Units.val (units_pow_card_sub_one (Matrix.GeneralLinearGroup.det g))
  simpa using this

theorem uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (StatedProj (StatedSL n K)) :=
  UniqueElemSylow.statedProj (d := Nat.card K - 1) (by omega) (fun c _ => units_pow_card_sub_one c)
    (uniqueElemSylow_statedSL_of_mod_three_eq_two K hK hn)

end CFSG.GroupTheory.WeirSylow
