module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityFamily
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherIncidenceGraph
import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitRadical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.AGLEmbedding.LinearThreeKit

private theorem pCoreOf_projStabilizer_ne_bot {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {W : Submodule K (Fin n → K)} (hW0 : ⊥ < W)
    (hWT : W < ⊤) : CFSG.Open.pCoreOf 2 (projStabilizer W) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  have hle : (elationSubgroup W).map (proj n K) ≤ CFSG.Open.pCoreOf 2 (projStabilizer W) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.map_mono (elationSubgroup_le_stabilizer _))
      ((Subgroup.map_mono (stabilizer_le_normalizer_elationSubgroup _)).trans
        (Subgroup.le_normalizer_map _))
      ((isPGroup_elationSubgroup 2 _).map _)
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.map_eq_bot_iff, ker_proj] at hle
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hWT
  refine hv (mem_of_forall_mem_elationSubgroup hW0.ne' fun A hA => ?_)
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (hle hA)
  rw [hc, Subsingleton.elim c 1, Units.val_one, map_one, Matrix.one_mulVec]

private theorem two_pow_mod_three {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, hm⟩ := hn
  rw [hm, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem parityCoreLinA_holds : ParityCoreLinA := by
  intro n K _ _ hn h5 hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [Fintype.card_eq_nat_card, hK, pow_one])
  have : Finite (projectiveSL n K) := inferInstance
  have : Finite (Subgroup (projectiveSL n K)) :=
    Finite.of_injective (fun H : Subgroup (projectiveSL n K) => (H : Set (projectiveSL n K)))
      fun H H' h => Subgroup.ext (Set.ext_iff.mp h)
  obtain ⟨hE, hdisj, -⟩ := intrinsic_extremal_parabolics (K := K) (n := n) 2 (by omega)
  have hinj := (maximal_parabolics (K := K) (n := n) 2 (by omega)).2.1
  have hcard : ∀ k, (k = 1 ∨ k = n - 1) →
      Nat.card ↥(projStabilizer '' {W : Submodule K (Fin n → K) | finrank K W = k}) =
        2 ^ n - 1 := by
    intro k hk
    have hk1 : 1 ≤ k ∧ k < n := by omega
    have hsub : {W : Submodule K (Fin n → K) | finrank K W = k} ⊆ {W | ⊥ < W ∧ W < ⊤} :=
      fun W (hW : finrank K W = k) => bot_lt_and_lt_top_of_finrank (by omega) (by omega)
    rw [Nat.card_image_of_injOn (hinj.mono hsub)]
    have h1 : (Nat.card {W : Submodule K (Fin n → K) // finrank K W = k} : ℚ) = 2 ^ n - 1 := by
      rw [card_finrank_eq hk1.2.le, hK]
      rcases hk with rfl | rfl
      · rw [gaussianCoeff_one]
        norm_num
      · rw [← gaussianCoeff_symm le_rfl (by omega : 1 ≤ n), gaussianCoeff_one]
        norm_num
    have h2 : ((2 ^ n - 1 : ℕ) : ℚ) = 2 ^ n - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      norm_num
    exact_mod_cast h1.trans h2.symm
  have hpow := two_pow_mod_three hn
  refine parityCoreAt_of_pCoreOf_family Nat.prime_three (extremalParabolics (projectiveSL n K) 2)
    ?_ (fun α M hM => map_mem_extremalParabolics α hM) ?_
  · rw [hE, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj, ← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq, hcard 1 (Or.inl rfl), hcard (n - 1) (Or.inr rfl)]
    generalize 2 ^ n = x at hpow ⊢
    omega
  · intro M hM
    rw [hE] at hM
    rcases hM with ⟨W, hW, rfl⟩ | ⟨W, hW, rfl⟩
    · have hW' : finrank K W = 1 := hW
      obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (n := n) (W := W) (by omega) (by omega)
      exact pCoreOf_projStabilizer_ne_bot hK h0 htop
    · have hW' : finrank K W = n - 1 := hW
      obtain ⟨h0, htop⟩ := bot_lt_and_lt_top_of_finrank (n := n) (W := W) (by omega) (by omega)
      exact pCoreOf_projStabilizer_ne_bot hK h0 htop

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
