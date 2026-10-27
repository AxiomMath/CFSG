module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem card_statedSL_two_aux {K : Type} [Field K] [Finite K] :
    Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two K

theorem center_eq_bot_of_equiv_statedSL_two {X : Type*} [Group X] {K : Type} [Field K] [CharP K 2]
    (e : X ≃* ↥(StatedSL 2 K)) : Subgroup.center X = ⊥ := by
  classical
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  rw [eq_bot_iff]
  intro c hc
  have hzc : e' c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.1 hc g'
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hzc
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (r - 1) ^ 2 = 0 := by
      have : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
      have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      rw [this, hr]
      linear_combination (1 - r) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)
  rw [Subgroup.mem_bot]
  apply e'.injective
  rw [map_one]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])

theorem card_slThreeFour {X : Type*} [Group X] [Finite X] (h : IsSLThreeFour X) :
    Nat.card X = 60480 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) = 60480
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK]
  norm_num

theorem card_lThreeFour {X : Type*} [Group X] [Finite X] (h : IsLThreeFour X) :
    Nat.card X = 20160 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) = 20160
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide +kernel

theorem card_of_isLTwoOddPow {X : Type*} [Group X] [Finite X] (h : IsLTwoOddPow X) :
    ∃ n : ℕ, n % 2 = 1 ∧ 1 < n ∧ Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨K, _, _, n, hn, hn1, hK, ⟨e⟩⟩ := h
  refine ⟨n, hn, hn1, ?_⟩
  rw [Nat.card_congr e.toEquiv, card_statedSL_two_aux, hK]
  congr 1
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private theorem arith_aux (N : ℕ) (k : ℕ) (hk : ¬ 2 ^ (k + 1) ∣ N) (n : ℕ)
    (h : 2 ^ n * (4 ^ n - 1) = N) : n ≤ k := by
  by_contra hlt
  have hlt := not_le.1 hlt
  apply hk
  rw [← h]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 hlt) _

theorem not_isLTwoOddPow_of_card {X : Type*} [Group X] [Finite X] (h : IsLTwoOddPow X) (k N : ℕ)
    (hk : ¬ 2 ^ (k + 1) ∣ N)
    (hall : ∀ n, n ≤ k → n % 2 = 1 → 1 < n → 2 ^ n * (4 ^ n - 1) ≠ N) (hX : Nat.card X = N) :
    False := by
  obtain ⟨n, hn, hn1, hc⟩ := card_of_isLTwoOddPow h
  have hnk := arith_aux N k hk n (hc.symm.trans hX)
  exact hall n hnk hn hn1 (hc.symm.trans hX)

theorem not_isLTwoOddPow_slThreeFour {X : Type*} [Group X] [Finite X] (h : IsSLThreeFour X) :
    ¬ IsLTwoOddPow X := by
  intro h2
  refine not_isLTwoOddPow_of_card h2 6 60480 (by norm_num) ?_ (card_slThreeFour h)
  intro n hn hodd h1
  interval_cases n <;> simp_all

theorem not_isLTwoOddPow_lThreeFour {X : Type*} [Group X] [Finite X] (h : IsLThreeFour X) :
    ¬ IsLTwoOddPow X := by
  intro h2
  refine not_isLTwoOddPow_of_card h2 6 20160 (by norm_num) ?_ (card_lThreeFour h)
  intro n hn hodd h1
  interval_cases n <;> simp_all

theorem not_isLTwoOddPow_hatON (hON : InputONGroup) {X : Type*} [Group X] [Finite X]
    (h : IsHatON X) : ¬ IsLTwoOddPow X := by
  intro h2
  obtain ⟨-, hQ⟩ := isSimple_card_of_isHatON hON h
  have hZ := h.2.1
  have hX : Nat.card X = 3 * orderON := by
    rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, hQ, hZ, mul_comm]
  refine not_isLTwoOddPow_of_card h2 9 (3 * orderON)
    (by unfold orderON; norm_num) ?_ hX
  intro n hn hodd h1
  unfold orderON
  interval_cases n <;> simp_all

theorem not_isLThreeFour_quot_of_isLTwoOddPow {M : Type*} [Group M] [Finite M]
    (hM : IsLTwoOddPow M) (Z : Subgroup M) [Z.Normal] (hZ : Z ≤ Subgroup.center M) :
    ¬ IsLThreeFour (M ⧸ Z) := by
  intro hL
  obtain ⟨K, _, _, n, hn, hn1, hK, ⟨e⟩⟩ := hM
  have := charP_two_of_card_pow hK
  have hc : Subgroup.center M = ⊥ := center_eq_bot_of_equiv_statedSL_two e
  have hZb : Z = ⊥ := by
    rw [eq_bot_iff]
    exact hc ▸ hZ
  have hq : Nat.card (M ⧸ Z) = 20160 := card_lThreeFour hL
  have hMc : Nat.card M = 20160 := by
    rw [Z.card_eq_card_quotient_mul_card_subgroup, hq, hZb, Subgroup.card_bot, mul_one]
  have hM2 : IsLTwoOddPow M := ⟨K, inferInstance, inferInstance, n, hn, hn1, hK, ⟨e⟩⟩
  refine not_isLTwoOddPow_of_card hM2 6 20160 (by norm_num) ?_ hMc
  intro m hm hodd h1
  interval_cases m <;> simp_all

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
