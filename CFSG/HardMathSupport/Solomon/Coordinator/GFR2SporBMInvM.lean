module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvMData
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Cases

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Dickson.Sec6.BM

theorem le_twentyone_of_pow_le_M {m k : ℕ} (hm : 360 ≤ m)
    (hk : m ^ k ≤ 808017424794512875886459904961710757005754368000000000) : k ≤ 21 := by
  by_contra h
  have h22 : 360 ^ 22 ≤ m ^ k :=
    (Nat.pow_le_pow_left hm 22).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have := h22.trans hk
  norm_num at this

theorem not_dvd_factorial_M {m k N : ℕ} (hm : 360 ≤ m)
    (hk : m ^ k ≤ 808017424794512875886459904961710757005754368000000000)
    (hN : N = 4089470473293004800 ∨ N = 90745943887872000) : ¬ N ∣ k.factorial := by
  intro hd
  have hk21 := le_twentyone_of_pow_le_M hm hk
  rcases hN with rfl | rfl
  · have h23 : 23 ∣ 4089470473293004800 := by norm_num
    have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 23)).1 (h23.trans hd)
    omega
  · have h31 : 31 ∣ 90745943887872000 := by norm_num
    have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 31)).1 (h31.trans hd)
    omega

theorem not_dvd_sq_M {N : ℕ} (hN : N = 4089470473293004800 ∨ N = 90745943887872000) :
    ¬ N ∣ 1080 ^ 2 ∧ ¬ N ∣ (orderON * 3) ^ 2 := by
  unfold orderON
  rcases hN with rfl | rfl <;> constructor <;> norm_num

section Inverted


theorem false_of_isHat_of_invertedByTwoA (hOG : UniquenessMaximal.InputONGroup) {G : Type}
    [Group G] (hE : MonsterExistenceStatement G) {s : G} (hs : orderOf s = 3)
    (hinv : InvertedByTwoA s) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({s} : Set G)))
    (h : IsHatSix ↥K ∨ IsHatON ↥K) : False := by
  haveI : Finite G := hE.1.1
  have hO := gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE Nat.prime_three (by norm_num) hs hinv
  obtain ⟨α, H, hα, hαs, hH, -, hcard, hHα, hHs, hHn, hCQ⟩ := M_inverted_data hE hs hinv
  have hG : Nat.card G = 808017424794512875886459904961710757005754368000000000 := by
    have := hE.1.2.2.2
    rw [monsterOrder_eq_numeral] at this
    exact this
  have key := @false_of_inverted_component G _ _ s α hα hαs hO
  have hcomp := glaPComponent_of_isComponentOf_of_core_eq_bot hO hK
  obtain ⟨hZ3, hperf⟩ : Nat.card ↥(Subgroup.center ↥K) = 3 ∧ commutator ↥K = ⊤ := by
    rcases h with h | h
    · exact ⟨h.2.1, h.1⟩
    · exact ⟨h.2.1, h.1⟩
  have hnc := exists_noncomm_of_perfect_center_card_three hperf hZ3
  obtain ⟨m, hm, hmZ, hsq⟩ : ∃ m : ℕ, 360 ≤ m ∧ m * Nat.card ↥(Subgroup.center ↥K) ≤ Nat.card ↥K ∧
      ¬ Nat.card ↥H ∣ Nat.card ↥K ^ 2 := by
    rcases h with h | h
    · have h1080 : Nat.card ↥K = 1080 := gfr2_card_isHatSix h
      refine ⟨360, le_rfl, by rw [hZ3, h1080], ?_⟩
      rw [h1080]
      rcases hcard with hc | hc <;> rw [hc] <;> exact (not_dvd_sq_M (by simp [hc])).1
    · have hq := UniquenessMaximal.isSimple_card_of_isHatON hOG h
      have hKcard : Nat.card ↥K = orderON * 3 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥K), hq.2, hZ3]
      refine ⟨orderON, ?_, by rw [hZ3, hKcard], ?_⟩
      · unfold orderON; norm_num
      · rw [hKcard]
        rcases hcard with hc | hc <;> rw [hc] <;> exact (not_dvd_sq_M (by simp [hc])).2
  refine key hH hHα hHs hHn hCQ m ?_ hcomp hmZ hnc hsq
  intro k hk hdvd
  rw [hG] at hk
  exact not_dvd_factorial_M hm hk (by rcases hcard with hc | hc <;> simp [hc]) hdvd

end Inverted

end CFSG.HardMathSupport.Solomon.Coordinator
