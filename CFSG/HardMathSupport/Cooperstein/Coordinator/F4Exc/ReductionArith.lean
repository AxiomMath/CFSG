module

public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem ordF4_lt {q : ℕ} (hq : 2 ≤ q) : ordF4 q < q ^ 52 := by
  have h : ∀ d : ℕ, 1 ≤ d → 0 < q ^ d - 1 ∧ q ^ d - 1 < q ^ d := by
    intro d hd
    have h1 : 2 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
    exact ⟨by omega, by omega⟩
  unfold ordF4
  have e : q ^ 52 = q ^ 24 * q ^ 12 * q ^ 8 * q ^ 6 * q ^ 2 := by
    simp only [← pow_add]
  rw [e]
  have hq0 : 0 < q := by omega
  gcongr
  all_goals first | exact (h _ (by norm_num)).2 | exact (h _ (by norm_num)).1.le | positivity

theorem nonsurv_numerics {n δ m g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n) (hgδ : g ∣ δ) (hδ : 1 ≤ δ)
    (h : 52 * (n / g) + 1 ≤ m) : 52 * n + 1 ≤ δ * m := by
  obtain ⟨t, rfl⟩ := hgn
  have ha : g * t / g = t := Nat.mul_div_cancel_left t hg
  rw [ha] at h
  have hgδ' : g ≤ δ := Nat.le_of_dvd hδ hgδ
  calc 52 * (g * t) + 1 ≤ g * (52 * t + 1) := by nlinarith
    _ ≤ δ * m := Nat.mul_le_mul hgδ' h

section Center


theorem center_eq_bot_of_F4 {L : Type} [Group L] [Finite L] (hL : CFSG.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L))) {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : L ⧸ Subgroup.center L ≃* AdjointQuotient .F4 K) :
    Subgroup.center L = ⊥ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hfinX : Finite (AdjointQuotient .F4 K) := inferInstance
  have key : ∀ hperf : commutator (AdjointQuotient .F4 K) = ⊤,
      Finite (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) := by
    intro hperf
    have := CFSG.RankThree.PerfectCover.finite_hopfMultiplier (Group.isPerfect_def.2 hperf)
    exact Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  have hsub : ∀ hperf : commutator (AdjointQuotient .F4 K) = ⊤,
      Subsingleton (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) →
      Subgroup.center L = ⊥ := by
    intro hperf hM
    have hfin := key hperf
    have h1 := GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hL e
    have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (AdjointQuotient .F4 K)) = 1 :=
      Nat.card_unique
    rw [h2] at h1
    exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n
    · obtain ⟨hperf, hle⟩ := F4Two.f4_two_hopfMultiplier (K := K) (by simpa using hK)
      have hfin := key hperf
      have h1 := GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hL e
      have h2 : Nat.card (Subgroup.center L) ≤ 2 :=
        (Nat.le_of_dvd Nat.card_pos h1).trans hle
      have h3 : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
      obtain ⟨j, hj⟩ := hodd
      have : Nat.card (Subgroup.center L) = 1 := by omega
      exact Subgroup.card_eq_one.1 this
    · obtain ⟨hperf, hM⟩ := FieldFour.f4_four_hopfMultiplier (K := K) hK
      exact hsub hperf hM
  · have h5 : 5 ≤ Nat.card K := by
      rw [hK]
      calc 5 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    obtain ⟨hperf, hM⟩ := AdjointClosed.f4_hopfMultiplier (K := K) h5
    exact hsub hperf hM

end Center

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
