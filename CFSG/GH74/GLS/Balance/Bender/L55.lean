module

public import CFSG.GH74.GLS.Balance.Bender.L55Cases

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem l55_step {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) (h52iv : BenderL52iv p)
    (h54 : BenderL54 p) (hq42 : BenderQ42iii p) (hq43 : BenderQ43iii p) (hq326 : BenderQ326)
    {m : ℕ} (ih : l55_Claim p m) : l55_Claim p (m + 1) := by
  refine l55_reduce ?_
  intro G _ _ X P hcard hXp hP hPX hsup
  have hXn : X.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer hPX
  by_cases hX1 : X = ⊥
  · rw [hX1]
    exact bot_le
  obtain ⟨N, hNn, hN1, hNX, hmin⟩ := l55_exists_minimal_normal hX1
  have := hNn
  by_cases hdvd : p ∣ Nat.card N
  · by_cases hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
    · exact l55_case_pgroup h52ii h52iv hq42 ih hcard hXp hP hPX hsup hNX hN1 hmin
        (l55_isPGroup_of_abelian hmin hdvd hab)
    · push Not at hab
      exact l55_case_nonab h54 hq326 ih hcard hXp hP hPX hNX hN1 hmin hdvd hab
  · exact l55_case_coprime h52ii hq43 ih hcard hXp hP hNX hN1
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hdvd)

theorem l55_claim_all {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) (h52iv : BenderL52iv p)
    (h54 : BenderL54 p) (hq42 : BenderQ42iii p) (hq43 : BenderQ43iii p) (hq326 : BenderQ326)
    (n : ℕ) : l55_Claim p n := by
  induction n with
  | zero =>
    intro G _ _ X P hcard
    exfalso
    have : 0 < Nat.card X := Nat.card_pos
    omega
  | succ m ih => exact l55_step h52ii h52iv h54 hq42 hq43 hq326 ih

theorem l55_commutator_le {G : Type} [Group G] {X P : Subgroup G}
    (hPX : P ≤ normalizer (X : Set G)) : ⁅X, P⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ X := (mem_normalizer_iff.mp (hPX hy) x⁻¹).mp (X.inv_mem hx)
  have h2 := X.mul_mem hx h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h2

theorem bender_l55 {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) (h52iv : BenderL52iv p)
    (h54 : BenderL54 p) (hq42 : BenderQ42iii p) (hq43 : BenderQ43iii p) (hq326 : BenderQ326) :
    BenderL55 p := by
  intro G _ _ X P hXp hP hPX
  have hweak := l55_claim_all h52ii h52iv h54 hq42 hq43 hq326 (Nat.card X) G X P le_rfl hXp hP hPX
  apply le_antisymm
  · exact l55_aux hXp.oResOf_eq
      (fun c hc => l55_mem_normalizer_commutator (Subgroup.le_normalizer hc.1) hc.2) hweak
  · exact sup_le (l55_commutator_le hPX) ((oResOf_le p _).trans inf_le_left)

end CFSG.GH74.GLS.Balance
