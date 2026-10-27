module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltOrd

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint Subgroup Equiv Equiv.Perm

namespace S3HLOCard

theorem sl2Quot_card_data {Lb : Type} [Group Lb]
    (h : HasSL2Model (Lb ⧸ pPrimeCore 2 Lb) (fun q => Odd q ∧ 5 ≤ q)) :
    ∃ q : ℕ, Odd q ∧ 5 ≤ q ∧ Nat.card (Lb ⧸ pPrimeCore 2 Lb) = q * (q ^ 2 - 1) ∧
      q * (q ^ 2 - 1) ∣ Nat.card Lb := by
  obtain ⟨q, hq, hq5, hc⟩ := S3SL2Basic.sl2_card_data h
  exact ⟨q, hq, hq5, hc, hc ▸ Subgroup.card_quotient_dvd_card _⟩

theorem le_card_of_dvd {Lb : Type} [Group Lb] [Finite Lb] {q : ℕ} (h : q * (q ^ 2 - 1) ∣ Nat.card Lb) :
    q * (q ^ 2 - 1) ≤ Nat.card Lb :=
  Nat.le_of_dvd Nat.card_pos h

variable {Y : Type} [Group Y] {H : Subgroup Y} {n : ℕ} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}

theorem constraint_of_commuting' (S : AltSetting H n hsN) [Finite Y] {Lb : Subgroup Y} (hLbH : Lb ≤ H)
    (hZ : Nat.card (center ↥H) = 2) {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hcard : q * (q ^ 2 - 1) ∣ Nat.card Lb) {σ₁ : Perm (Fin n)} (hσ₁ : σ₁ * σ₁ = 1) (hσ₁1 : σ₁ ≠ 1)
    (hc : ∀ l : ↥H, (l : Y) ∈ Lb →
      σ₁ * (S.π l : Perm (Fin n)) = (S.π l : Perm (Fin n)) * σ₁) :
    5 ≤ n - 2 * σ₁.cycleType.card ∨ 5 ≤ σ₁.cycleType.card := by
  classical
  obtain ⟨r, hr, hr5, hrdvd⟩ := S3SL2Perm.prime_ge_five_dvd hq hq5
  obtain ⟨m, hm2, hmcard⟩ := S3SL2AltOrd.card_image_dvd S hLbH hZ
  have hrm : ¬ r ∣ m := by
    intro h
    have := Nat.le_of_dvd (by norm_num) (h.trans hm2)
    omega
  have hrL : r ∣ Nat.card Lb := hrdvd.trans hcard
  have hrR : r ∣ Nat.card ((Lb.subgroupOf H).map S.π) := by
    rw [hmcard] at hrL
    exact ((Nat.Prime.dvd_mul hr).1 hrL).resolve_left hrm
  have hdvd := S3SL2AltOrd.card_image_dvd_centralizer S hc
  rw [S3SL2Perm.card_centralizer_involution hσ₁ hσ₁1] at hdvd
  have := S3SL2Perm.prime_dvd_cases hr hr5 (hrR.trans hdvd)
  omega

end S3HLOCard

end CFSG.GH74.Generic.BProg.B3
