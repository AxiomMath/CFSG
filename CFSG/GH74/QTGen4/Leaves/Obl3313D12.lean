module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Vol2.Ch3Sec3Sec
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.Quasithin CFSG.Quasithin.H13

theorem false_of_psl_two_prime_of_dvd_20160 {X : Type} [Group X] {q : ℕ} (hq : q.Prime)
    (h11 : 11 ≤ q) (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 q 1) (hd : Nat.card X ∣ 20160) :
    False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  rw [pow_one] at hK
  have hcard : Nat.card X = (q ^ (2 * (2 - 1) / 2) * ∏ i ∈ Finset.Icc 2 2, (q ^ i - 1)) /
      Nat.gcd 2 (q - 1) := by
    rw [Nat.card_congr (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).toEquiv,
      CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
  simp only [Finset.Icc_self, Finset.prod_singleton] at hcard
  have hg : Nat.gcd 2 (q - 1) ∣ q ^ (2 * (2 - 1) / 2) * (q ^ 2 - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right 2 (q - 1)).trans ?_
    simpa using Nat.sub_dvd_pow_sub_pow q 1 2
  have hmul : Nat.card X * Nat.gcd 2 (q - 1) = q ^ (2 * (2 - 1) / 2) * (q ^ 2 - 1) := by
    rw [hcard]
    exact Nat.div_mul_cancel hg
  have hgle : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 (q - 1))
  have hgpos : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hcop : Nat.Coprime q (Nat.gcd 2 (q - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => ?_
    have := Nat.le_of_dvd hgpos h
    omega
  have hqd : q ∣ Nat.card X * Nat.gcd 2 (q - 1) := by
    have hp : q ^ (2 * (2 - 1) / 2) = q := by norm_num
    rw [hmul, hp]
    exact Dvd.intro _ rfl
  have hq1 : q ∣ Nat.card X := hcop.dvd_of_dvd_mul_right hqd
  have hq2 : q ∣ 20160 := hq1.trans hd
  have h20160 : (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num
  rw [h20160] at hq2
  rcases (Nat.Prime.dvd_mul hq).1 hq2 with h | h
  · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hq.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

@[expose] def Obl3_3_13D12_Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.GH74.Gen4 G →
    ∀ (T M L D H K : Subgroup G), Hyp331 G T M L D → InH T H →
    H ≤ L ⊔ T → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) → pCoreOf 2 (H ⊔ D) ≠ ⊥ →
    K ∈ cComp (H ⊔ D) → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
    oTwoUpper H ≤ conjClosure K T → ¬ T ≤ Subgroup.normalizer (K : Set G) →
    (∃ q : ℕ, q.Prime ∧ (q % 24 = 11 ∨ q % 24 = 13) ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 q 1) →
    D ≤ Subgroup.normalizer (oTwoUpper H : Set G)

theorem obl3_3_13D12_gen4 : Obl3_3_13D12_Gen4 := by
  intro G _ _ hG T M L D H K h hH _ _ hO hK _ _ _ ⟨q, hq, hq24, hmod⟩
  exfalso
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hX : InH (P : Subgroup G) (H ⊔ D) := ⟨hH.1.trans le_sup_left, hO⟩
  have hd := modO2_dvd_of_inH hG h.qtke.2.1 P hX (K := K) (le_of_isSubnormal hK.2.2.1)
  exact false_of_psl_two_prime_of_dvd_20160 hq (by omega) hmod hd

end CFSG.GH74.QTGen4.Leaves
