module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartOne.K1214 (SylowShape)
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.RankThree.PartOne.K128
  (sylowShape_G2 pRank_le_one_G2 dvd_card_of_pRank_pos dvd_sq_sub_one_of_dvd_pow
    factorization_sq_pow)
open CFSG.LocalAnalysis.RankFourTheoremC (crossExc_not_dvd_pow_of_ne)

theorem heisG2_two_le_factorization {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hd : p ∣ ((2 ^ m₀) ^ p) ^ 2 - 1) : 2 ≤ (((2 ^ m₀) ^ p) ^ 2 - 1).factorization p := by
  have hp2 : p ≠ 2 := by omega
  have hq2 : 2 ≤ 2 ^ m₀ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m₀ := Nat.pow_le_pow_right (by norm_num) hm₀
  have hpq : ¬ p ∣ 2 ^ m₀ := crossExc_not_dvd_pow_of_ne hp Nat.prime_two (by omega)
  have hd' : p ∣ (2 ^ m₀) ^ 2 - 1 := dvd_sq_sub_one_of_dvd_pow hp hp2 hq2 hpq hd
  have hlte := factorization_sq_pow hp hp2 hq2 hpq
  simp only [hd', ↓reduceIte] at hlte
  rw [hlte]
  have hne : (2 ^ m₀) ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ (2 ^ m₀) ^ 2 := by nlinarith
    omega
  have hone : 1 ≤ ((2 ^ m₀) ^ 2 - 1).factorization p :=
    (hp.dvd_iff_one_le_factorization hne).1 hd'
  omega

theorem heisG2_sylow_data
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m)
    (eK : X ≃* adjointGroup .G2 K)
    (hfield : (∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → ∃ m₀ : ℕ, m = p * m₀) :
    ∀ S : Sylow p X, (∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x) ∧
      ((∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) →
        Nat.card {x : S // x ^ p = 1} ≤ p ∨
          ∀ x ∈ (S : Subgroup X), x ^ p = 1 → ∃ y ∈ (S : Subgroup X), y ^ p = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  haveI : Finite (adjointGroup .G2 K) := Finite.of_equiv X eK.toEquiv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp Nat.prime_two (by omega)
  have hab : ∀ S : Sylow p X, IsMulCommutative (S : Subgroup X) := fun S =>
    CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv eK
      (fun R => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_adjointGroup hp
        (CFSG.LocalAnalysis.RankFourTheoremC.crossExc_not_dvd_card_weylGroup_G2 hp hp5) hpK R) S
  intro S
  have habS : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y = y * x := fun x hx y hy => by
    haveI := hab S
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : (S : Subgroup X)) ⟨y, hy⟩)
  refine ⟨habS, fun hout => ?_⟩
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  ·
    have hshX := SylowShape.of_mulEquiv eK (sylowShape_G2 K hp hp5 hK hm hd)
    obtain ⟨e'⟩ := hshX (S : Subgroup X) S.isPGroup' S.not_dvd_index
    have h2 : 2 ≤ (Nat.card K ^ 2 - 1).factorization p := by
      obtain ⟨m₀, hm₀⟩ := hfield hout
      have hm₀pos : 1 ≤ m₀ := by
        rcases Nat.eq_zero_or_pos m₀ with h0 | h0
        · rw [h0, mul_zero] at hm₀
          omega
        · exact h0
      have hq : Nat.card K = (2 ^ m₀) ^ p := by rw [hK, hm₀, ← pow_mul, mul_comm]
      rw [hq] at hd ⊢
      exact heisG2_two_le_factorization hp hp5 hm₀pos hd
    exact homC_sylow_data hp e' (Or.inr h2)
  ·
    left
    have hrank : CFSG.pRank p X ≤ 1 := by
      by_cases hdvd : p ∣ Nat.card (adjointGroup .G2 K)
      · rw [CFSG.RankThree.PartOne.pRank_eq_of_mulEquiv_of_one_lt hp.one_lt eK]
        exact pRank_le_one_G2 K hp hp5 hK hm hdvd hd
      · have h1 : ¬ 1 ≤ CFSG.pRank p X := fun h1 =>
          hdvd (by rw [← Nat.card_congr eK.toEquiv]; exact dvd_card_of_pRank_pos hp h1)
        omega
    have hEA : CFSG.IsElementaryAbelian p (torsionSubgroup (S : Subgroup X) habS p) :=
      { toIsMulCommutative := torsionSubgroup_comm _ habS p
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (by simpa using ((mem_torsionSubgroup _ habS p).1 x.2).2) }
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.IsElementaryAbelian.isPGroup p
      (torsionSubgroup (S : Subgroup X) habS p))
    have hkle : k ≤ CFSG.pRank p X :=
      CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEA hk
    rw [torsionSubgroup_card] at hk
    calc Nat.card {x : S // x ^ p = 1} = p ^ k := hk
      _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (hkle.trans hrank)
      _ = p := pow_one p

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
