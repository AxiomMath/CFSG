module

public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.RankThree.PartTwo.Sec11.Item119

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

theorem nonempty_projSL_two_seven_equiv_three_two :
    Nonempty (projSL 2 (GaloisField 7 1) ≃* projSL 3 (GaloisField 2 1)) := by
  obtain ⟨e₄⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let ψ7 : ZMod 7 ≃+* GaloisField 7 1 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod 7) 7 1 Nat.one_pos (by simp)
  let ψ2 : ZMod 2 ≃+* GaloisField 2 1 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod 2) 2 1 Nat.one_pos (by simp)
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  exact ⟨((((((projSLEquivPSLn 2 (GaloisField 7 1)).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv ψ7 (Fin 2)).symm).trans
    e₄.symm).trans e₃.symm).trans e₂.symm).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv ψ2 (Fin 3))).trans
    (projSLEquivPSLn 3 (GaloisField 2 1)).symm⟩


private theorem cubic_bound (q : ℕ) (hq : 8 ≤ q) : 504 ≤ q * (q ^ 2 - 1) := by
  have h1 : 64 ≤ q ^ 2 := by nlinarith
  have h2 : 63 ≤ q ^ 2 - 1 := by omega
  calc 504 = 8 * 63 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h2

private theorem big_bound (q : ℕ) (hq : 4 ≤ q) :
    1000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have h1 : 16 ≤ q ^ 2 := by nlinarith
  have h2 : 15 ≤ q ^ 2 - 1 := by omega
  have h3 : 64 ≤ q ^ 3 := by nlinarith
  calc 1000 ≤ 64 * (15 * 65) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
        Nat.mul_le_mul h3 (Nat.mul_le_mul h2 (by omega))

private theorem big_bound' (q : ℕ) (hq : 4 ≤ q) :
    1000 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h1 : 16 ≤ q ^ 2 := by nlinarith
  have h2 : 15 ≤ q ^ 2 - 1 := by omega
  have h3 : 64 ≤ q ^ 3 := by nlinarith
  have h4 : 63 ≤ q ^ 3 - 1 := by omega
  calc 1000 ≤ 64 * (15 * 63) := by norm_num
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
        Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h4)

theorem nonempty_equiv_projSL_three_two_of_type424 {Q : Type} [Group Q] [Finite Q]
    (hT : Sec11.IsType424 Q) (hcard : Nat.card Q = 168) :
    Nonempty (Q ≃* projSL 3 (GaloisField 2 1)) := by
  rcases hT with ⟨n, hn, ⟨e⟩⟩ | ⟨p, n, hp, h3p, hn, ⟨e⟩⟩ | ⟨n, hn, hL⟩
  ·
    exfalso
    have hc : Nat.card (projSL 2 (GaloisField 2 n)) = 168 := by
      rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
    have h := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_two_mul (GaloisField 2 n)
    rw [hc, GaloisField.card 2 n (by omega)] at h
    have hg : Nat.gcd 2 (2 ^ n - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := cubic_bound _ h8
      omega
    interval_cases n <;> norm_num at h
  ·
    have hc : Nat.card (projSL 2 (GaloisField p n)) = 168 := by
      rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
    have h := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_two_mul (GaloisField p n)
    rw [hc, GaloisField.card p n (by omega)] at h
    have hg : Nat.gcd 2 (p ^ n - 1) ≤ 2 := Nat.gcd_le_left _ (by norm_num)
    have hg1 : 1 ≤ Nat.gcd 2 (p ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hp5 : 5 ≤ p := by
      have := hp.out.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp.out (by norm_num)
      omega
    have hq5 : 5 ≤ p ^ n := by
      calc 5 ≤ p := hp5
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
    have hq7 : p ^ n ≤ 7 := by
      by_contra hlt
      have := cubic_bound _ (by omega : 8 ≤ p ^ n)
      omega
    have hq : p ^ n = 7 := by
      generalize p ^ n = q at h hg hg1 hq5 hq7
      interval_cases q <;> simp_all
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 hq
    obtain ⟨f⟩ := nonempty_projSL_two_seven_equiv_three_two
    exact ⟨e.trans f⟩
  · rcases hL with ⟨hmod, ⟨e⟩⟩ | ⟨hmod, ⟨e⟩⟩
    ·
      exfalso
      have hc : Nat.card (projSU 3 2 n) = 168 := by
        rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
      have h := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
      rw [hc] at h
      have hg : Nat.gcd 3 (2 ^ n + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have hn2 : 2 ≤ n := by
        by_contra h1
        have : n = 1 := by omega
        subst this
        norm_num at hmod
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have := big_bound _ h4
      have h' : 168 * Nat.gcd 3 (2 ^ n + 1) = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) *
          ((2 ^ n) ^ 3 + 1)) := h
      omega
    ·
      have hc : Nat.card (projSL 3 (GaloisField 2 n)) = 168 := by
        rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
      have h := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
      rw [hc, GaloisField.card 2 n (by omega)] at h
      have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
      have hn1 : n = 1 := by
        by_contra hn1
        have h4 : 4 ≤ 2 ^ n := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := big_bound' _ h4
        omega
      subst hn1
      exact ⟨e⟩

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
