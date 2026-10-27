module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylModel
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylQP
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylG2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylNonsplit
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylField

public noncomputable section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Classical
  CFSG.Open CFSG.Timmesfeld.ExceptionalOrders
open scoped MatrixGroups

section Conj

variable {K : Type} [Field K]

theorem conjSL_diagUnitOne_HSL (l : Kˣ) : conjSL (diagUnitOne l) (HSL l : SL2 K) = HSL l := by
  ext i j
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  fin_cases i <;> fin_cases j <;> simp [coe_HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjSL_diagUnitOne_WSL (l : Kˣ) : conjSL (diagUnitOne l) (WSL : SL2 K) = HSL l * WSL := by
  ext i j
  rw [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv]
  fin_cases i <;> fin_cases j <;>
    simp [coe_HSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem HSL_inv' (l : Kˣ) : (HSL l : SL2 K)⁻¹ = HSL l⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [HSL_mul', mul_inv_cancel, HSL_one']

end Conj

section Assembly


theorem exists_shapeConds_adjointG2 (K : Type) [Field K] [Finite K] (hodd : Nat.card K % 2 = 1) (n : ℕ)
    (hn : (Nat.card K ^ 2 - 1).factorization 2 = n + 1) :
    ∃ (S A : Subgroup ↥(adjointGroup .G2 K)) (a t y : ↥(adjointGroup .G2 K)), ShapeConds S A a t y n := by
  have h2 : (2 : K) ≠ 0 := by
    have := Fintype.ofFinite K
    refine Ring.two_ne_zero (fun hch => ?_)
    have := FiniteField.even_card_of_char_two hch
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hmod : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by omega
  rcases hmod with hK | hK
  · obtain ⟨n', ζ, hn', hn2, hζ1, hζ2, hζns⟩ := exists_split_data K hK
    have hnn : n' = n := by
      rw [factorization_sq_sub_one hq1, factorization_add_one_of_mod_four_eq_one hK, hn'] at hn
      omega
    subst hnn
    set T := g2TwistedPair ζ hζns with hT
    have hc : (HSL ζ : SL2 K) ^ (2 ^ n') = 1 := by rw [HSL_pow, hζ1, HSL_one']
    have hc2 : (HSL ζ : SL2 K) ^ (2 ^ (n' - 1)) = -1 := by rw [HSL_pow, hζ2, HSL_neg_one_eq]
    have hwc : (WSL : SL2 K) * HSL ζ * WSL⁻¹ = (HSL ζ)⁻¹ := by
      rw [WSL_conj_HSL, HSL_inv']
    have hQ := T.qpData_caseI h2 hn2 hc hc2 WSL_mul_WSL' hwc rfl (conjSL_diagUnitOne_HSL ζ)
      (conjSL_diagUnitOne_WSL ζ)
    exact ⟨_, _, _, _, _, shapeConds_of_qpData hQ⟩
  · obtain ⟨n', s, c, w, hn', hn2, hs, hc, hc2, hw, hwc, hcδ, hwδ⟩ := exists_nonsplit_quaternion K hK
    have hnn : n' = n := by
      rw [factorization_sq_sub_one hq1, factorization_sub_one_of_mod_four_eq_three hK, hn'] at hn
      omega
    subst hnn
    have := Fintype.ofFinite K
    have hns : ∀ p : K, ((-1 : Kˣ) : K) ≠ p * p := by
      intro p hp
      have hsq : IsSquare (-1 : K) := ⟨p, by simpa using hp⟩
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card] at hsq
      omega
    set T := g2TwistedPair (-1 : Kˣ) hns with hT
    have hδinv : (↑(diagUnitOne (-1 : Kˣ))⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![(-1 : K), 0; 0, 1] := by
      rw [coe_diagUnitOne_inv]; simp
    have hcδ' : conjSL (diagUnitOne (-1 : Kˣ)) c = c⁻¹ := by
      apply Subtype.ext
      rw [coe_conjSL, hδinv]
      exact hcδ
    have hwδ' : conjSL (diagUnitOne (-1 : Kˣ)) w = c ^ s * w := by
      apply Subtype.ext
      rw [coe_conjSL, hδinv]
      exact hwδ
    have hQ := T.qpData_caseII h2 hn2 hs hc hc2 hw hwc rfl hcδ' hwδ'
    exact ⟨_, _, _, _, _, shapeConds_of_qpData hQ⟩

theorem exists_sylow_shapeConds_adjointG2 (K : Type) [Field K] [Finite K] (hodd : Nat.card K % 2 = 1)
    (n : ℕ) (hn : (Nat.card K ^ 2 - 1).factorization 2 = n + 1) :
    ∃ (T : Sylow 2 ↥(adjointGroup .G2 K)) (A : Subgroup ↥(adjointGroup .G2 K))
      (a t y : ↥(adjointGroup .G2 K)), ShapeConds (T : Subgroup ↥(adjointGroup .G2 K)) A a t y n := by
  obtain ⟨S₀, A₀, a₀, t₀, y₀, hS₀⟩ := exists_shapeConds_adjointG2 K hodd n hn
  have hcardS : Nat.card ↥S₀ = 2 ^ (2 * n + 2) := hS₀.card_eq
  have hG : Nat.card ↥(adjointGroup .G2 K) = ordG2 (Nat.card K) := card_adjointGroup_G2
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hvG : (Nat.card ↥(adjointGroup .G2 K)).factorization 2 = 2 * n + 2 := by
    rw [hG]
    unfold ordG2
    rw [factorization_ordG2 hodd hq1, hn]
    ring
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Sylow.ofCard S₀ (by rw [hcardS, hvG]), A₀, a₀, t₀, y₀, ?_⟩
  rw [Sylow.coe_ofCard]
  exact hS₀

theorem g2_sylow_of_shapeConds {X : Type} [Group X] [Finite X] {S A : Subgroup X} {a t y : X} {n : ℕ}
    (hshape : ShapeConds S A a t y n) (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 0 < f)
    (hval : ((p ^ f) ^ 2 - 1).factorization 2 = n + 1) :
    ∃ (Gs : Type) (_ : Group Gs) (_ : Finite Gs), LieModel Gs .G2 0 p f ∧
      ∃ S' : Sylow 2 Gs, Nonempty (↥S ≃* ↥(S' : Subgroup Gs)) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p f
  have hcardK : Nat.card K = p ^ f := GaloisField.card p f hf.ne'
  have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Nat.card K % 2 = 1 := by rw [hcardK]; exact Nat.odd_iff.1 hpodd
  have hval' : (Nat.card K ^ 2 - 1).factorization 2 = n + 1 := by rw [hcardK]; exact hval
  obtain ⟨T, A₀, a₀, t₀, y₀, hS₀⟩ := exists_sylow_shapeConds_adjointG2 K hodd n hval'
  refine ⟨↥(adjointGroup .G2 K), inferInstance, inferInstance, ?_, ⟨T, ?_⟩⟩
  · have hcen := center_adjointGroup_eq_bot (τ := .G2) (K := K)
    let e : ↥(adjointGroup .G2 K) ≃* AdjointQuotient .G2 K :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
    have h3 : 3 ≤ p ^ f := by
      have : 3 ≤ p := by
        have := hp.two_le
        have := hp.eq_one_or_self_of_dvd 2
        rcases Nat.lt_or_ge p 3 with h | h
        · have : p = 2 := by omega
          exact absurd this hp2
        · exact h
      calc 3 ≤ p := this
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    right; left
    refine ⟨rfl, by decide, ⟨hp, hf, rfl, h3⟩, K, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
  · exact shapeConds_mulEquiv hshape hS₀

end Assembly

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
