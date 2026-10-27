module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74A2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Coprime
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73C

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem le_normalizer_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : B ≤ normalizer (A : Set G) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h x hx b hb, mul_inv_cancel_right]
    exact hx
  · intro hx
    have e : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * ((b * x * b⁻¹) * b) := by group
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [h _ hx b hb]
        _ = b * x * b⁻¹ := by group
    rw [e]
    exact hx

theorem card_centralizer_upperSL2_le {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    Nat.card ↥(centralizer ({upperSL2 (1 : K)} : Set SL(2, K))) ≤ 2 * Nat.card K := by
  classical
  have key : ∀ M : SL(2, K), M ∈ centralizer ({upperSL2 (1 : K)} : Set SL(2, K)) →
      (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) K) 1 1 = M 0 0 ∧
        ((M : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 ∨ (M : Matrix (Fin 2) (Fin 2) K) 0 0 = -1) := by
    intro M hM
    have hc := mem_centralizer_singleton_iff.mp hM
    have e := congrArg (fun N : SL(2, K) => (N : Matrix (Fin 2) (Fin 2) K)) hc
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_upperSL2] at e
    have e01 := congrFun (congrFun e 0) 1
    have e11 := congrFun (congrFun e 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e11
    have h10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination e11
    have h11 : (M : Matrix (Fin 2) (Fin 2) K) 1 1 = M 0 0 := by linear_combination -e01
    have hdet := M.det_coe
    rw [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero] at hdet
    have hpm : ((M : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) * (M 0 0 + 1) = 0 := by
      linear_combination hdet
    refine ⟨h10, h11, ?_⟩
    rcases mul_eq_zero.mp hpm with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hne : (-1 : K) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  let φ : ↥(centralizer ({upperSL2 (1 : K)} : Set SL(2, K))) → Bool × K := fun M =>
    (decide (((M : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1),
      ((M : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 1)
  have hφ : Function.Injective φ := by
    intro M N hMN
    obtain ⟨hM10, hM11, hM00⟩ := key M M.2
    obtain ⟨hN10, hN11, hN00⟩ := key N N.2
    have h1 := congrArg Prod.fst hMN
    have h2' := congrArg Prod.snd hMN
    simp only [φ, decide_eq_decide] at h1 h2'
    have h00 : ((M : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 =
        ((N : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 := by
      rcases hM00 with hM | hM <;> rcases hN00 with hN | hN
      · rw [hM, hN]
      · exact absurd (h1.mp hM) (by rw [hN]; exact hne)
      · exact absurd (h1.mpr hN) (by rw [hM]; exact hne)
      · rw [hM, hN]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h2', hM10, hN10, hM11, hN11]
  calc Nat.card ↥(centralizer ({upperSL2 (1 : K)} : Set SL(2, K))) ≤ Nat.card (Bool × K) :=
        Nat.card_le_card_of_injective φ hφ
    _ = 2 * Nat.card K := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

section Odd

variable {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
  (hK : Nat.card K = p ^ f)
include hp hp2 hK

theorem card_centralizer_tSeven_qThree_le_odd :
    Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ≤
      Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 2 := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have hodd := odd_card_spin hp hp2 hK
  have := finite_spinSeven h2
  obtain ⟨-, hz1, hzc, -, -, -, hz1J, ht2J, hzt3J, -⟩ := spinZ_facts hp hp2 hK
  have hq : qThree K ∈ spinJ₁ K := ⟨upperSL2 1, rfl⟩
  set A₁ := spinJ₁ K ⊓ centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) with hA₁
  set B := spinJ₂ K ⊔ spinJ₃ K with hB
  have hle : centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
      centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K))) ≤ A₁ ⊔ B := by
    intro x hx
    have hxE : x ∈ spinE K := a2_holds K hodd hx
    rw [← range_spinMulOdd hodd] at hxE
    obtain ⟨⟨⟨a, b⟩, c⟩, rfl⟩ := hxE
    have hx' := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    rw [spinMulOdd_apply] at hx' ⊢
    have hqb : qThree K * (b : spinGroup (quadOdd 3 K)) = b * qThree K :=
      commute_spinJ₁_spinJ₂ hq b.2
    have hqc : qThree K * (c : spinGroup (quadOdd 3 K)) = c * qThree K :=
      commute_spinJ₁_spinJ₃ hq c.2
    have haq : (a : spinGroup (quadOdd 3 K)) * qThree K = qThree K * a := by
      have h1 : (a : spinGroup (quadOdd 3 K)) * qThree K * (b * c) = qThree K * a * (b * c) := by
        calc (a : spinGroup (quadOdd 3 K)) * qThree K * (b * c) = a * (qThree K * b) * c := by
              group
          _ = a * (b * qThree K) * c := by rw [hqb]
          _ = a * b * (qThree K * c) := by group
          _ = a * b * (c * qThree K) := by rw [hqc]
          _ = qThree K * (a * b * c) := by rw [← hx']; group
          _ = qThree K * a * (b * c) := by group
      exact mul_right_cancel h1
    rw [mul_assoc]
    exact mul_mem_sup ⟨a.2, mem_centralizer_singleton_iff.mpr haq⟩
      (mul_mem (mem_sup_left b.2) (mem_sup_right c.2))
  have hA₁ : Nat.card A₁ ≤ 2 * Nat.card K := by
    have hsub : A₁ ≤ (centralizer ({upperSL2 (1 : K)} : Set SL(2, K))).map (shortSeven K) := by
      rintro x ⟨hx1, hx2⟩
      obtain ⟨M, rfl⟩ := hx1
      have hac : shortSeven K M * qThree K = qThree K * shortSeven K M :=
        mem_centralizer_singleton_iff.mp hx2
      refine ⟨M, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply injective_shortSeven
      rw [map_mul, map_mul]
      exact hac
    calc Nat.card A₁ ≤ Nat.card ↥((centralizer ({upperSL2 (1 : K)} : Set SL(2, K))).map
          (shortSeven K)) := card_le_of_le hsub
      _ = Nat.card ↥(centralizer ({upperSL2 (1 : K)} : Set SL(2, K))) :=
          card_map_of_injective injective_shortSeven
      _ ≤ 2 * Nat.card K := card_centralizer_upperSL2_le h2
  have hB : Nat.card B = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
    have hN : spinJ₃ K ≤ normalizer (spinJ₂ K : Set (spinGroup (quadOdd 3 K))) :=
      le_normalizer_of_commute fun a ha b hb => commute_spinJ₂_spinJ₃_odd hodd ha hb
    have h := card_sup_mul_card_inf_of_le_normalizer' hN
    have hinf : spinJ₂ K ⊓ spinJ₃ K = ⊥ := eq_bot_iff.mpr fun y hy =>
      mem_bot.mpr ((spinJ_inf_eq_one_odd (K := K) hp hp2 hK (y := y)).2.2 hy.1 hy.2)
    rw [hinf, card_bot, mul_one,
      card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true true),
      card_range_sl2 _ (longSL2_injective _ fin3_zero_ne_one true false)] at h
    rw [h]
    ring
  have hzA : spinZ K ∈ A₁ :=
    ⟨hz1J, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hzc (qThree K)).symm⟩
  have hzB : spinZ K ∈ B := by
    have h := mul_mem (mem_sup_right hzt3J : spinZ K * tSeven K ∈ B)
      (inv_mem (mem_sup_left ht2J : tSeven K ∈ B))
    rwa [mul_inv_cancel_right] at h
  have hAB2 : 2 ≤ Nat.card ↥(A₁ ⊓ B) := by
    have : Nontrivial ↥(A₁ ⊓ B) :=
      ⟨⟨⟨spinZ K, hzA, hzB⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hBN : B ≤ normalizer (A₁ : Set (spinGroup (quadOdd 3 K))) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have hb' : b ∈ centralizer (spinJ₁ K : Set (spinGroup (quadOdd 3 K))) := by
      refine (sup_le (fun y hy => ?_) (fun y hy => ?_) : B ≤ _) hb
      · exact mem_centralizer_iff.mpr fun x hx => commute_spinJ₁_spinJ₂ hx hy
      · exact mem_centralizer_iff.mpr fun x hx => commute_spinJ₁_spinJ₃ hx hy
    exact mem_centralizer_iff.mp hb' a ha.1
  have hcard := card_sup_mul_card_inf_of_le_normalizer' hBN
  have hsup : Nat.card ↥(A₁ ⊔ B) ≤ Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
    have h1 : Nat.card ↥(A₁ ⊔ B) * 2 ≤ 2 * (Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2) :=
      calc Nat.card ↥(A₁ ⊔ B) * 2 ≤ Nat.card ↥(A₁ ⊔ B) * Nat.card ↥(A₁ ⊓ B) :=
            Nat.mul_le_mul_left _ hAB2
        _ = Nat.card A₁ * Nat.card B := hcard
        _ ≤ 2 * Nat.card K * Nat.card B := Nat.mul_le_mul_right _ hA₁
        _ = 2 * (Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2) := by rw [hB]; ring
    omega
  calc Nat.card ↥(centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) ⊓
        centralizer ({qThree K} : Set (spinGroup (quadOdd 3 K)))) ≤ Nat.card ↥(A₁ ⊔ B) :=
        card_le_of_le hle
    _ ≤ Nat.card K * (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := hsup
    _ = Nat.card K ^ 3 * (Nat.card K ^ 2 - 1) ^ 2 := by ring

end Odd

end CFSG.ComponentClassification.HarrisLit.T1.S74
