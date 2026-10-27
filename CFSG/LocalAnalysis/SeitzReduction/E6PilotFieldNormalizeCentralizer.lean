module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutUBasic

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section RootElements

variable {n : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem exists_ne_zero_of_row (A : GL (Fin n) K) (r : Fin n) :
    ∃ s, (A : Matrix (Fin n) (Fin n) K) r s ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := congrFun (congrFun (Units.mul_inv A) r) r
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  simp only [h, zero_mul, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

theorem exists_eq_fieldAut_of_forall_apply_transvection (hn : 3 ≤ n) {S : Set K}
    (hS1 : (1 : K) ∈ S) {β : MulAut (projectiveSL n K)}
    (hβ : ∀ (i j : Fin n) (hij : i ≠ j), ∀ c ∈ S,
      β (proj n K (SpecialLinearGroup.transvection hij c)) =
        proj n K (SpecialLinearGroup.transvection hij c)) :
    ∃ ρ : K ≃+* K, (∀ c ∈ S, ρ c = c) ∧ β = fieldAut n K ρ := by
  obtain ⟨A, ρ, ε, hε, rfl⟩ := (automorphism_generation hn).2 β
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => absurd (congrArg Fin.val h) (by simp [i₀, i₁])
  have h02 : i₀ ≠ i₂ := fun h => absurd (congrArg Fin.val h) (by simp [i₀, i₂])
  interval_cases ε
  ·
    simp only [pow_zero, mul_one] at hβ ⊢
    have key : ∀ (i j : Fin n) (hij : i ≠ j), ∀ c ∈ S,
        single i j c * (A : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * single i j (ρ c) := fun i j hij c hc =>
      LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_apply A ρ hij c c (hβ i j hij c hc)
    have hcomm : Pairwise fun i j => Commute (single i j (1 : K))
        (A : Matrix (Fin n) (Fin n) K) := fun i j hij => by
      have h := key i j hij 1 hS1
      rw [map_one] at h
      exact h
    obtain ⟨a, ha⟩ := mem_range_scalar_of_commute_single hcomm
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨s, hs⟩ := exists_ne_zero_of_row A i₀
      rw [← ha] at hs
      exact hs (by simp)
    have hA : A = GeneralLinearGroup.scalar (Fin n) (Units.mk0 a ha0) := by
      refine Units.ext ?_
      rw [← ha, GeneralLinearGroup.coe_scalar]
      rfl
    refine ⟨ρ, fun c hc => ?_, by rw [hA, LinearFlag.conjAut_scalar, one_mul]⟩
    have h := congrFun (congrFun (key i₀ i₁ h01 c hc) i₀) i₁
    rw [← ha] at h
    simp only [scalar_apply, mul_diagonal, diagonal_mul, single_apply_same] at h
    rw [mul_comm a] at h
    exact (mul_right_cancel₀ ha0 h).symm
  ·
    exfalso
    simp only [pow_one] at hβ
    have key : ∀ (i j : Fin n) (hij : i ≠ j),
        single i j (1 : K) * (A : Matrix (Fin n) (Fin n) K) =
          (A : Matrix (Fin n) (Fin n) K) * single j i (-ρ 1) := fun i j hij =>
      LinearPilot.single_mul_eq_of_conjAut_mul_fieldAut_mul_dualAut_apply A ρ hij 1 1
        (hβ i j hij 1 hS1)
    have hrow : ∀ i : Fin n, i ≠ i₀ → ∀ s, s ≠ i → (A : Matrix (Fin n) (Fin n) K) i₀ s = 0 := by
      intro i hi s hs
      have h := congrFun (congrFun (key i i₀ hi) i) s
      rw [single_mul_apply_same, one_mul, mul_single_apply_of_ne _ _ _ _ _ hs] at h
      exact h
    obtain ⟨s, hs⟩ := exists_ne_zero_of_row A i₀
    by_cases hs1 : s = i₁
    · exact hs (hrow i₂ h02.symm s (by rw [hs1]; exact fun h => h01 (by
        rw [← Fin.val_inj] at h ⊢; simp [i₁, i₂] at h)))
    · exact hs (hrow i₁ h01.symm s hs1)

end RootElements

section Galois

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_or_eq_of_forall_fix {σ : K ≃+* K} (hσ : orderOf σ = 2) {ρ : K ≃+* K}
    (hρ : ∀ c, σ c = c → ρ c = c) : ρ = 1 ∨ ρ = σ := by
  obtain ⟨e, he, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨-, -, -, -, -, hsub⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two he hK
  set A := Subgroup.closure ({ρ, σ} : Set (K ≃+* K)) with hA
  set B := Subgroup.zpowers σ with hBdef
  have hB : Nat.card B = 2 := by rw [hBdef, Nat.card_zpowers, hσ]
  have hBA : B ≤ A := (Subgroup.zpowers_le).2 (Subgroup.subset_closure (by simp))
  have hfixA : {a | ∀ τ ∈ A, τ a = a} = {a | ∀ τ ∈ B, τ a = a} := by
    ext a
    constructor
    · intro h τ hτ
      exact h τ (hBA hτ)
    · intro h τ hτ
      have hσa : σ a = a := h σ (Subgroup.mem_zpowers σ)
      induction hτ using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl | hx
        · exact hρ a hσa
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hσa
      | one => rfl
      | mul x y _ _ hx hy => rw [RingAut.mul_apply, hy, hx]
      | inv x _ hx =>
        conv_lhs => rw [← hx]
        rw [← RingAut.mul_apply, inv_mul_cancel]
        rfl
  obtain ⟨hAd, SA, hSA, hcA⟩ := hsub A
  obtain ⟨hBd, SB, hSB, hcB⟩ := hsub B
  have hSAB : SA = SB := SetLike.coe_injective (hSA.trans (hfixA.trans hSB.symm))
  have hcard : 2 ^ (e / Nat.card A) = 2 ^ (e / 2) := by rw [← hcA, hSAB, hcB, hB]
  have he2 : e / Nat.card A = e / 2 := Nat.pow_right_injective le_rfl hcard
  rw [hB] at hBd
  have hA2 : Nat.card A = 2 := by
    obtain ⟨m, hm⟩ := hAd
    obtain ⟨m', hm'⟩ := hBd
    have hApos : 0 < Nat.card A := Nat.card_pos
    have h1 : e / Nat.card A = m := by rw [hm, Nat.mul_div_cancel_left _ hApos]
    have h2 : e / 2 = m' := by rw [hm', Nat.mul_div_cancel_left _ (by norm_num)]
    have hmm : m = m' := by rw [← h1, ← h2, he2]
    have hm0 : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · rw [h, mul_zero] at hm'
        omega
      · exact h
    rw [hmm] at hm
    exact Nat.eq_of_mul_eq_mul_right hm0 (hm.symm.trans hm')
  have hAB : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hA2, hB])
  have hρA : ρ ∈ A := Subgroup.subset_closure (by simp)
  rw [← hAB] at hρA
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hρA
  rw [← zpow_mod_orderOf, hσ]
  have hz : z % ((2 : ℕ) : ℤ) = 0 ∨ z % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hz with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem eq_one_or_eq_fieldAut_of_forall_apply_transvection {n : ℕ} (hn : 3 ≤ n)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) {β : MulAut (projectiveSL n K)}
    (hβ : ∀ (i j : Fin n) (hij : i ≠ j), ∀ c, σ c = c →
      β (proj n K (SpecialLinearGroup.transvection hij c)) =
        proj n K (SpecialLinearGroup.transvection hij c)) :
    β = 1 ∨ β = fieldAut n K σ := by
  obtain ⟨ρ, hρ, rfl⟩ := exists_eq_fieldAut_of_forall_apply_transvection (S := {c | σ c = c}) hn
    (map_one σ) hβ
  rcases eq_one_or_eq_of_forall_fix hσ (fun c hc => hρ c hc) with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

end Galois

end CFSG.SeitzReduction.E6Pilot
