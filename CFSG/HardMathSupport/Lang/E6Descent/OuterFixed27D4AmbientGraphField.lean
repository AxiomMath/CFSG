module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


section Powers

variable {K : Type} [Field K]

theorem normalForm_pow_adjX (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε n : ℕ) :
    ∃ B : Fin Tag.D4.rank → K, ∀ (i : Fin Tag.D4.rank) (c : K),
      ((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ n) (adjX Tag.D4 K i c) =
        adjX Tag.D4 K (((d4Rho ^ ε) ^ n) i) (B i * (σ ^ n) c) := by
  induction n with
  | zero => exact ⟨fun _ => 1, fun i c => by simp⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨fun i => B ((d4Rho ^ ε) i) * (σ ^ n) (a ((d4Rho ^ ε) i)), fun i c => ?_⟩
    rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjX, exactNormalAut_adjX,
      exactPerm_zero, Equiv.Perm.one_apply, hB, pow_succ, pow_succ, Equiv.Perm.mul_apply,
      RingAut.mul_apply, map_mul]
    rw [mul_assoc]

theorem sigma_pow_three_eq_one_of_pow_three (a b : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (h : (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ 3 = exactNormalAut Tag.D4 K b 1 0) :
    σ ^ 3 = 1 := by
  obtain ⟨B, hB⟩ := normalForm_pow_adjX a σ ε 3
  have hρ : ((d4Rho ^ ε) ^ 3 : Equiv.Perm (Fin Tag.D4.rank)) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show d4Rho ^ 3 = 1 from TwistTag.perm_pow_order TwistTag.D4,
      one_pow]
  have hx : ∀ i c, adjX Tag.D4 K i (B i * (σ ^ 3) c) = adjX Tag.D4 K i ((b i : K) * c) := by
    intro i c
    have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.D4 K) => φ (adjX Tag.D4 K i c)) h
    simp only [hB, hρ, Equiv.Perm.one_apply, exactNormalAut_adjX, exactPerm_zero] at h1
    simpa using h1
  have hB1 : ∀ i, B i = (b i : K) := fun i => by
    have := adjX_injective _ (hx i 1)
    simpa using this
  refine RingEquiv.ext fun c => ?_
  have h2 := adjX_injective _ (hx ⟨0, by decide⟩ c)
  rw [hB1] at h2
  rw [RingAut.one_apply]
  exact mul_left_cancel₀ (b ⟨0, by decide⟩).ne_zero h2

theorem pow_three_eq_exactNormalAut_diag [Finite K] (β : MulAut (adjointGroup Tag.D4 K))
    (hA : β ∈ unipotentPairAut Tag.D4 K) (g : adjointGroup Tag.D4 K)
    (hα3 : (MulAut.conj g * β) ^ 3 = 1) :
    ∃ b : Fin Tag.D4.rank → Kˣ, β ^ 3 = exactNormalAut Tag.D4 K b 1 0 := by
  have hβ3 : β ^ 3 = MulAut.conj (g * β g * β (β g))⁻¹ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : ((MulAut.conj g * β) ^ 3) x =
        (g * β g * β (β g)) * (β ^ 3) x * (g * β g * β (β g))⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul,
        map_inv]
      group
    rw [hα3, MulAut.one_apply] at h1
    rw [MulAut.conj_apply, inv_inv]
    calc (β ^ 3) x = (g * β g * β (β g))⁻¹ * ((g * β g * β (β g)) * (β ^ 3) x *
          (g * β g * β (β g))⁻¹) * (g * β g * β (β g)) := by group
      _ = (g * β g * β (β g))⁻¹ * x * (g * β g * β (β g)) := by rw [← h1]
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have hβ3A : β ^ 3 ∈ unipotentPairAut Tag.D4 K := pow_mem hA 3
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (hβ3 ▸ hβ3A)
  exact ⟨b, hβ3.trans hb⟩

theorem sigma_pow_three_eq_one_of_cube [Finite K] (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K)
    (ε : ℕ)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    σ ^ 3 = 1 := by
  have hA : exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem ε)
  obtain ⟨b, hb⟩ := pow_three_eq_exactNormalAut_diag _ hA g (hα ▸ hα3)
  exact sigma_pow_three_eq_one_of_pow_three a b σ ε hb

end Powers

theorem twentySeven_dvd_card_fixedSubgroup_graphField {ℓ f : ℕ} [Fact ℓ.Prime]
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (h3 : ¬ 3 ∣ ℓ)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0) (hσ : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hσ3 := sigma_pow_three_eq_one_of_cube α hα3 g a σ ε hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three (Fact.out : ℓ.Prime) hf K hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  have h3' : ¬ 3 ∣ ℓ ^ e := fun h => h3 (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  exact twentySeven_dvd_card_fixedSubgroup_of_normalForm_orient K hK hK4 he hef h3' T σ hT hσT α
    hα3 g a ε (by omega) hα

end CFSG.HardMathSupport.Lang.E6Descent
