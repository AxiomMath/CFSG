module

public import CFSG.HardMathSupport.GuralnickMalle.AdjointHeart
public import CFSG.HardMathSupport.GuralnickMalle.InvolutionRank
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.UnitaryOrderBound

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open CFSG.Open CFSG.HardMathSupport.GuralnickMalle Module
open CFSG.LieType.Universal.Unitary (conjTr mem_SUid SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

theorem two_mul_sub_four_le_finrank_range_adjointHeartRep_sub_one {K : Type} [Field K]
    [CharP K 2] {m : ℕ} (x : GL (Fin m) K) (hx : x * x = 1) (hx1 : x ≠ 1) :
    2 * m - 4 ≤ Module.finrank K
      (LinearMap.range (CFSG.HardMathSupport.GuralnickMalle.adjointHeartRep m K x - 1)) := by
  have h₁ :=
    CFSG.HardMathSupport.GuralnickMalle.two_mul_sub_two_le_finrank_range_conj_sub_one x hx hx1
  have h₂ :=
    CFSG.HardMathSupport.GuralnickMalle.finrank_range_conj_sub_one_le_adjointHeart (m := m) x
  omega

theorem card_le_of_adjointHeart_of_le_statedSU {K : Type} [Field K] [Finite K] {m f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {A : Subgroup (GL (Fin m) K)}
    (hAS : A ≤ CFSG.Open.StatedSU m (2 ^ f) K) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hq : ∀ a ∈ A, ∀ b ∈ A,
      (CFSG.HardMathSupport.GuralnickMalle.adjointHeartRep m K a - 1) *
        (CFSG.HardMathSupport.GuralnickMalle.adjointHeartRep m K b - 1) = 0) :
    Nat.card A ≤ 2 ^ f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (r := 2) (n := f * 2) Nat.prime_two
      (by rw [hK, pow_mul])
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_pow] at hK
    have h1 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    omega
  have h2f : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hf)
  rcases Subgroup.bot_or_exists_ne_one A with hbot | ⟨a₀, ha₀A, ha₀ne⟩
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_pow f 2 (by norm_num)
  ·
    obtain ⟨N, hN⟩ := exists_smul_eq_of_adjointHeart (K := K) (m := m) hA hq
    have hN₀ne : unipotentMat a₀ ≠ 0 := by
      intro h0
      apply ha₀ne
      refine unipotentMat_injective ?_
      calc unipotentMat a₀ = 0 := h0
        _ = unipotentMat (1 : GL (Fin m) K) := by simp [unipotentMat]
    let μ : A → K := fun a => Classical.choose (hN (a : GL (Fin m) K) a.2)
    have hμspec : ∀ a : A,
        unipotentMat (a : GL (Fin m) K) = μ a • N := fun a =>
      Classical.choose_spec (hN (a : GL (Fin m) K) a.2)
    let μ₀ : K := μ ⟨a₀, ha₀A⟩
    have hμ₀spec : unipotentMat a₀ = μ₀ • N := hμspec ⟨a₀, ha₀A⟩
    have hμ₀ne : μ₀ ≠ 0 := by
      intro h0
      apply hN₀ne
      rw [hμ₀spec, h0, zero_smul]
    have hN_eq : N = μ₀⁻¹ • unipotentMat a₀ := by
      rw [hμ₀spec, smul_smul, inv_mul_cancel₀ hμ₀ne, one_smul]
    have hνspec : ∀ a : A,
        unipotentMat (a : GL (Fin m) K) = (μ a / μ₀) • unipotentMat a₀ := by
      intro a
      rw [hμspec a, hN_eq, smul_smul, div_eq_mul_inv]
    have huni : ∀ a ∈ A,
        conjTr (unitaryInvolution K 2 f) ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *
          ((a : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 := by
      intro a ha
      have hSU : (a : GL (Fin m) K) ∈ SUid (unitaryInvolution K 2 f) m := by
        rw [SUid_eq_statedSU hK m]
        exact hAS ha
      exact (mem_SUid.mp hSU).2
    have hsq : ∀ a ∈ A,
        (a : GL (Fin m) K) * (a : GL (Fin m) K) = 1 := by
      intro a ha
      simpa [pow_two] using hA.2 (a : GL (Fin m) K) ha
    have hfix : ∀ a ∈ A,
        conjTr (unitaryInvolution K 2 f) (unipotentMat a) = unipotentMat a :=
      fun a ha => conjTr_unipotentMat (unitaryInvolution K 2 f) (huni a ha) (hsq a ha)
    have hfixν : ∀ a : A,
        unitaryInvolution K 2 f (μ a / μ₀) = μ a / μ₀ := by
      intro a
      have hself : conjTr (unitaryInvolution K 2 f) ((μ a / μ₀) • unipotentMat a₀) =
          (μ a / μ₀) • unipotentMat a₀ := by
        rw [← hνspec a]
        exact hfix (a : GL (Fin m) K) a.2
      have hσ : unitaryInvolution K 2 f (μ a / μ₀) • unipotentMat a₀ =
          (μ a / μ₀) • unipotentMat a₀ := by
        calc unitaryInvolution K 2 f (μ a / μ₀) • unipotentMat a₀
            = unitaryInvolution K 2 f (μ a / μ₀) •
                conjTr (unitaryInvolution K 2 f) (unipotentMat a₀) := by
              rw [hfix a₀ ha₀A]
          _ = conjTr (unitaryInvolution K 2 f) ((μ a / μ₀) • unipotentMat a₀) := by
              rw [conjTr_smul]
          _ = (μ a / μ₀) • unipotentMat a₀ := hself
      exact smul_eq_of_smul_eq_of_ne_zero hN₀ne hσ
    let ν : A → {c : K // unitaryInvolution K 2 f c = c} :=
      fun a => ⟨μ a / μ₀, hfixν a⟩
    have hνval : ∀ a : A, (ν a : K) = μ a / μ₀ := fun a => rfl
    have hinj : Function.Injective ν := by
      intro a b hab
      apply Subtype.ext
      apply unipotentMat_injective
      have h : (ν a : K) = (ν b : K) := congrArg Subtype.val hab
      rw [hνval a, hνval b] at h
      rw [hνspec a, hνspec b, h]
    calc Nat.card A ≤ Nat.card {c : K // unitaryInvolution K 2 f c = c} :=
          Nat.card_le_card_of_injective ν hinj
      _ ≤ 2 ^ f :=
          card_fixed_le_pow (q := 2 ^ f) h2f (unitaryInvolution K 2 f) (fun c => by
            rw [unitaryInvolution_apply])

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
