module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.AGLEmbedding
open Matrix

namespace L34BetaHPara

section Matrices

variable {k : Type} [Field k] [CharP k 2]

@[expose] def m3M : Matrix (Fin 3) (Fin 3) k := !![1, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def m3 : SpecialLinearGroup (Fin 3) k :=
  ⟨m3M, by simp only [m3M, det_fin_three]; simp [CharTwo.neg_eq]⟩

theorem m3_inv_transpose :
    ((m3 : SpecialLinearGroup (Fin 3) k)⁻¹).transpose = m3⁻¹ := by
  apply Subtype.ext
  change (adjugate m3M).transpose = adjugate m3M
  rw [adjugate_fin_three]
  simp only [m3M]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem m3_pow_three : (m3 : SpecialLinearGroup (Fin 3) k) ^ 3 = 1 := by
  have h : (m3 : SpecialLinearGroup (Fin 3) k) ^ 3 = m3 * m3 * m3 := by
    simp only [pow_succ, pow_zero, one_mul]
  rw [h]
  apply Subtype.ext
  change m3M * m3M * m3M = 1
  simp only [m3M, mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CharTwo.add_self_eq_zero]

theorem m3_not_mem_scalars : (m3 : SpecialLinearGroup (Fin 3) k) ∉ scalars 3 k := by
  intro h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have h01 := congrFun (congrFun hc 0) 1
  change m3M 0 1 = _ at h01
  simp [m3M, Matrix.scalar_apply] at h01

theorem map_m3 (σ : k ≃+* k) :
    SpecialLinearGroup.map σ.toRingHom (m3 : SpecialLinearGroup (Fin 3) k) = m3 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe]
  change σ.toRingHom.mapMatrix m3M = m3M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m3M]

theorem orderOf_proj_m3 : orderOf (proj 3 k (m3 : SpecialLinearGroup (Fin 3) k)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, m3_pow_three, map_one]
  · rw [Ne, proj_eq_one_iff]
    exact m3_not_mem_scalars

omit [CharP k 2] in
theorem betaAut_proj {σ : k ≃+* k} (g : SpecialLinearGroup (Fin 3) k) :
    L34.betaAut σ (proj 3 k g) =
      proj 3 k (SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose) := by
  rw [L34.betaAut, MulAut.mul_apply, dualAut_proj, fieldAut_proj]

theorem betaAut_proj_m3 {σ : k ≃+* k} :
    L34.betaAut σ (proj 3 k (m3 : SpecialLinearGroup (Fin 3) k)) =
      (proj 3 k (m3 : SpecialLinearGroup (Fin 3) k))⁻¹ := by
  rw [betaAut_proj, m3_inv_transpose, map_inv, map_m3, map_inv]

end Matrices

section Transport

open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (mem_autFixed)

theorem exists_orderThree_inverted {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K)
    {E : Subgroup K} (hE : Nat.card E = 9) :
    ∃ y : K, orderOf y = 3 ∧ y ∉ Subgroup.normalizer (E : Set K) ∧
      ∀ α : MulAut K, (∀ e ∈ E, α e = e) → ¬ 3 ∣ orderOf α → α = 1 ∨ α y = y⁻¹ := by
  obtain ⟨ε₀⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv (GaloisField 2 2) 2 a = a ^ 2 := fun a =>
    frobeniusEquiv_apply (GaloisField 2 2) 2 a
  have hE₁ : Nat.card (E.map ε₀.toMonoidHom) = 9 := by
    rw [← hE]
    exact (Nat.card_congr (ε₀.subgroupMap E).toEquiv).symm
  obtain ⟨g, hg⟩ := L34.exists_eq_map_conj_eZero hk hE₁
  let ε : projectiveSL 3 (GaloisField 2 2) ≃* K := (MulAut.conj g).trans ε₀.symm
  have hεE : ∀ p, p ∈ L34.eZero (GaloisField 2 2) ↔ ε p ∈ E := by
    intro p
    have h1 : ε p ∈ E ↔ g * p * g⁻¹ ∈ E.map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * p * g⁻¹) * g = p by group]
  set x : projectiveSL 3 (GaloisField 2 2) := proj 3 (GaloisField 2 2) m3 with hx
  refine ⟨ε x, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hx, orderOf_proj_m3]
  · intro hn
    have hn' : x ∈ Subgroup.normalizer (L34.eZero (GaloisField 2 2) : Set _) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      have h := Subgroup.mem_normalizer_iff.mp hn (ε q)
      rw [hεE q, hεE (x * q * x⁻¹), map_mul, map_mul, map_inv]
      exact h
    rw [← L34.autFixed_betaAut hk hσ] at hn'
    have h1 := (mem_autFixed).mp hn'
    rw [hx, betaAut_proj_m3] at h1
    have h2 : (proj 3 (GaloisField 2 2) m3) ^ 2 = 1 := by
      rw [sq]
      exact mul_eq_one_iff_eq_inv.mpr h1.symm
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [orderOf_proj_m3] at h3
    omega
  · intro α hfix h3
    set α' : MulAut (projectiveSL 3 (GaloisField 2 2)) := MulAut.congr ε.symm α with hα'
    have hα'apply : ∀ p, α' p = ε.symm (α (ε p)) := fun p => by
      rw [hα', MulAut.congr_apply]
      simp
    have hfix' : ∀ p ∈ L34.eZero (GaloisField 2 2), α' p = p := fun p hp => by
      rw [hα'apply, hfix (ε p) ((hεE p).mp hp)]
      exact ε.symm_apply_apply p
    have hord : ¬ 3 ∣ orderOf α' := by
      rwa [hα', MulEquiv.orderOf_eq]
    rcases L34.eq_one_or_eq_betaAut hk hσ hfix' hord with h | h
    · left
      apply (MulAut.congr ε.symm).injective
      rw [← hα', h, map_one]
    · right
      have h1 := hα'apply x
      rw [h, hx, betaAut_proj_m3] at h1
      have h2 : α (ε x) = ε (x⁻¹) := by
        have := congrArg ε h1
        rw [ε.apply_symm_apply] at this
        simpa [hx] using this.symm
      rw [h2, map_inv]

end Transport

section Outer

theorem exists_inverted_of_centralizes {X : Type} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] (hC : Subgroup.centralizer (K : Set X) = ⊥) (hK : IsLinThreeFour K)
    {E : Subgroup X} (hEK : E ≤ K) (hE : Nat.card E = 9) {V : Subgroup X} (hV : IsPGroup 2 V)
    (hVE : ∀ t ∈ V, ∀ e ∈ E, t * e = e * t) :
    ∃ y ∈ K, orderOf y = 3 ∧ y ∉ Subgroup.normalizer (E : Set X) ∧
      ∀ t ∈ V, t = 1 ∨ t * y * t⁻¹ = y⁻¹ := by
  have hE' : Nat.card (E.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE]
  obtain ⟨y, hy3, hyN, hy⟩ := exists_orderThree_inverted hK hE'
  refine ⟨(y : X), y.2, by rw [Subgroup.orderOf_coe, hy3], ?_, fun t ht => ?_⟩
  · intro hn
    apply hyN
    rw [← Subgroup.subgroupOf_normalizer_eq hEK]
    exact hn
  · set α : MulAut K := MulAut.conjNormal t with hα
    have hfix : ∀ e ∈ E.subgroupOf K, α e = e := fun e he => by
      apply Subtype.ext
      rw [hα, MulAut.conjNormal_apply]
      have := hVE t ht e (Subgroup.mem_subgroupOf.mp he)
      rw [this, mul_inv_cancel_right]
    have hord : ¬ 3 ∣ orderOf α := by
      obtain ⟨n, hn⟩ := hV ⟨t, ht⟩
      have hn' : t ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have h1 : α ^ 2 ^ n = 1 := by rw [hα, ← map_pow, hn', map_one]
      intro h3
      have h4 := h3.trans (orderOf_dvd_of_pow_eq_one h1)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4) (by norm_num)
    rcases hy α hfix hord with h | h
    · left
      have hcent : t ∈ Subgroup.centralizer (K : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h1 := congrArg Subtype.val (DFunLike.congr_fun h ⟨k, hk⟩)
        rw [hα, MulAut.conjNormal_apply] at h1
        change t * k * t⁻¹ = k at h1
        calc k * t = (t * k * t⁻¹) * t := by rw [h1]
          _ = t * k := by group
      rw [hC, Subgroup.mem_bot] at hcent
      exact hcent
    · right
      have h1 := congrArg Subtype.val h
      rw [hα, MulAut.conjNormal_apply] at h1
      exact h1

end Outer

end L34BetaHPara

end CFSG.AGLEmbeddingD2
