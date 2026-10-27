module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Iso
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Conj
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.ComponentClassification.TBLit CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups

section Psl

variable {n : ℕ} {K : Type} [Field K]

@[expose] def blockScalarHom (J : Finset (Fin n)) : Kˣ →* GL (Fin n) K where
  toFun γ := blockScalarGL J γ 1
  map_one' := by
    apply Units.ext
    rw [coe_blockScalarGL]
    simp only [Units.val_one]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i ∈ J <;> simp [diagonal_apply_eq]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  map_mul' α β := by
    apply Units.ext
    rw [Units.val_mul, coe_blockScalarGL, coe_blockScalarGL, coe_blockScalarGL,
      diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i ∈ J <;> simp [hi]

theorem blockScalarGL_eq (J : Finset (Fin n)) (α β : Kˣ) :
    blockScalarGL J α β = GeneralLinearGroup.scalar (Fin n) β * blockScalarHom J (α / β) := by
  apply Units.ext
  rw [Units.val_mul, coe_blockScalarGL]
  change _ = ((GeneralLinearGroup.scalar (Fin n) β : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
    ((blockScalarGL J (α / β) 1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  rw [coe_blockScalarGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i ∈ J
  · simp [hi, mul_div_cancel₀ _ β.ne_zero]
  · simp [hi]

theorem psl_oddCoreIn_cyclic_inner [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {t : MulAut (projectiveSL n K)} (htB : t ∈ B) (ht : orderOf t = 2) {A : GL (Fin n) K}
    (htA : t = conjAut n K A) : IsCyclic ↥(oddCoreIn B t) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hsc : ∀ (c : Kˣ) (Z : GL (Fin n) K), Commute (GeneralLinearGroup.scalar (Fin n) c) Z :=
    fun c Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hA2 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← htA, htt]
  obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA2
  have hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin n) c := by
    intro c hc
    have : t = 1 := by rw [htA, hc, conjAut_scalar]
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hconjB : ∀ H : GL (Fin n) K,
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤
        B.map (MulAut.conj (conjAut n K H)).toMonoidHom := by
    intro H
    rintro _ ⟨x, rfl⟩
    refine ⟨(conjAut n K H)⁻¹ * MulAut.conj x * conjAut n K H, hB ?_, ?_⟩
    · refine ⟨(conjAut n K H)⁻¹ x, ?_⟩
      ext y
      simp [MulAut.conj_apply]
    · ext y
      simp [MulAut.conj_apply]
  by_cases hsq : IsSquare (l : K)
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact l.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [← hl]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    set c := conjAut n K H with hc
    have hct : c * t * c⁻¹ = conjAut n K (signGL K J) := by
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hH, map_mul, conjAut_scalar, one_mul]
    set B' := B.map (MulAut.conj c).toMonoidHom with hB'def
    have hcore := oddCoreIn_map_conj B htB c
    rw [hct] at hcore
    have hW' : IsCyclic ↥(oddCoreIn B' (conjAut n K (signGL K J))) := by
      refine isCyclic_of_le_range ((conjAut n K).comp (blockScalarHom J)) fun y hy => ?_
      obtain ⟨α, β, rfl⟩ := split_oddCoreIn hK hn hinj (hconjB H) ha hb hy
      refine ⟨α / β, ?_⟩
      show conjAut n K (blockScalarGL J (α / β) 1) = conjAut n K (blockScalarGL J α β)
      rw [blockScalarGL_eq J α β, map_mul, conjAut_scalar, one_mul]
      rfl
    rw [hcore] at hW'
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.surjective
  · have hev := even_of_sq_eq_nonsquare hl.symm hsq
    obtain ⟨m, rfl⟩ : ∃ m, n = m * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hm : 2 ≤ m := by omega
    have : NeZero (m * 2) := ⟨by omega⟩
    have hAm : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * A = (l : K) • 1 := by
      have := congrArg Units.val hl
      rw [Units.val_mul] at this
      rw [← this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have hHGL : H * A * H⁻¹ = quadGL (l : K) m hsq := Units.ext hH
    set c := conjAut (m * 2) K H with hc
    have hct : c * t * c⁻¹ = conjAut (m * 2) K (quadGL (l : K) m hsq) := by
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hHGL]
    set B' := B.map (MulAut.conj c).toMonoidHom with hB'def
    have hcore := oddCoreIn_map_conj B htB c
    rw [hct] at hcore
    have hW' : IsCyclic ↥(oddCoreIn B' (conjAut (m * 2) K (quadGL (l : K) m hsq))) := by
      have : Fact (Irreducible (quadPoly (l : K))) := ⟨quadPoly_irreducible hsq⟩
      have hmonic : (quadPoly (l : K)).Monic := Polynomial.monic_X_pow_sub_C (l : K) two_ne_zero
      have : Module.Finite K (QuadExt (l : K)) := (AdjoinRoot.powerBasis' hmonic).finite
      have : Finite (QuadExt (l : K)) := Module.finite_of_finite K
      let R : QuadExt (l : K) →+* Matrix (Fin (m * 2)) (Fin (m * 2)) K :=
        (blockRep (l : K) m).toRingHom.comp (Matrix.scalar (Fin m))
      let ψ₁ : (QuadExt (l : K))ˣ →* GL (Fin (m * 2)) K := Units.map R.toMonoidHom
      refine isCyclic_of_le_range ((conjAut (m * 2) K).comp ψ₁) fun y hy => ?_
      obtain ⟨D, x, rfl, hD⟩ := nonsplit_oddCoreIn hsq hm hinj (hconjB H) hy
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply Units.ne_zero D
        rw [hD]
        simp
      refine ⟨Units.mk0 x hx0, ?_⟩
      show conjAut (m * 2) K (ψ₁ (Units.mk0 x hx0)) = conjAut (m * 2) K D
      congr 1
      apply Units.ext
      rw [hD]
      simp [ψ₁, R]
    rw [hcore] at hW'
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (oddCoreIn B t) (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).symm.surjective

theorem oddCoreCyclic_psl {p f : ℕ} [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = p ^ f) (hn : 3 ≤ n) : OddCoreCyclic (projectiveSL n K) := by
  classical
  intro B hB t htB ht
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)) :=
    conj_injective_of_center_eq_bot (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn)
  have hψ : Function.Injective B.subtype := Subtype.val_injective
  have hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤
      B.subtype.range := by
    rw [Subgroup.range_subtype]
    exact hB
  have ht' : orderOf (⟨t, htB⟩ : ↥B) = 2 := by
    rw [← ht, ← Subgroup.orderOf_coe]
  have hbot : (∀ Y : Subgroup ↥B, Y ≤ oddCentralizerCore (⟨t, htB⟩ : ↥B) → Y = ⊥) →
      IsCyclic ↥(oddCoreIn B t) := fun h => by
    rw [oddCoreIn_eq_bot_of_forall htB h]
    infer_instance
  have hsq : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 t
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      exact psl_oddCoreIn_cyclic_inner hK hn hinj hB htB ht hα
    · exact hbot fun Y hY => field_eq_bot hp hp2 hf hKc hn hinj (ψ := B.subtype) hψ hInn ht' hσ
        hα hY
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      have hα' : t = conjAut n K A * dualAut n K := by rw [hα, map_one, mul_one]
      have hsq' : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1 := by
        rw [← hα]
        exact hsq
      rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq hn A
          hsq' with hA | hA
      · exact hbot fun Y hY => orthogonal_eq_bot hK hn hinj (ψ := B.subtype) hψ hInn
          (t := ⟨t, htB⟩) hA hα' hY
      · rw [hα']
        have := symplectic_oddCoreIn_eq_bot hK hn hinj hB hA
        rw [this]
        infer_instance
    · exact hbot fun Y hY => graphField_eq_bot hp hp2 hf hKc hn hinj (ψ := B.subtype) hψ hInn ht'
        hσ hα hY

end Psl

section NoPsl

theorem no911_psl {Y : Type} [Group Y] [Finite Y] {n p f : ℕ} (hn : 3 ≤ n) (hp2 : p ≠ 2)
    (hL : LieModel Y .PSL n p f) (hp : p.Prime) (hf : 1 ≤ f) : No911 Y := by
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  exact no911_of_mulEquiv θ (no911_of_oddCoreCyclic (oddCoreCyclic_psl hp hp2 hf hKc hn))

end NoPsl

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
