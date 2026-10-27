module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenSyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Fix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1

section U3

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem u3_aut_eq_one_of_fix (hp : p ≠ 2) {z : MulAut (hypPSU h 1 1)}
    (hcop : Nat.Coprime (orderOf z) p)
    (hfix : ∀ g : hypSU h 1 1, g ∈ hypUnitriangular h 1 1 →
      z (hypProj h 1 1 g) = hypProj h 1 1 g) : z = 1 := by
  classical
  have hpp : p.Prime := h.prime
  have : Fact p.Prime := ⟨hpp⟩
  have : Finite K := h.finite
  have : CharP K p := h.charP
  obtain ⟨x₀, hx₀⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp (by norm_num) z
  set A : GL (HypIndex 1 1) K := (x₀ : SemiGL (HypIndex 1 1) K).left with hA
  set σ : K ≃+* K := (x₀ : SemiGL (HypIndex 1 1) K).right with hσ
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  have hcentral : ∀ β : K, β + h.bar β = 0 → β ≠ 0 →
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inl 0) = 0 ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inl 0) = 0 ∧
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    intro β hβ hβ0
    obtain ⟨g, hg, hgM⟩ := exists_mem_of_uMat (h := h) (α := 0) (β := β) (by simpa using hβ)
    have hfix' := hfix g hg
    rw [← hx₀] at hfix'
    have heq := u3_fix_matrix_eq hg hgM hfix'
    rw [map_zero] at heq
    obtain ⟨h1, h2, h3, -⟩ :=
      u3_fix_entries_central hβ0 (fun h0 => hβ0 (σ.injective (by rw [h0, map_zero]))) heq
    exact ⟨h1, h2, h3⟩
  obtain ⟨β₀, hβ₀E, hβ₀0⟩ := exists_mem_traceZero_ne_zero' h
  have hβ₀ : β₀ + h.bar β₀ = 0 := hβ₀E
  obtain ⟨hwe, hfe, hfw⟩ := hcentral β₀ hβ₀ hβ₀0
  have hAtri : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos :=
    u3_blockTriangular_of_hyp3 hwe hfe hfw
  have hAee : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) ≠ 0 :=
    u3_diag_ne_zero_of_blockTriangular hAtri _
  have hAff : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) ≠ 0 :=
    u3_diag_ne_zero_of_blockTriangular hAtri _
  have hreg : ∀ α : K, α ≠ 0 →
      σ α * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) =
        α * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) ∧
      h.bar (σ α) * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) =
        h.bar α * (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) := by
    intro α hα
    have hβ : (-(2 : K)⁻¹ * (α * h.bar α)) + h.bar (-(2 : K)⁻¹ * (α * h.bar α)) =
        -(α * h.bar α) := by
      rw [map_mul, map_mul, map_neg, map_inv₀, map_ofNat, h.bar_bar]
      field_simp
      ring
    obtain ⟨g, hg, hgM⟩ := exists_mem_of_uMat (h := h) hβ
    have hfix' := hfix g hg
    rw [← hx₀] at hfix'
    have heq := u3_fix_matrix_eq hg hgM hfix'
    obtain ⟨-, -, -, hrw, hrf⟩ := u3_fix_entries_regular hα heq
    exact ⟨hrw, hrf⟩
  obtain ⟨hee1, hff1⟩ := hreg 1 one_ne_zero
  have hee_ww : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) =
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) := by
    have h1 := hee1
    rw [map_one, one_mul, one_mul] at h1
    exact h1
  have hσ1 : σ = 1 := by
    apply RingEquiv.ext
    intro α
    by_cases hα : α = 0
    · rw [hα, map_zero]
      rfl
    · have h2 := (hreg α hα).1
      rw [← hee_ww] at h2
      exact mul_right_cancel₀ hAee h2
  have hσc : ∀ c, σ c = c := fun c => by rw [hσ1]; rfl
  have hbα : h.bar (1 : K) ≠ 0 := by simp
  have hww_ff : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inr (.inl 0)) =
      (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inr 0)) := by
    rw [hσc, map_one, one_mul, one_mul] at hff1
    exact hff1
  set a : K := (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inl 0) (.inl 0) with ha
  have ha0 : a ≠ 0 := hAee
  set au : Kˣ := Units.mk0 a ha0 with hau
  have hdiag : ∀ i, (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) i i = a := by
    intro i
    rcases i with i | i | i
    · rw [Subsingleton.elim i 0]
    · rw [Subsingleton.elim i 0, ← hee_ww]
    · rw [Subsingleton.elim i 0, ← hww_ff, ← hee_ww]
  set u'' : GL (HypIndex 1 1) K := GeneralLinearGroup.scalar _ au⁻¹ * A with hu''
  have hu''mat : (u'' : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      ((au⁻¹ : Kˣ) : K) • (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    rw [hu'', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hu''U : u'' ∈ fullUnitriangular 1 1 K := by
    refine ⟨?_, fun i => ?_⟩
    · intro i j hij
      rw [hu''mat, Matrix.smul_apply, hAtri hij, smul_zero]
    · rw [hu''mat, Matrix.smul_apply, hdiag i, smul_eq_mul]
      simp [hau, ha0]
  have hu''p : u'' ^ p = 1 := u3_fullUnitriangular_pow_prime hp hu''U
  have hAeq : A = GeneralLinearGroup.scalar _ au * u'' := by
    rw [hu'', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hAp : A ^ p = GeneralLinearGroup.scalar (HypIndex 1 1) (au ^ p) := by
    rw [hAeq, (commute_scalar au u'').symm.mul_pow, hu''p, mul_one, map_pow]
  have hxinl : (x₀ : SemiGL (HypIndex 1 1) K) = SemidirectProduct.inl A :=
    SemidirectProduct.ext (by simp [hA]) (by simpa using hσ1)
  have hxp : semilinearAutHom h (le_refl 1) (le_refl 1) (x₀ ^ p) = 1 := by
    refine (semilinearAutHom_eq_one_iff h (le_refl 1) (le_refl 1) (by norm_num) _).mpr
      ⟨?_, au ^ p, ?_⟩
    · rw [Subgroup.coe_pow, hxinl, ← map_pow, SemidirectProduct.right_inl]
      rfl
    · rw [Subgroup.coe_pow, hxinl, ← map_pow, SemidirectProduct.left_inl, hAp]
  have hzp : z ^ p = 1 := by
    rw [← hx₀, ← map_pow]
    exact hxp
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hzp))

theorem sylowRigid_hypPSU_three (hp : p ≠ 2) [Finite (hypPSU h 1 1)] :
    SylowRigid p (hypPSU h 1 1) := by
  have hpp : p.Prime := h.prime
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨-, -, -, -, ⟨SP, hSP⟩, -, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  refine SylowRigid.of_one SP fun z hz hcop => u3_aut_eq_one_of_fix hp hcop fun g hg => ?_
  refine hz _ ?_
  rw [hSP]
  exact ⟨g, hg, rfl⟩

end U3

section Model

open CFSG.Open

variable {q : ℕ} [Fact q.Prime]

theorem sylowRigid_of_PSU_three (hq2 : q ≠ 2) {f : ℕ} {S : Type} [Group S] [Finite S]
    (hm : StatedClassicalModel S .PSU 3 q f) : SylowRigid q S := by
  obtain ⟨⟨-, hf, -⟩, K, _, hfin, hcard, ⟨e⟩⟩ := hm
  have hh : UnitaryFieldData q f K := ⟨Fact.out, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hh
  let e' : hypPSU hh 1 1 ≃* S := (hypPSUEquivStatedProj hh hR (by norm_num)).trans e.symm
  haveI : Finite (hypPSU hh 1 1) := Finite.of_equiv S e'.symm.toEquiv
  exact (sylowRigid_hypPSU_three (h := hh) hq2).of_mulEquiv e'

end Model

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
