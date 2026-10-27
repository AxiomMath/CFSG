module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.LieType.Chevalley CFSG.ClassicalInvolution.G2D4Models CFSG.ClassicalInvolution.Generic
  Matrix
open scoped MatrixGroups

section Trace

variable {F : Type} [Field F]

@[expose] def traceSL (x : F) : SL2 F := ⟨!![x, -1; 1, 0], by simp [det_fin_two]⟩

theorem trace_glConjSL (D : GL (Fin 2) F) (A : SL2 F) :
    trace ((glConjSL D A : SL2 F) : Matrix (Fin 2) (Fin 2) F) =
      trace (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [glConjSL_coe, trace_mul_cycle, gl_inv_mul, one_mul]

theorem eq_of_glConjSL_map_eq {D : GL (Fin 2) F} {δ : F →+* F}
    (h : ∀ A : SL2 F, glConjSL D (SpecialLinearGroup.map δ A) = A) (x : F) : δ x = x := by
  have h1 := congrArg (fun A : SL2 F => trace (A : Matrix (Fin 2) (Fin 2) F)) (h (traceSL x))
  simp only [trace_glConjSL, SpecialLinearGroup.map_apply_coe] at h1
  simpa [traceSL, trace_fin_two] using h1

theorem map_neg_one_SL2 (δ : F →+* F) : SpecialLinearGroup.map δ (-1 : SL2 F) = -1 := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_neg]

theorem eq_of_fixes_conjSub {C : Type*} [Group C] (Φ : SL2 F →* C) (hΦ : Function.Injective Φ)
    (β : MulAut C) (δ : F →+* F) (hβΦ : ∀ A, β (Φ A) = Φ (SpecialLinearGroup.map δ A))
    (hlin : ∀ c : C, c * Φ (-1) = Φ (-1) * c → LinAct Φ c) (g h : C)
    (hfix : ∀ x ∈ conjSub h Φ.range, g * β x * g⁻¹ = x) (x : F) : δ x = x := by
  set c := h⁻¹ * (g * β h) with hc
  have key : ∀ A, c * Φ (SpecialLinearGroup.map δ A) * c⁻¹ = Φ A := by
    intro A
    have hx := hfix (h * Φ A * h⁻¹) ⟨Φ A, ⟨A, rfl⟩, rfl⟩
    rw [map_mul, map_mul, map_inv, hβΦ] at hx
    calc c * Φ (SpecialLinearGroup.map δ A) * c⁻¹ =
          h⁻¹ * (g * (β h * Φ (SpecialLinearGroup.map δ A) * (β h)⁻¹) * g⁻¹) * h := by
            rw [hc]; group
      _ = Φ A := by rw [hx]; group
  have hcz : c * Φ (-1) = Φ (-1) * c := by
    have h1 := key (-1)
    rw [map_neg_one_SL2] at h1
    calc c * Φ (-1) = c * Φ (-1) * c⁻¹ * c := by group
      _ = Φ (-1) * c := by rw [h1]
  obtain ⟨D, hD⟩ := hlin c hcz
  exact eq_of_glConjSL_map_eq (D := D) (fun A => hΦ (by rw [← hD, key])) x

end Trace

section Field

variable {K : Type} [Field K]

theorem ringEquiv_pow_apply_of_fixed {δ : K ≃+* K} {c : K} (hc : δ c = c) (m : ℕ) :
    (δ ^ m) c = c := by
  induction m with
  | zero => rw [pow_zero, RingAut.one_apply]
  | succ m ih => rw [pow_succ', RingAut.mul_apply, ih, hc]

theorem eq_one_of_fixes_subfield [Finite K] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ (3 * e)) (S : Subfield K) (hS : Nat.card S = p ^ e)
    (hSp : ∀ c ∈ S, c ^ (p ^ e) = c) {δ : K ≃+* K} {n : ℕ} (hδn : δ ^ (2 ^ n) = 1)
    (hfix : ∀ c ∈ S, δ c = c) : δ = 1 := by
  by_contra hδ1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hδn)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    refine ⟨k - 1, ?_⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, h0, pow_zero])) hδ1
    · omega
  have hε2 : (δ ^ (2 ^ j)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, ← hk, pow_orderOf_eq_one]
  have hε1 : δ ^ (2 ^ j) ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hk] at h'
    exact absurd ((Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h') (by omega)
  obtain ⟨hev, hεc, -⟩ := ringEquiv_sq_eq_one_facts hp (by omega) hK hε2 hε1
  obtain ⟨a, ha⟩ : ∃ a, e = 2 * a := by
    rcases Nat.even_mul.mp hev with h3 | ⟨a, ha⟩
    · exact absurd h3 (by decide)
    · exact ⟨a, by omega⟩
  have hSa : ∀ c ∈ S, c ^ (p ^ a) = c := by
    intro c hc
    have h1 : c ^ (p ^ (3 * e / 2)) = c := by
      rw [← hεc]
      exact ringEquiv_pow_apply_of_fixed (hfix c hc) _
    have h2 : c ^ (p ^ (2 * a)) = c := ha ▸ hSp c hc
    rwa [show 3 * e / 2 = 2 * a + a by omega, pow_add, pow_mul, h2] at h1
  have hS' : Nat.card S = p ^ (2 * a) := by rw [hS, ha]
  obtain ⟨φ, hφ, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega) hS'
  have hφa : φ ^ a = 1 := RingEquiv.ext fun x => by
    rw [ringAut_pow_apply_of_frobenius hφ, RingAut.one_apply]
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hSa x x.2)
  have h' := orderOf_dvd_of_pow_eq_one hφa
  rw [hord] at h'
  exact absurd (Nat.le_of_dvd (by omega) h') (by omega)

end Field

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
