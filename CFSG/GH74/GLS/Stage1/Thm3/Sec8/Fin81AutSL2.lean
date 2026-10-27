module

public import CFSG.GH74.GLS.LU.Local.SL2Sylow
public import CFSG.GH74.GLS.Stage1.Main.BrG2AutA

public section

open Matrix CFSG.GH74.GLS.LU.Local.SL2 CFSG.Semidihedral.OddFieldSL2
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_matrix)

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

section Core

variable {F : Type} [Field F]

def q8T (A B A' B' X : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  X - A' * X * A - B' * X * B - A' * B' * X * (A * B)

theorem q8T_mul_A (A B A' B' X : Matrix (Fin 2) (Fin 2) F)
    (hA : A * A = -1) (hBA : B * A = -(A * B)) (hA' : A' * A' = -1) :
    q8T A B A' B' X * A = A' * q8T A B A' B' X := by
  have e : q8T A B A' B' X * A - A' * q8T A B A' B' X =
      (A' * A' + 1) * X * A - A' * X * (A * A + 1) - A' * B' * X * A * (B * A + A * B)
        + A' * B' * X * (A * A + 1) * B - B' * X * (B * A + A * B) + (A' * A' + 1) * B' * X * (A * B) := by
    unfold q8T
    noncomm_ring
  have h1 : A' * A' + 1 = 0 := by rw [hA']; simp
  have h2 : A * A + 1 = 0 := by rw [hA]; simp
  have h3 : B * A + A * B = 0 := by rw [hBA]; simp
  rw [h1, h2, h3] at e
  simp at e
  exact sub_eq_zero.1 e

theorem q8T_mul_B (A B A' B' X : Matrix (Fin 2) (Fin 2) F)
    (hB : B * B = -1) (hB' : B' * B' = -1) (hBA' : B' * A' = -(A' * B')) :
    q8T A B A' B' X * B = B' * q8T A B A' B' X := by
  have e : q8T A B A' B' X * B - B' * q8T A B A' B' X =
      -(B' * X * (B * B + 1)) + (B' * B' + 1) * X * B - A' * B' * X * A * (B * B + 1)
        + (B' * A' + A' * B') * X * A + (B' * A' + A' * B') * B' * X * (A * B)
        - A' * (B' * B' + 1) * X * (A * B) := by
    unfold q8T
    noncomm_ring
  have h1 : B * B + 1 = 0 := by rw [hB]; simp
  have h2 : B' * B' + 1 = 0 := by rw [hB']; simp
  have h3 : B' * A' + A' * B' = 0 := by rw [hBA']; simp
  rw [h1, h2, h3] at e
  simp at e
  exact sub_eq_zero.1 e


theorem sum_sandwich (P Q : Matrix (Fin 2) (Fin 2) F) :
    ∑ i : Fin 2, ∑ j : Fin 2, (P * Matrix.single i j (1 : F) * Q) i j = P.trace * Q.trace := by
  simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.single_apply, Matrix.trace, Matrix.diag_apply]
  ring

theorem trace_eq_zero_of_sq (M : Matrix (Fin 2) (Fin 2) F) (hd : M.det = 1) (hM : M * M = -1) :
    M.trace = 0 := by
  rw [Matrix.trace_fin_two]
  exact trace_zero_of_sq M hd hM

theorem exists_q8T_ne_zero (h2 : (2 : F) ≠ 0) (A B A' B' : Matrix (Fin 2) (Fin 2) F)
    (hAt : A.trace = 0) (hBt : B.trace = 0) (hABt : (A * B).trace = 0)
    (hAt' : A'.trace = 0) (hBt' : B'.trace = 0) (hABt' : (A' * B').trace = 0) :
    ∃ i j : Fin 2, q8T A B A' B' (Matrix.single i j (1 : F)) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hsum : ∑ i : Fin 2, ∑ j : Fin 2, (q8T A B A' B' (Matrix.single i j (1 : F))) i j = 4 := by
    simp only [q8T, Matrix.sub_apply, Finset.sum_sub_distrib, sum_sandwich, hAt, hBt, hABt, hAt', hBt', hABt']
    simp
    norm_num
  have h0 : ∑ i : Fin 2, ∑ j : Fin 2, (q8T A B A' B' (Matrix.single i j (1 : F))) i j = 0 := by
    simp [hall]
  rw [h0] at hsum
  have h4 : (4 : F) = 2 * 2 := by norm_num
  rw [h4] at hsum
  exact mul_ne_zero h2 h2 hsum.symm


theorem exists_smul_of_mulVec_eq_zero (G : Matrix (Fin 2) (Fin 2) F) (hG : G ≠ 0) (u v : Fin 2 → F)
    (hu : u ≠ 0) (hGu : G *ᵥ u = 0) (hGv : G *ᵥ v = 0) : ∃ c : F, v = c • u := by
  by_cases hD : u 0 * v 1 - u 1 * v 0 = 0
  · by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro h1
        apply hu
        ext i
        fin_cases i
        · exact h0
        · exact h1
      refine ⟨v 1 / u 1, ?_⟩
      have hv0 : v 0 = 0 := by
        rw [h0, zero_mul, zero_sub, neg_eq_zero] at hD
        exact (mul_eq_zero.1 hD).resolve_left h1
      ext i
      fin_cases i
      · simp [hv0, h0]
      · simp [h1]
    · refine ⟨v 0 / u 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · simp
        field_simp
        linear_combination hD
  · exfalso
    apply hG
    have e1 := congrFun hGu 0
    have e2 := congrFun hGu 1
    have e3 := congrFun hGv 0
    have e4 := congrFun hGv 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2 e3 e4
    have h00 : G 0 0 = 0 := by
      have : G 0 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * e1 - u 1 * e3
      exact (mul_eq_zero.1 this).resolve_right hD
    have h01 : G 0 1 = 0 := by
      have : G 0 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * e3 - v 0 * e1
      exact (mul_eq_zero.1 this).resolve_right hD
    have h10 : G 1 0 = 0 := by
      have : G 1 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * e2 - u 1 * e4
      exact (mul_eq_zero.1 this).resolve_right hD
    have h11 : G 1 1 = 0 := by
      have : G 1 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * e4 - v 0 * e2
      exact (mul_eq_zero.1 this).resolve_right hD
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem no_common_eigenvector (h2 : (2 : F) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) F) (hA : A * A = -1)
    (hB : B * B = -1) (hBA : B * A = -(A * B)) (u : Fin 2 → F) (hu : u ≠ 0) (a b : F)
    (hAu : A *ᵥ u = a • u) (hBu : B *ᵥ u = b • u) : False := by
  have hab : (2 * (a * b)) • u = 0 := by
    have h1 : A *ᵥ (B *ᵥ u) = (b * a) • u := by
      rw [hBu, Matrix.mulVec_smul, hAu, smul_smul]
    have h2' : B *ᵥ (A *ᵥ u) = (a * b) • u := by
      rw [hAu, Matrix.mulVec_smul, hBu, smul_smul]
    have h3 : B *ᵥ (A *ᵥ u) = -(A *ᵥ (B *ᵥ u)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.neg_mulVec]
    rw [h1, h2'] at h3
    rw [mul_comm b a] at h3
    have : (a * b) • u + (a * b) • u = 0 := eq_neg_iff_add_eq_zero.1 h3
    rw [← two_smul F, ← mul_smul] at this
    rw [← this]
  have hab' : 2 * (a * b) = 0 := (smul_eq_zero.1 hab).resolve_right hu
  have ha0 : a ≠ 0 := by
    intro ha
    have h1 : (A * A) *ᵥ u = -u := by rw [hA, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hAu, Matrix.mulVec_smul, hAu, smul_smul, ha] at h1
    simp at h1
    exact hu (by simpa using h1)
  have hb0 : b ≠ 0 := by
    intro hb
    have h1 : (B * B) *ᵥ u = -u := by rw [hB, Matrix.neg_mulVec, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hBu, Matrix.mulVec_smul, hBu, smul_smul, hb] at h1
    simp at h1
    exact hu (by simpa using h1)
  exact mul_ne_zero h2 (mul_ne_zero ha0 hb0) hab'


theorem exists_intertwiner (h2 : (2 : F) ≠ 0) (A B A' B' : Matrix (Fin 2) (Fin 2) F)
    (hAd : A.det = 1) (hBd : B.det = 1) (hA'd : A'.det = 1) (hB'd : B'.det = 1)
    (hA : A * A = -1) (hB : B * B = -1) (hBA : B * A = -(A * B))
    (hA' : A' * A' = -1) (hB' : B' * B' = -1) (hBA' : B' * A' = -(A' * B')) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det ≠ 0 ∧ g * A = A' * g ∧ g * B = B' * g := by
  have hABsq : A * B * (A * B) = -1 := by
    calc A * B * (A * B) = A * (B * A) * B := by noncomm_ring
      _ = A * (-(A * B)) * B := by rw [hBA]
      _ = -((A * A) * (B * B)) := by noncomm_ring
      _ = -1 := by rw [hA, hB]; simp
  have hBA'sq : A' * B' * (A' * B') = -1 := by
    calc A' * B' * (A' * B') = A' * (B' * A') * B' := by noncomm_ring
      _ = A' * (-(A' * B')) * B' := by rw [hBA']
      _ = -((A' * A') * (B' * B')) := by noncomm_ring
      _ = -1 := by rw [hA', hB']; simp
  obtain ⟨i, j, hij⟩ := exists_q8T_ne_zero h2 A B A' B'
    (trace_eq_zero_of_sq A hAd hA) (trace_eq_zero_of_sq B hBd hB)
    (trace_eq_zero_of_sq (A * B) (by rw [Matrix.det_mul, hAd, hBd, one_mul]) hABsq)
    (trace_eq_zero_of_sq A' hA'd hA') (trace_eq_zero_of_sq B' hB'd hB')
    (trace_eq_zero_of_sq (A' * B') (by rw [Matrix.det_mul, hA'd, hB'd, one_mul]) hBA'sq)
  set g := q8T A B A' B' (Matrix.single i j (1 : F)) with hg
  have hgA : g * A = A' * g := q8T_mul_A A B A' B' _ hA hBA hA'
  have hgB : g * B = B' * g := q8T_mul_B A B A' B' _ hB hB' hBA'
  refine ⟨g, ?_, hgA, hgB⟩
  intro hdet
  obtain ⟨v, hv, hgv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hAv : g *ᵥ (A *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hgA, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_zero]
  have hBv : g *ᵥ (B *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hgB, ← Matrix.mulVec_mulVec, hgv, Matrix.mulVec_zero]
  obtain ⟨a, ha⟩ := exists_smul_of_mulVec_eq_zero g hij v (A *ᵥ v) hv hgv hAv
  obtain ⟨b, hb⟩ := exists_smul_of_mulVec_eq_zero g hij v (B *ᵥ v) hv hgv hBv
  exact no_common_eigenvector h2 A B hA hB hBA v hv a b ha hb


theorem matrix_rel_of_sl (α β : SpecialLinearGroup (Fin 2) F) (hαα : α * α = minusIdentity F)
    (hββ : β * β = minusIdentity F) (hβα : β * α = α * β * minusIdentity F) :
    (α : Matrix (Fin 2) (Fin 2) F) * α = -1 ∧ (β : Matrix (Fin 2) (Fin 2) F) * β = -1 ∧
      (β : Matrix (Fin 2) (Fin 2) F) * α = -((α : Matrix (Fin 2) (Fin 2) F) * β) := by
  have hneg : ((minusIdentity F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hαα
    simpa [hneg] using this
  · have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hββ
    simpa [hneg] using this
  · have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hβα
    simpa [hneg] using this

theorem exists_aut_of_quaternion_pair (h2 : (2 : F) ≠ 0) (α β α' β' : SpecialLinearGroup (Fin 2) F)
    (hαα : α * α = minusIdentity F) (hββ : β * β = minusIdentity F)
    (hβα : β * α = α * β * minusIdentity F) (hαα' : α' * α' = minusIdentity F)
    (hββ' : β' * β' = minusIdentity F) (hβα' : β' * α' = α' * β' * minusIdentity F) :
    ∃ γ : MulAut (SpecialLinearGroup (Fin 2) F), γ α = α' ∧ γ β = β' := by
  obtain ⟨hA, hB, hBA⟩ := matrix_rel_of_sl α β hαα hββ hβα
  obtain ⟨hA', hB', hBA'⟩ := matrix_rel_of_sl α' β' hαα' hββ' hβα'
  obtain ⟨g, hgdet, hgA, hgB⟩ := exists_intertwiner h2 (α : Matrix (Fin 2) (Fin 2) F) β α' β'
    (Matrix.SpecialLinearGroup.det_coe α) (Matrix.SpecialLinearGroup.det_coe β)
    (Matrix.SpecialLinearGroup.det_coe α') (Matrix.SpecialLinearGroup.det_coe β') hA hB hBA hA' hB' hBA'
  let G : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero g hgdet
  have hGinv : (g * g⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 :=
    Matrix.mul_nonsing_inv g (isUnit_iff_ne_zero.2 hgdet)
  have hconj : ∀ (X X' : SpecialLinearGroup (Fin 2) F),
      g * (X : Matrix (Fin 2) (Fin 2) F) = (X' : Matrix (Fin 2) (Fin 2) F) * g →
        slConjugation F G X = X' := by
    intro X X' h
    apply Subtype.ext
    rw [slConjugation_matrix]
    have hG1 : (G : Matrix (Fin 2) (Fin 2) F) = g := rfl
    have hG2 : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = g⁻¹ := by
      simp [G, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [hG1, hG2, h, Matrix.mul_assoc, hGinv, Matrix.mul_one]
  exact ⟨slConjugation F G, hconj α α' hgA, hconj β β' hgB⟩

end Core

section Sylow

variable {F : Type} [Field F] [Finite F]

theorem exists_sylow_eq_of_isSylowOf {P : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) :
    ∃ Q : Sylow 2 (SpecialLinearGroup (Fin 2) F), (Q : Subgroup (SpecialLinearGroup (Fin 2) F)) = P := by
  have hcard : Nat.card P = 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 := by
    have := hP.card_eq
    rwa [Subgroup.card_top] at this
  exact ⟨Sylow.ofCard P hcard, Sylow.coe_ofCard P hcard⟩

theorem factorization_two_card_sl2 (q : ℕ) (h : q % 8 = 3 ∨ q % 8 = 5) :
    (q * (q ^ 2 - 1)).factorization 2 = 3 := by
  obtain ⟨m, hm, hq⟩ : ∃ m, Odd m ∧ q * (q ^ 2 - 1) = 8 * m := by
    rcases h with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
      have e : (8 * k + 3) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 1)) := by
        have : (8 * k + 3) ^ 2 = 64 * k ^ 2 + 48 * k + 9 := by ring
        have h2 : 8 * ((2 * k + 1) * (4 * k + 1)) = 64 * k ^ 2 + 48 * k + 8 := by ring
        omega
      refine ⟨(8 * k + 3) * ((2 * k + 1) * (4 * k + 1)), ?_, ?_⟩
      · have o1 : Odd (8 * k + 3) := ⟨4 * k + 1, by ring⟩
        have o2 : Odd (2 * k + 1) := ⟨k, rfl⟩
        have o3 : Odd (4 * k + 1) := ⟨2 * k, by ring⟩
        exact o1.mul (o2.mul o3)
      · rw [e]; ring
    · obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 5 := ⟨q / 8, by omega⟩
      have e : (8 * k + 5) ^ 2 - 1 = 8 * ((2 * k + 1) * (4 * k + 3)) := by
        have : (8 * k + 5) ^ 2 = 64 * k ^ 2 + 80 * k + 25 := by ring
        have h2 : 8 * ((2 * k + 1) * (4 * k + 3)) = 64 * k ^ 2 + 80 * k + 24 := by ring
        omega
      refine ⟨(8 * k + 5) * ((2 * k + 1) * (4 * k + 3)), ?_, ?_⟩
      · have o1 : Odd (8 * k + 5) := ⟨4 * k + 2, by ring⟩
        have o2 : Odd (2 * k + 1) := ⟨k, rfl⟩
        have o3 : Odd (4 * k + 3) := ⟨2 * k + 1, by ring⟩
        exact o1.mul (o2.mul o3)
      · rw [e]; ring
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [hq, Nat.factorization_mul (by norm_num) hm0]
  have h8 : (Nat.factorization 8) 2 = 3 := by
    have : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [this, Nat.Prime.factorization_pow Nat.prime_two]; simp
  have : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro hd; exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd))
  simp [this, h8]

theorem nonempty_equiv_q8_of_sylow (hodd : Odd (Nat.card F)) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (Q : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    Nonempty (↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup 2) := by
  obtain ⟨f, hf⟩ := exists_quaternion_embedding_in_sylow F hodd Q
  have hQcard : Nat.card ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)) = 8 := by
    rw [Sylow.card_eq_multiplicity, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      factorization_two_card_sl2 _ hmod]
    norm_num
  have hQ8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hQcard, hQ8])
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end Sylow



section Main

variable {F : Type} [Field F] [Finite F]

theorem exists_aut_extending_sylow (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {P P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) (hP' : CFSG.ABGLocalTools.IsSylowOf 2 P' ⊤) (β : ↥P ≃* ↥P') :
    ∃ γ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ x : ↥P, γ (x : Matrix.SpecialLinearGroup (Fin 2) F) =
        ((β x : ↥P') : Matrix.SpecialLinearGroup (Fin 2) F) := by
  have _h5 : 5 ≤ Nat.card F := h5
  have _hP' := hP'
  have h2 := two_ne_zero_of_odd_card F hodd
  obtain ⟨Q, rfl⟩ := exists_sylow_eq_of_isSylowOf hP
  obtain ⟨φ⟩ := nonempty_equiv_q8_of_sylow hodd hmod Q
  obtain ⟨α, b, hα, hb, hαα, hbb, hbα, hgen⟩ := q8_gens h2 Q φ
  have hzQ : minusIdentity F ∈ (Q : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    rw [← hαα]; exact Subgroup.mul_mem _ hα hα
  have hz : ((β ⟨minusIdentity F, hzQ⟩ : ↥P') : SpecialLinearGroup (Fin 2) F) = minusIdentity F := by
    apply (orderOf_eq_two_iff F h2 _).mp
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact minusIdentity_orderOf F h2
  have hmul : ∀ x y : ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)),
      ((β x : ↥P') : SpecialLinearGroup (Fin 2) F) * ((β y : ↥P') : SpecialLinearGroup (Fin 2) F) =
        ((β (x * y) : ↥P') : SpecialLinearGroup (Fin 2) F) := by
    intro x y
    rw [map_mul]
    rfl
  set a₀ : ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)) := ⟨α, hα⟩ with ha₀
  set b₀ : ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)) := ⟨b, hb⟩ with hb₀
  set z₀ : ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)) := ⟨minusIdentity F, hzQ⟩ with hz₀
  have e1 : a₀ * a₀ = z₀ := Subtype.ext hαα
  have e2 : b₀ * b₀ = z₀ := Subtype.ext hbb
  have e3 : b₀ * a₀ = a₀ * b₀ * z₀ := Subtype.ext hbα
  obtain ⟨γ, hγα, hγb⟩ := exists_aut_of_quaternion_pair h2 α b
    ((β a₀ : ↥P') : SpecialLinearGroup (Fin 2) F) ((β b₀ : ↥P') : SpecialLinearGroup (Fin 2) F)
    hαα hbb hbα
    (by rw [hmul, e1]; exact hz)
    (by rw [hmul, e2]; exact hz)
    (by rw [← hz]; simp only [hmul]; rw [e3])
  have key : ∀ x ∈ Subgroup.closure ({α, b} : Set (SpecialLinearGroup (Fin 2) F)),
      ∃ hx : x ∈ (Q : Subgroup (SpecialLinearGroup (Fin 2) F)),
        γ x = ((β ⟨x, hx⟩ : ↥P') : SpecialLinearGroup (Fin 2) F) := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ hx : x ∈ (Q : Subgroup (SpecialLinearGroup (Fin 2) F)),
      γ x = ((β ⟨x, hx⟩ : ↥P') : SpecialLinearGroup (Fin 2) F)) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with h | h
      · rw [h]
        exact ⟨hα, hγα⟩
      · have h' : y = b := h
        rw [h']
        exact ⟨hb, hγb⟩
    · refine ⟨(Q : Subgroup (SpecialLinearGroup (Fin 2) F)).one_mem, ?_⟩
      have h1 : (⟨1, (Q : Subgroup (SpecialLinearGroup (Fin 2) F)).one_mem⟩ :
          ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F))) = 1 := rfl
      rw [h1, map_one, map_one]
      rfl
    · intro y z _ _ ⟨hyQ, hγy⟩ ⟨hzQ', hγz⟩
      refine ⟨(Q : Subgroup (SpecialLinearGroup (Fin 2) F)).mul_mem hyQ hzQ', ?_⟩
      rw [map_mul, hγy, hγz, hmul]
      rfl
    · intro y _ ⟨hyQ, hγy⟩
      refine ⟨(Q : Subgroup (SpecialLinearGroup (Fin 2) F)).inv_mem hyQ, ?_⟩
      rw [map_inv, hγy]
      have h1 : (⟨y⁻¹, (Q : Subgroup (SpecialLinearGroup (Fin 2) F)).inv_mem hyQ⟩ :
          ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F))) =
          (⟨y, hyQ⟩ : ↥(Q : Subgroup (SpecialLinearGroup (Fin 2) F)))⁻¹ := rfl
      rw [h1, map_inv]
      rfl
  refine ⟨γ, fun x => ?_⟩
  obtain ⟨hx, hγ⟩ := key x.1 (hgen x.1 x.2)
  exact hγ

end Main

section Fixing

variable {F : Type} [Field F] [Finite F]

theorem centralizer_sylow_le_center (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤)
    {x : Matrix.SpecialLinearGroup (Fin 2) F} (hx : ∀ y ∈ P, x * y = y * x) :
    x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have _h5 : 5 ≤ Nat.card F := h5
  have _hmod := hmod
  obtain ⟨Q, rfl⟩ := exists_sylow_eq_of_isSylowOf hP
  exact cent_sylow_le_center hodd Q hx

theorem odd_orderOf_of_fixing_sylow (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤)
    (γ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (hfix : ∀ x ∈ P, γ x = x) :
    Odd (orderOf γ) := by
  have h3 : 3 < Nat.card F := by omega
  obtain ⟨Q, rfl⟩ := exists_sylow_eq_of_isSylowOf hP
  have hn : orderOf γ ≠ 0 := (orderOf_pos γ).ne'
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hmpos : 0 < m := hm.pos
  have h2pow : ∃ j : ℕ, (γ ^ m) ^ (2 ^ j) = 1 := by
    refine ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, ← hnm]
    exact pow_orderOf_eq_one γ
  have hR := CFSG.GH74.GLS.Stage1.Main.field_part_trivial_small hodd h3 hmod (γ ^ m) h2pow
  obtain ⟨G, hG⟩ := CFSG.GH74.GLS.IVK.Lifted.eq_slConjugation_of_right_eq_one hodd h3 (γ ^ m) hR
  have hfixm : ∀ j : ℕ, ∀ x ∈ (Q : Subgroup (SpecialLinearGroup (Fin 2) F)), (γ ^ j) x = x := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      rw [pow_succ, MulAut.mul_apply, hfix x hx, ih x hx]
  have hone : γ ^ m = 1 := by
    by_contra hne
    have hne' : slConjugation F G ≠ 1 := hG ▸ hne
    obtain ⟨α, b, hα, hb, hαα, hbb, hbα⟩ := exists_anticomm_pair hodd Q
    have hfa : α ∈ CFSG.GH74.GLS.fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G) := by
      show (slConjugation F G) α = α
      rw [← hG]
      exact hfixm m α hα
    have hfb : b ∈ CFSG.GH74.GLS.fixedSubgroup (SpecialLinearGroup (Fin 2) F) (slConjugation F G) := by
      show (slConjugation F G) b = b
      rw [← hG]
      exact hfixm m b hb
    have hcomm := CFSG.GH74.GLS.IVK.Lifted.fixed_comm_of_slConjugation G hne' α hfa b hfb
    have h1 : α * b = α * b * minusIdentity F := by
      calc α * b = b * α := hcomm
        _ = α * b * minusIdentity F := hbα
    have h2 : minusIdentity F = 1 := by
      have h1' : (α * b) * (1 : SpecialLinearGroup (Fin 2) F) = (α * b) * minusIdentity F := by
        rw [mul_one]; exact h1
      exact (mul_left_cancel h1').symm
    exact minusIdentity_ne_one F (two_ne_zero_of_odd_card F hodd) h2
  have hdvd : orderOf γ ∣ m := orderOf_dvd_of_pow_eq_one hone
  have hk : k = 0 := by
    have h1 : 2 ^ k * m ∣ 1 * m := by rw [one_mul, ← hnm]; exact hdvd
    have h2 : 2 ^ k ∣ 1 := Nat.dvd_of_mul_dvd_mul_right hmpos h1
    have h3 : 2 ^ k = 1 := Nat.dvd_one.1 h2
    exact Nat.pow_eq_one.1 h3 |>.resolve_left (by norm_num)
  rw [hnm, hk, pow_zero, one_mul]
  exact hm

end Fixing

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
