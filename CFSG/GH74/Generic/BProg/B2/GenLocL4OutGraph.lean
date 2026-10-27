module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def IsInnerDiag4 (φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) : Prop :=
  ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
    ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

theorem eq_one_of_mul_self [Finite F] (hF4 : Nat.card F % 4 = 3) (σ : F ≃+* F) (hσ : σ * σ = 1) : σ = 1 := by
  by_contra h1
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ) h1
  have hcard := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hord] at hcard
  set r := Nat.card ↥(CFSG.GH74.GLS.IVK.fixedField σ) with hr
  have hodd : r % 2 = 1 := by
    by_contra h
    have : r % 2 = 0 := by omega
    have h4 : (r ^ 2) % 4 = 0 := by
      obtain ⟨k, hk⟩ : 2 ∣ r := Nat.dvd_of_mod_eq_zero this
      rw [hk]; ring_nf; omega
    omega
  have : (r ^ 2) % 4 = 1 := by
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := ⟨r / 2, by omega⟩
    rw [hk]; ring_nf; omega
  omega

theorem sq_eq_one_of_conj (σ : F ≃+* F) (M : Matrix (Fin 4) (Fin 4) F) (hM : M ≠ 0)
    (h : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      M * (g : Matrix (Fin 4) (Fin 4) F).map (σ * σ) = (g : Matrix (Fin 4) (Fin 4) F) * M) :
    σ * σ = 1 := by
  have hs : M ∈ Set.range (Matrix.scalar (Fin 4) : F → Matrix (Fin 4) (Fin 4) F) := by
    refine Matrix.mem_range_scalar_of_commute_single (fun i j hij => ?_)
    have h1 := h (Matrix.SpecialLinearGroup.transvection hij 1)
    rw [CFSG.LinearGroups.coe_transvection hij 1, Matrix.map_add _ (fun a b => map_add (σ * σ) a b), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_single _ _ _ (σ * σ), map_one, mul_add, add_mul, mul_one, one_mul] at h1
    exact (add_right_injective _ h1 : _).symm
  obtain ⟨l, hl⟩ := hs
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hM
    rw [← hl]; ext a b; simp
  ext t
  have h1 := h (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) t)
  rw [CFSG.LinearGroups.coe_transvection _ t, Matrix.map_add _ (fun a b => map_add (σ * σ) a b), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_single _ _ _ (σ * σ), ← hl] at h1
  have h2 := congrFun (congrFun h1 0) 1
  simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, Fin.sum_univ_four] at h2
  have h3 : l * (σ * σ) t = l * t := by simpa [mul_comm] using h2
  exact mul_left_cancel₀ hl0 h3

theorem sigma_one_of_linear [Finite F] (hF4 : Nat.card F % 4 = 3) (u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hu : ∀ g, u (u g) = g) (A : GL (Fin 4) F) (σ : F ≃+* F)
    (hA : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F, ((u g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map σ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    σ = 1 := by
  set φ : Matrix (Fin 4) (Fin 4) F →+* Matrix (Fin 4) (Fin 4) F := (σ : F →+* F).mapMatrix with hφ
  have hmap : ∀ X : Matrix (Fin 4) (Fin 4) F, X.map σ = φ X := fun X => rfl
  set Am : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAm
  set Ai : Matrix (Fin 4) (Fin 4) F := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hAi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hφAi : φ Ai * φ Am = 1 := by rw [← map_mul, hAiA, map_one]
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (Am * φ Am) * (g : Matrix (Fin 4) (Fin 4) F).map (σ * σ) = (g : Matrix (Fin 4) (Fin 4) F) * (Am * φ Am) := by
    intro g
    have h1 := hA (u g)
    rw [hu g, hA g] at h1
    have h2 : (g : Matrix (Fin 4) (Fin 4) F).map (σ * σ) = φ (φ (g : Matrix (Fin 4) (Fin 4) F)) := by
      rw [← hmap, ← hmap, Matrix.map_map]; rfl
    rw [h2]
    simp only [hmap, map_mul] at h1
    calc (Am * φ Am) * φ (φ (g : Matrix (Fin 4) (Fin 4) F))
        = (Am * (φ Am * φ (φ (g : Matrix (Fin 4) (Fin 4) F)) * φ Ai) * Ai) * (Am * φ Am) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Ai Am, hAiA, Matrix.one_mul, hφAi, Matrix.mul_one]
      _ = (g : Matrix (Fin 4) (Fin 4) F) * (Am * φ Am) := by rw [← h1]
  have hM0 : Am * φ Am ≠ 0 := by
    intro h0
    have : (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
      calc (1 : Matrix (Fin 4) (Fin 4) F) = Am * φ (Am * Ai) * Ai := by rw [hAAi, map_one, Matrix.mul_one, hAAi]
        _ = (Am * φ Am) * φ Ai * Ai := by rw [map_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h0]; simp
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
  exact eq_one_of_mul_self hF4 σ (sq_eq_one_of_conj σ (Am * φ Am) hM0 key)


theorem sigma_one_of_graph [Finite F] (hF4 : Nat.card F % 4 = 3) (u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hu : ∀ g, u (u g) = g) (A : GL (Fin 4) F) (σ : F ≃+* F)
    (hA : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F, ((u g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose.map σ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :
    σ = 1 := by
  set φ : Matrix (Fin 4) (Fin 4) F →+* Matrix (Fin 4) (Fin 4) F := (σ : F →+* F).mapMatrix with hφ
  have hmap : ∀ X : Matrix (Fin 4) (Fin 4) F, X.map σ = φ X := fun X => rfl
  set Am : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAm
  set Ai : Matrix (Fin 4) (Fin 4) F := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hAi
  have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hT : Ai.transpose * Am.transpose = 1 := by rw [← Matrix.transpose_mul, hAAi, Matrix.transpose_one]
  have hT' : Am.transpose * Ai.transpose = 1 := by rw [← Matrix.transpose_mul, hAiA, Matrix.transpose_one]
  have hφT : φ Ai.transpose * φ Am.transpose = 1 := by rw [← map_mul, hT, map_one]
  have hφT' : φ Am.transpose * φ Ai.transpose = 1 := by rw [← map_mul, hT', map_one]
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (Am * φ Ai.transpose) * (g : Matrix (Fin 4) (Fin 4) F).map (σ * σ) =
        (g : Matrix (Fin 4) (Fin 4) F) * (Am * φ Ai.transpose) := by
    intro g
    have h1 := hA (u g)
    have hinv : (u g)⁻¹ = u g⁻¹ := (map_inv u g).symm
    rw [hu g, hinv, hA (g⁻¹), inv_inv] at h1
    simp only [hmap, Matrix.transpose_mul, map_mul] at h1
    have h2 : (g : Matrix (Fin 4) (Fin 4) F).map (σ * σ) = φ (φ (g : Matrix (Fin 4) (Fin 4) F)) := by
      rw [← hmap, ← hmap, Matrix.map_map]; rfl
    rw [h2]
    have htr : ∀ X : Matrix (Fin 4) (Fin 4) F, (φ X).transpose = φ X.transpose := fun X => by
      rw [← hmap, ← hmap, Matrix.transpose_map]
    simp only [htr, Matrix.transpose_transpose] at h1
    calc Am * φ Ai.transpose * φ (φ (g : Matrix (Fin 4) (Fin 4) F))
        = (Am * (φ Ai.transpose * (φ (φ (g : Matrix (Fin 4) (Fin 4) F)) * φ Am.transpose)) * Ai) *
            (Am * φ Ai.transpose) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Ai Am, hAiA, Matrix.one_mul]
          rw [hφT', Matrix.mul_one]
      _ = (g : Matrix (Fin 4) (Fin 4) F) * (Am * φ Ai.transpose) := by rw [← h1]
  have hM0 : Am * φ Ai.transpose ≠ 0 := by
    intro h0
    have : (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by
      calc (1 : Matrix (Fin 4) (Fin 4) F) = Am * φ (Ai.transpose * Am.transpose) * Ai := by
            rw [hT, map_one, Matrix.mul_one, hAAi]
        _ = (Am * φ Ai.transpose) * φ Am.transpose * Ai := by rw [map_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [h0]; simp
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
  exact eq_one_of_mul_self hF4 σ (sq_eq_one_of_conj σ (Am * φ Ai.transpose) hM0 key)


theorem exists_graph_form [Finite F] (hF4 : Nat.card F % 4 = 3) (u : MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hu : u * u = 1) (hn : ¬ IsInnerDiag4 u) :
    ∃ B : GL (Fin 4) F, (∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ((u g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (B : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose *
            ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ∧
      ((B : Matrix (Fin 4) (Fin 4) F).transpose = B ∨
        (B : Matrix (Fin 4) (Fin 4) F).transpose = -(B : Matrix (Fin 4) (Fin 4) F)) := by
  have hu' : ∀ g, u (u g) = g := fun g => by
    have := congrArg (fun φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) => φ g) hu
    simpa using this
  obtain ⟨A, σ, hform⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (by norm_num : 3 ≤ 4) u
  rcases hform with h1 | h2
  · have hσ := sigma_one_of_linear hF4 u hu' A σ h1
    subst hσ
    exfalso
    apply hn
    refine ⟨A, fun g => ?_⟩
    rw [h1 g]
    simp
  · have hσ := sigma_one_of_graph hF4 u hu' A σ h2
    subst hσ
    have h2' : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ((u g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          (A : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).transpose *
            ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := fun g => by
      rw [h2 g]; simp
    refine ⟨A, h2', ?_⟩
    set Am : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAm
    set Ai : Matrix (Fin 4) (Fin 4) F := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hAi
    have hAAi : Am * Ai = 1 := by rw [hAm, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hAiA : Ai * Am = 1 := by rw [hAm, hAi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hT : Ai.transpose * Am.transpose = 1 := by rw [← Matrix.transpose_mul, hAAi, Matrix.transpose_one]
    have hT' : Am.transpose * Ai.transpose = 1 := by rw [← Matrix.transpose_mul, hAiA, Matrix.transpose_one]
    have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        (g : Matrix (Fin 4) (Fin 4) F) * (Am * Ai.transpose) = (Am * Ai.transpose) * (g : Matrix (Fin 4) (Fin 4) F) := by
      intro g
      have h3 := h2' (u g)
      have hinv : (u g)⁻¹ = u g⁻¹ := (map_inv u g).symm
      rw [hu' g, hinv, h2' (g⁻¹), inv_inv] at h3
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h3
      calc (g : Matrix (Fin 4) (Fin 4) F) * (Am * Ai.transpose)
          = (Am * (Ai.transpose * ((g : Matrix (Fin 4) (Fin 4) F) * Am.transpose)) * Ai) * (Am * Ai.transpose) := by rw [← h3]
        _ = (Am * Ai.transpose) * (g : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Ai Am, hAiA, Matrix.one_mul, hT', Matrix.mul_one]
    obtain ⟨l, hl⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (fun g => hcomm g)
    have hA1 : Am = l • Am.transpose := by
      calc Am = Am * (Ai.transpose * Am.transpose) := by rw [hT, Matrix.mul_one]
        _ = (Am * Ai.transpose) * Am.transpose := by rw [Matrix.mul_assoc]
        _ = l • Am.transpose := by rw [hl, smul_mul_assoc, Matrix.one_mul]
    have hA2 : Am.transpose = l • Am := by
      have := congrArg Matrix.transpose hA1
      rwa [Matrix.transpose_smul, Matrix.transpose_transpose] at this
    have hA0 : Am ≠ 0 := by
      intro h0
      have : (1 : Matrix (Fin 4) (Fin 4) F) = 0 := by rw [← hAAi, h0, Matrix.zero_mul]
      have h00 := congrFun (congrFun this 0) 0
      simp at h00
    have hll : l * l = 1 := by
      have h3 : Am = (l * l) • Am := by
        calc Am = l • Am.transpose := hA1
          _ = l • (l • Am) := by rw [hA2]
          _ = (l * l) • Am := by rw [smul_smul]
      by_contra hne
      apply hA0
      have h4 : (l * l - 1) • Am = 0 := by rw [sub_smul, one_smul, ← h3]; simp
      rcases smul_eq_zero.1 h4 with h5 | h5
      · exact absurd (sub_eq_zero.1 h5) hne
      · exact h5
    rcases mul_self_eq_one_iff.1 hll with h | h
    · left; rw [hA2, h, one_smul]
    · right; rw [hA2, h, neg_smul, one_smul]

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
