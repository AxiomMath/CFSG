module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412f
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk0

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups

section SmulMulVec

variable {K : Type} [Field K]

@[expose] def smulMulVec (H : SL(2, K)) (l : K) : (Fin 2 → K) →+ (Fin 2 → K) where
  toFun v := l • (H : Matrix (Fin 2) (Fin 2) K).mulVec v
  map_zero' := by simp
  map_add' v w := by simp only [Matrix.mulVec_add, smul_add]

theorem smulMulVec_apply (H : SL(2, K)) (l : K) (v : Fin 2 → K) :
    smulMulVec H l v = l • (H : Matrix (Fin 2) (Fin 2) K).mulVec v := rfl

theorem smulMulVec_injective (H : SL(2, K)) {l : K} (hl : l ≠ 0) :
    Function.Injective (smulMulVec H l) := by
  intro v w hvw
  have h1 : l • (H : Matrix (Fin 2) (Fin 2) K).mulVec v = l • (H : Matrix (Fin 2) (Fin 2) K).mulVec w :=
    hvw
  have h2 := congrArg (fun x => ((H⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (l⁻¹ • x)) h1
  simp only [smul_smul, inv_mul_cancel₀ hl, one_smul, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec] at h2
  exact h2

theorem smulMulVec_surjective (H : SL(2, K)) {l : K} (hl : l ≠ 0) :
    Function.Surjective (smulMulVec H l) := by
  intro w
  refine ⟨((H⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (l⁻¹ • w), ?_⟩
  rw [smulMulVec_apply, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hl, one_smul]

theorem conj_mulVec (H a : SL(2, K)) (w : Fin 2 → K) :
    ((H * a * H⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec
        ((H : Matrix (Fin 2) (Fin 2) K).mulVec w) =
      (H : Matrix (Fin 2) (Fin 2) K).mulVec ((a : Matrix (Fin 2) (Fin 2) K).mulVec w) := by
  have e : H * a * H⁻¹ * H = H * a := by group
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, e]

end SmulMulVec

section Conj

variable {G : Type} [Group G] {L P : Subgroup G} {n : ℕ} {K : Type} [Field K] [Fintype K]

@[expose] noncomputable def Adapted.conj (A : Adapted L P n K) (H : SL(2, K))
    (hH : (H : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {l : K} (hl : l ≠ 0) : Adapted L P n K where
  P_le := A.P_le
  card_eq := A.card_eq
  α := (MulAut.conj H).toMonoidHom.comp A.α
  α_surj := (MulAut.conj H).surjective.comp A.α_surj
  α_ker := by
    rw [MonoidHom.ker_comp_of_injective A.α (MulAut.conj H).toMonoidHom
      (MulAut.conj H).injective, A.α_ker]
  β := (AddMonoidHom.toMultiplicative (smulMulVec H l)).comp A.β
  β_surj := by
    rw [MonoidHom.coe_comp]
    refine Function.Surjective.comp ?_ A.β_surj
    intro y
    obtain ⟨w, hw⟩ := smulMulVec_surjective H hl (Multiplicative.toAdd y)
    exact ⟨Multiplicative.ofAdd w, Multiplicative.toAdd.injective hw⟩
  β_ker := by
    have hinj : Function.Injective (AddMonoidHom.toMultiplicative (smulMulVec H l)) := by
      intro a b hab
      exact Multiplicative.toAdd.injective
        (smulMulVec_injective H hl (congrArg Multiplicative.toAdd hab))
    rw [MonoidHom.ker_comp_of_injective A.β _ hinj, A.β_ker]
  β_equiv := by
    intro ℓ u v hv
    have h1 := A.β_equiv ℓ u v hv
    show smulMulVec H l (Multiplicative.toAdd (A.β v)) =
      ((MulAut.conj H (A.α ℓ) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec
        (smulMulVec H l (Multiplicative.toAdd (A.β u)))
    rw [h1, smulMulVec_apply, smulMulVec_apply, Matrix.mulVec_smul, MulAut.conj_apply,
      conj_mulVec]
  mem_P := by
    intro ℓ
    have hHn : H ∈ Subgroup.normalizer (slUni K : Set SL(2, K)) := mem_normalizer_slUni_iff.2 hH
    exact (A.mem_P ℓ).trans (Subgroup.mem_normalizer_iff.1 hHn (A.α ℓ))

theorem Adapted.conj_α (A : Adapted L P n K) (H : SL(2, K))
    (hH : (H : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {l : K} (hl : l ≠ 0) (ℓ : L) :
    (A.conj H hH hl).α ℓ = H * A.α ℓ * H⁻¹ := rfl

theorem Adapted.conj_β (A : Adapted L P n K) (H : SL(2, K))
    (hH : (H : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) {l : K} (hl : l ≠ 0) (u : blockU L) :
    Multiplicative.toAdd ((A.conj H hH hl).β u) =
      l • (H : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (A.β u)) := rfl

end Conj

section Normalized

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.exists_normalized (h : Lin2Cfg G T M H S L n D)
    (hQL : pCoreOf 2 L = pCoreOf 2 H) {F : Subgroup G} (hF2 : IsPGroup 2 F) (hFL : F ⊓ L = ⊥)
    (hHF : H = L ⊔ F) {K : Type} [Field K] [Fintype K] {R : Subgroup G} (A : Adapted L R n K)
    (hOL : pCoreOf 2 L = blockU L) {f : G} (hf : f ∈ F) (hf1 : f ≠ 1) (hff : f * f = 1)
    (hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L) (hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L)
    (hfR : ∀ x ∈ R, f * x * f⁻¹ ∈ R) :
    ∃ (A' : Adapted L R n K) (σ : K ≃+* K), σ ≠ 1 ∧ (∀ v, σ (σ v) = v) ∧
      (∀ ℓ : L, A'.α ⟨f * ℓ * f⁻¹, hfL ℓ ℓ.2⟩ =
        Matrix.SpecialLinearGroup.map σ.toRingHom (A'.α ℓ)) ∧
      (∀ u : blockU L, Multiplicative.toAdd (A'.β ⟨f * u * f⁻¹, hfU u u.2⟩) =
        fun i => σ (Multiplicative.toAdd (A'.β u) i)) := by
  obtain ⟨σ, a, c', ha, hσσ, hc3, -, hc1, -, -, -, -, ⟨Gm, hG10, hG00, hGb, hGα, hGβ⟩, hσ1⟩ :=
    h.link A hOL hff hfL hfU hfR
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card h.one_pos A.card_eq
  have hσ : σ ≠ 1 := by
    intro hσ1'
    obtain ⟨k, hk⟩ := hσ1 hσ1'
    exact hf1 (h.eq_one_of_inner hQL hF2 hFL hHF A hf hfL k hk)
  obtain ⟨⟨θ, hθ⟩, -⟩ := exists_half_of_twisted hK2 A.card_eq σ hσσ hσ
  have hKcard : 1 < Nat.card K := by
    rw [Nat.card_eq_fintype_card, A.card_eq]
    exact Nat.one_lt_pow (by have := h.one_pos; omega) (by norm_num)
  have haσ : a * σ a = 1 := by
    have h1 : (a * σ a) ^ 2 = 1 := by
      have := hc3
      rw [map_mul] at this
      linear_combination this
    have h0 : (a * σ a - 1) ^ 2 = 0 := by
      linear_combination h1 - (a * σ a) * hK2 + hK2
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  have hcc : c' * σ c' = 1 := by
    have h1 := hc1
    rw [map_mul] at h1
    calc c' * σ c' = c' * σ c' * (a * σ a) := by rw [haσ, mul_one]
      _ = c' * a * (σ c' * σ a) := by ring
      _ = 1 := h1
  obtain ⟨hh, k, l, hh0, hl0, hσh, hσk, hσl⟩ :=
    hilbert90_package hK2 σ hσσ θ hθ hKcard ha haσ hGb hcc
  have hG11 : (Gm : Matrix (Fin 2) (Fin 2) K) 1 1 = a⁻¹ := by
    have := Gm.det_coe
    rw [Matrix.det_fin_two, hG10, hG00] at this
    exact eq_inv_of_mul_eq_one_right (by simpa using this)
  obtain ⟨Hm, hHm00, hHm01, hHm10, hHm11⟩ : ∃ Hm : SL(2, K),
      (Hm : Matrix (Fin 2) (Fin 2) K) 0 0 = hh ∧ (Hm : Matrix (Fin 2) (Fin 2) K) 0 1 = k ∧
      (Hm : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (Hm : Matrix (Fin 2) (Fin 2) K) 1 1 = hh⁻¹ :=
    ⟨⟨!![hh, k; 0, hh⁻¹], by simp [Matrix.det_fin_two, hh0]⟩, rfl, rfl, rfl, rfl⟩
  have hHG : Matrix.SpecialLinearGroup.map σ.toRingHom Hm = Hm * Gm := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hHm00, hHm01, hHm10, hHm11, hG10, hG00, hG11,
        hσh, hσk]
    ring
  refine ⟨A.conj Hm hHm10 hl0, σ, hσ, hσσ, fun ℓ => ?_, fun u => ?_⟩
  · rw [Adapted.conj_α, Adapted.conj_α]
    have e := eq_mul_inv_of_mul_eq (hGα ℓ)
    rw [e, map_mul, map_mul, map_inv, hHG]
    group
  · rw [Adapted.conj_β, Adapted.conj_β, hGβ]
    ext i
    fin_cases i
    · simp [hHm00, hHm01, hHm10, hHm11, hG10, hG00, hG11, hσh, hσk, hσl]
      ring
    · simp [hHm00, hHm01, hHm10, hHm11, hG10, hG00, hG11, hσh, hσl]
      ring

end Normalized

end CFSG.QuasithinUnique.Lin2
