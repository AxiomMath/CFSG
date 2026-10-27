module

public import CFSG.GH74.Generic.Front.SpNFDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy

public section

namespace CFSG.GH74.Generic

open Module Matrix

section SpNFb

variable {F : Type} [Field F]

private theorem tensorNF_of_basis (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (p q : Fin 2 → Fin 2 ⊕ Fin 2 → F) (a G : Matrix (Fin 2) (Fin 2) F)
    (hG : IsUnit G.det) (hGs : ∀ i j, G j i = G i j)
    (hp : ∀ j, A *ᵥ p j = ∑ i, a i j • p i) (hq : ∀ j, A *ᵥ q j = ∑ i, a i j • q i)
    (hpp : ∀ i j, sp2Form (p i) (p j) = 0) (hqq : ∀ i j, sp2Form (q i) (q j) = 0)
    (hpq : ∀ i j, sp2Form (p i) (q j) = G i j) : TensorNF A := by
  classical
  have hqp : ∀ i j, sp2Form (q i) (p j) = -G i j := fun i j => by
    rw [sp2Form_comm, hpq, hGs]
  have hgram : (sp2ColMat p q)ᵀ * sp2Gram F * sp2ColMat p q = fromBlocks 0 G (-G) 0 := by
    ext x y
    rw [sp2_gram_apply]
    rcases x with i | i <;> rcases y with j | j
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inl, hpp]
      simp
    · rw [sp2ColMat_mulVec_inl, sp2ColMat_mulVec_inr, hpq]
      simp
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inl, hqp]
      simp
    · rw [sp2ColMat_mulVec_inr, sp2ColMat_mulVec_inr, hqq]
      simp
  refine ⟨sp2ColMat p q, a, G, ?_, ?_, hgram⟩
  · have hG2 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    have hT : (fromBlocks 0 (-G⁻¹) G⁻¹ 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        fromBlocks 0 G (-G) 0 = 1 := by
      rw [fromBlocks_multiply]
      simp [hG2, ← fromBlocks_one]
    have hinv : ((fromBlocks 0 (-G⁻¹) G⁻¹ 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((sp2ColMat p q)ᵀ * sp2Gram F)) * sp2ColMat p q = 1 := by
      rw [Matrix.mul_assoc, hgram, hT]
    exact isUnit_det_of_left_inverse hinv
  · ext x y
    rcases y with j | j
    · have h := congrFun (hp j) x
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp [Matrix.mul_apply, Fintype.sum_sum_type, sp2ColMat, h, mul_comm]
    · have h := congrFun (hq j) x
      simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      simp [Matrix.mul_apply, Fintype.sum_sum_type, sp2ColMat, h, mul_comm]

private theorem sp2Form_mulVec_similitude {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {μ : F}
    (hs : Aᵀ * sp2Gram F * A = μ • sp2Gram F) (a b : Fin 2 ⊕ Fin 2 → F) :
    sp2Form (A *ᵥ a) (A *ᵥ b) = μ * sp2Form a b := by
  have h1 : ∀ x : Fin 2 ⊕ Fin 2 → F, (A *ᵥ a) ⬝ᵥ x = a ⬝ᵥ (Aᵀ *ᵥ x) := by
    intro x
    rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [sp2Form, h1, mulVec_mulVec, mulVec_mulVec, hs, smul_mulVec, dotProduct_smul, smul_eq_mul]

private theorem sp2Form_adj {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {c μ : F}
    (hAA : A * A = c • 1) (hs : Aᵀ * sp2Gram F * A = μ • sp2Gram F) (u v : Fin 2 ⊕ Fin 2 → F) :
    c * sp2Form (A *ᵥ u) v = μ * sp2Form u (A *ᵥ v) := by
  have h := sp2Form_mulVec_similitude hs u (A *ᵥ v)
  rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec, sp2Form_smul_right] at h
  exact h

private theorem sp2Form_add_left' (x y v : Fin 2 ⊕ Fin 2 → F) :
    sp2Form (x + y) v = sp2Form x v + sp2Form y v := by
  simp [sp2Form, add_dotProduct]

private theorem sp2Form_smul_left' (c : F) (u v : Fin 2 ⊕ Fin 2 → F) :
    sp2Form (c • u) v = c * sp2Form u v := by
  simp [sp2Form, smul_dotProduct]

private theorem odd_natCard_of_two_ne_zero [Finite F] (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have hc : CharP F 2 := ringChar.eq_iff.1 h
    exact_mod_cast CharP.cast_eq_zero F 2
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hchar)

private theorem exists_isotropic_skew [Finite F] (h2 : (2 : F) ≠ 0)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (l : F) (hl0 : l ≠ 0) (hAA : A * A = l • 1)
    (hsymm : ∀ u v, sp2Form (A *ᵥ v) u = sp2Form (A *ᵥ u) v) :
    ∃ e : Fin 2 ⊕ Fin 2 → F, e ≠ 0 ∧ sp2Form (A *ᵥ e) e = 0 := by
  classical
  let β : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F) →ₗ[F] F :=
    LinearMap.mk₂ F (fun u v => sp2Form (A *ᵥ u) v)
      (fun x y v => by simp [sp2Form, mulVec_add, add_dotProduct])
      (fun c x v => by simp [sp2Form, mulVec_smul, smul_dotProduct])
      (fun x y z => sp2Form_add_right (A *ᵥ x) y z)
      (fun c x y => sp2Form_smul_right c (A *ᵥ x) y)
  let Q : QuadraticForm F (Fin 2 ⊕ Fin 2 → F) := LinearMap.BilinMap.toQuadraticMap β
  have hQ : ∀ v, Q v = sp2Form (A *ᵥ v) v := fun v => by
    simp [Q, β, LinearMap.BilinMap.toQuadraticMap_apply]
  have hpolar : ∀ x y, Q.polarBilin x y = 2 * sp2Form (A *ᵥ x) y := fun x y => by
    rw [QuadraticMap.polarBilin_apply_apply, LinearMap.BilinMap.polar_toQuadraticMap]
    show sp2Form (A *ᵥ x) y + sp2Form (A *ᵥ y) x = _
    rw [hsymm x y, two_mul]
  have hsepL : ∀ x : Fin 2 ⊕ Fin 2 → F, (∀ y, Q.polarBilin x y = 0) → x = 0 := by
    intro x hx
    have h1 : ∀ y, sp2Form (A *ᵥ x) y = 0 := fun y => by
      have := hx y
      rw [hpolar] at this
      exact (mul_eq_zero.1 this).resolve_left h2
    have h3 : A *ᵥ x = 0 := eq_zero_of_sp2Form_right h1
    have h4 : l • x = 0 := by
      rw [← one_mulVec x, ← smul_mulVec, ← hAA, ← mulVec_mulVec, h3, mulVec_zero]
    exact (smul_eq_zero.1 h4).resolve_left hl0
  have hnd : Q.polarBilin.Nondegenerate :=
    ⟨hsepL, fun y hy => hsepL y fun x => by rw [QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm, ← QuadraticMap.polarBilin_apply_apply]; exact hy x⟩
  have hfin : 3 ≤ Module.finrank F (Fin 2 ⊕ Fin 2 → F) := by simp
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.exists_isotropic_of_three_le
      (odd_natCard_of_two_ne_zero h2) Q hnd hfin
  exact ⟨v, hv0, by rw [← hQ]; exact hv⟩

end SpNFb

theorem tensorNF_nonsplit_minus {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (l : F) (hl : ¬ IsSquare l)
    (hAA : A * A = l • 1) (hAJ : Aᵀ * sp2Gram F * A = (-l) • sp2Gram F) : TensorNF A := by
  classical
  have hl0 : l ≠ 0 := fun h => hl ⟨0, by rw [h, mul_zero]⟩
  have hA2 : ∀ v, A *ᵥ (A *ᵥ v) = l • v := fun v => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hAA' : ∀ u v, sp2Form (A *ᵥ u) (A *ᵥ v) = (-l) * sp2Form u v :=
    sp2Form_mulVec_similitude hAJ
  have hadj : ∀ u v, sp2Form (A *ᵥ u) v = -sp2Form u (A *ᵥ v) := fun u v => by
    have h := sp2Form_adj hAA hAJ u v
    apply mul_left_cancel₀ hl0
    linear_combination h
  have hsymm : ∀ u v, sp2Form (A *ᵥ v) u = sp2Form (A *ᵥ u) v := fun u v =>
    (sp2Form_comm u (A *ᵥ v)).trans (hadj u v).symm
  obtain ⟨e, he0, heQ⟩ := exists_isotropic_skew h2 A l hl0 hAA hsymm
  have heAe : sp2Form e (A *ᵥ e) = 0 := by
    have h := hadj e e
    rw [heQ] at h
    exact neg_eq_zero.1 h.symm
  have hee : sp2Form e e = 0 := sp2Form_self h2 e
  have hAeAe : sp2Form (A *ᵥ e) (A *ᵥ e) = 0 := by rw [hAA', hee, mul_zero]
  obtain ⟨g, hgA, hge⟩ : ∃ g, sp2Form (A *ᵥ e) g = 0 ∧ sp2Form e g = 1 := by
    obtain ⟨v, hv⟩ : ∃ v, sp2Form e v ≠ 0 := by
      by_contra hcon
      exact he0 (eq_zero_of_sp2Form_right fun w => by_contra fun hw => hcon ⟨w, hw⟩)
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, sp2Form e g₀ = 1 :=
      ⟨(sp2Form e v)⁻¹ • v, by rw [sp2Form_smul_right, inv_mul_cancel₀ hv]⟩
    obtain ⟨s, hs⟩ : ∃ s, s = sp2Form (A *ᵥ e) g₀ := ⟨_, rfl⟩
    have hsA : sp2Form e (A *ᵥ g₀) = -s := by
      have h := hadj e g₀
      rw [← hs] at h
      linear_combination h
    have hAAg : sp2Form (A *ᵥ e) (A *ᵥ g₀) = -l := by rw [hAA', hg₀]; ring
    have hd : 1 - s * (s / l) ≠ 0 := by
      intro h
      apply hl
      refine ⟨s, ?_⟩
      field_simp at h
      linear_combination h
    refine ⟨(1 - s * (s / l))⁻¹ • (g₀ + (s / l) • (A *ᵥ g₀)), ?_, ?_⟩
    · rw [sp2Form_smul_right, sp2Form_add_right, sp2Form_smul_right, hAAg, ← hs]
      have : s + s / l * -l = 0 := by field_simp; ring
      rw [this, mul_zero]
    · rw [sp2Form_smul_right, sp2Form_add_right, sp2Form_smul_right, hsA, hg₀]
      have : 1 + s / l * -s = 1 - s * (s / l) := by ring
      rw [this, inv_mul_cancel₀ hd]
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ = sp2Form (A *ᵥ g) g := ⟨_, rfl⟩
  obtain ⟨t, htl⟩ : ∃ t : F, 2 * l * t = -q₀ :=
    ⟨-q₀ / (2 * l), by field_simp⟩
  obtain ⟨f, hf⟩ : ∃ f, f = g + t • (A *ᵥ e) := ⟨_, rfl⟩
  have hAf : A *ᵥ f = A *ᵥ g + (t * l) • e := by
    rw [hf, mulVec_add, mulVec_smul, hA2, smul_smul]
  have hef : sp2Form e f = 1 := by
    rw [hf, sp2Form_add_right, sp2Form_smul_right, heAe, hge]; ring
  have hAef : sp2Form (A *ᵥ e) f = 0 := by
    rw [hf, sp2Form_add_right, sp2Form_smul_right, hgA, hAeAe]; ring
  have hAgAe : sp2Form (A *ᵥ g) (A *ᵥ e) = l := by
    rw [hAA', sp2Form_comm e g, hge]; ring
  have hQf : sp2Form (A *ᵥ f) f = 0 := by
    have h1 : sp2Form (A *ᵥ f) f = sp2Form (A *ᵥ g) g + t * sp2Form (A *ᵥ g) (A *ᵥ e) +
        (t * l) * sp2Form e g + (t * l) * (t * sp2Form e (A *ᵥ e)) := by
      rw [hAf, hf, sp2Form_add_left', sp2Form_smul_left', sp2Form_add_right, sp2Form_add_right,
        sp2Form_smul_right, sp2Form_smul_right]
      ring
    rw [h1, ← hq₀, hAgAe, hge, heAe]
    linear_combination htl
  have hpair : ∀ u : Fin 2 ⊕ Fin 2 → F, sp2Form (A *ᵥ u) u = 0 →
      ∀ i j, sp2Form (![u, A *ᵥ u] i) (![u, A *ᵥ u] j) = 0 := by
    intro u hu i j
    have hu' : sp2Form u (A *ᵥ u) = 0 := by
      have h := hadj u u
      rw [hu] at h
      exact neg_eq_zero.1 h.symm
    fin_cases i <;> fin_cases j
    · exact sp2Form_self h2 u
    · exact hu'
    · exact hu
    · show sp2Form (A *ᵥ u) (A *ᵥ u) = 0
      rw [hAA', sp2Form_self h2, mul_zero]
  have hact : ∀ u : Fin 2 ⊕ Fin 2 → F, ∀ j, A *ᵥ (![u, A *ᵥ u] j) =
      ∑ i, (!![0, l; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j • ![u, A *ᵥ u] i := by
    intro u j
    fin_cases j
    · simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two, hA2]
  refine tensorNF_of_basis A ![e, A *ᵥ e] ![f, A *ᵥ f] !![0, l; 1, 0] !![1, 0; 0, -l] ?_ ?_
    (hact e) (hact f) (hpair e heQ) (hpair f hQf) ?_
  · rw [Matrix.det_fin_two_of]
    exact isUnit_iff_ne_zero.2 (by simpa using hl0)
  · simp [Fin.forall_fin_two]
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hef
    · show sp2Form e (A *ᵥ f) = 0
      have h := hadj e f
      rw [hAef] at h
      exact neg_eq_zero.1 h.symm
    · exact hAef
    · show sp2Form (A *ᵥ e) (A *ᵥ f) = -l
      rw [hAA', hef, mul_one]

end CFSG.GH74.Generic
