module

public import CFSG.GH74.GLS.IVK.L2.Lemma19Aut
public import CFSG.GH74.GLS.IVK.L2.Hilbert90
public import CFSG.CharacterTheory.Semidihedral.MatrixCoverData

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup Matrix CFSG CFSG.GorensteinWalter CFSG.ABGLocalTools
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL)

section L113A

variable {F : Type} [Field F] [Finite F]

theorem exists_sq_sub_eq_neg_one (hF2 : ringChar F ≠ 2) (l : F) (hl : l ≠ 0) :
    ∃ a b : F, a ^ 2 - l * b ^ 2 = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have hdeg : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_X_pow]
    rfl
  have hdeg2 : (Polynomial.C (-l) * Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial F).degree = 2 := by
    rw [Polynomial.degree_add_C (by
      rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hl)]; norm_num)]
    rw [Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hl)]
    rfl
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic
    (f := (Polynomial.X ^ 2 : Polynomial F))
    (g := (Polynomial.C (-l) * Polynomial.X ^ 2 + Polynomial.C 1)) hdeg hdeg2
    (FiniteField.odd_card_of_char_ne_two hF2)
  refine ⟨a, b, ?_⟩
  simp at h
  linear_combination h

theorem exists_anticommuting_sl (hF2 : ringChar F ≠ 2)
    (G : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hG2 : G * G = lam • (1 : Matrix (Fin 2) (Fin 2) F)) (hdet : G.det ≠ 0)
    (hns : ∀ c : F, G ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ x : SpecialLinearGroup (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F) * x = -1 ∧
      G * (x : Matrix (Fin 2) (Fin 2) F) = -((x : Matrix (Fin 2) (Fin 2) F) * G) := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F, G = !![p, q; r, s] :=
    ⟨G 0 0, G 0 1, G 1 0, G 1 1, Matrix.eta_fin_two G⟩
  simp only [Matrix.mul_fin_two] at hG2
  have e00 := congrFun (congrFun hG2 0) 0
  have e01 := congrFun (congrFun hG2 0) 1
  have e10 := congrFun (congrFun hG2 1) 0
  have e11 := congrFun (congrFun hG2 1) 1
  simp at e00 e01 e10 e11
  rw [Matrix.det_fin_two_of] at hdet
  have hps : p + s = 0 := by
    by_contra hne
    have hq : q = 0 := by
      have : q * (p + s) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hne
    have hr : r = 0 := by
      have : r * (p + s) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne
    have hpq : p = s := by
      have : (p - s) * (p + s) = 0 := by
        subst hq; subst hr; linear_combination e00 - e11
      have := (mul_eq_zero.1 this).resolve_right hne
      linear_combination this
    apply hns p
    rw [Matrix.eta_fin_two (p • (1 : Matrix (Fin 2) (Fin 2) F))]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hq, hr, hpq]
  have hs : s = -p := by linear_combination hps
  subst hs
  have hlam : lam = p ^ 2 + q * r := by linear_combination -e00
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hdet
    rw [hlam] at h0
    linear_combination -h0
  have key : ∃ a b c : F, 2 * a * p + b * r + c * q = 0 ∧ a ^ 2 + b * c = -1 := by
    by_cases hq : q = 0
    · by_cases hr : r = 0
      · exact ⟨0, 1, -1, by simp [hr, hq], by ring⟩
      · obtain ⟨a', c', h⟩ := exists_sq_sub_eq_neg_one hF2 (lam / r ^ 2)
          (div_ne_zero hlam0 (pow_ne_zero 2 hr))
        refine ⟨a' + p * c' / r, -(2 * (a' + p * c' / r) * p + c' * q) / r, c', ?_, ?_⟩
        · field_simp
          ring
        · have e : (a' + p * c' / r) ^ 2 + (-(2 * (a' + p * c' / r) * p + c' * q) / r) * c' =
              a' ^ 2 - (lam / r ^ 2) * c' ^ 2 := by
            rw [hlam]
            field_simp
            ring
          rw [e]
          exact h
    · obtain ⟨a', b', h⟩ := exists_sq_sub_eq_neg_one hF2 (lam / q ^ 2)
        (div_ne_zero hlam0 (pow_ne_zero 2 hq))
      refine ⟨a' + p * b' / q, b', -(2 * (a' + p * b' / q) * p + b' * r) / q, ?_, ?_⟩
      · field_simp
        ring
      · have e : (a' + p * b' / q) ^ 2 + b' * (-(2 * (a' + p * b' / q) * p + b' * r) / q) =
            a' ^ 2 - (lam / q ^ 2) * b' ^ 2 := by
          rw [hlam]
          field_simp
          ring
        rw [e]
        exact h
  obtain ⟨a, b, c, hlin, hquad⟩ := key
  have hdetx : (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -hquad
  refine ⟨⟨!![a, b; c, -a], hdetx⟩, ?_, ?_⟩
  · show (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, -a] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hquad
  · show (!![p, q; r, -p] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, -a] =
      -((!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) F) * !![p, q; r, -p])
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hlin

end L113A

section L113B

variable {F : Type} [Field F] [Finite F]

theorem psl2MulAutOf_slConjugation (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (c : GL (Fin 2) F) :
    psl2MulAutOf (slConjugation F c) = thetaEquiv hodd h3
      (SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk c)) := by
  rw [thetaEquiv_inl]
  ext x
  induction x using QuotientGroup.induction_on with | H b => ?_
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply]
  change Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk' _ (slConjugation F c b)) = _
  rw [QuotientGroup.mk'_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, slConjugation_toGL]
  have : Matrix.ProjectiveSpecialLinearGroup.toPGL (b : PSL2 F) =
      Matrix.ProjGenLinGroup.mk (SpecialLinearGroup.toGL b) :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_mk b
  rw [this, map_mul, map_mul, map_inv]

omit [Finite F] in
theorem orderOf_eq_four_of_sq_eq_neg_one (h2 : (2 : F) ≠ 0) (x : SpecialLinearGroup (Fin 2) F)
    (h : (x : Matrix (Fin 2) (Fin 2) F) * x = -1) : orderOf x = 4 := by
  have hx2 : ((x ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two]; exact h
  have hnot : ¬ x ^ 2 ^ 1 = 1 := by
    intro h1
    have h3 := congrArg (fun y : SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F) 0 0) h1
    simp only [pow_one] at h3
    rw [hx2] at h3
    simp at h3
    apply h2
    linear_combination -h3
  have hfin : x ^ 2 ^ (1 + 1) = 1 := by
    apply Subtype.ext
    have : x ^ 2 ^ (1 + 1) = (x ^ 2) * (x ^ 2) := by group
    rw [this, Matrix.SpecialLinearGroup.coe_mul, hx2]
    simp
  have := orderOf_eq_prime_pow (p := 2) hnot hfin
  simpa using this

theorem exists_inverted_sl_inner (hodd : Odd (Nat.card F))
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1) (hα1 : α ≠ 1)
    (G : GL (Fin 2) F)
    (hα : ∀ b, SpecialLinearGroup.toGL (α b) = G * SpecialLinearGroup.toGL b * G⁻¹) :
    ∃ x : SpecialLinearGroup (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F) * x = -1 ∧ α x = x⁻¹ := by
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have hcomm : ∀ b : SpecialLinearGroup (Fin 2) F,
      ((G * G : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) =
        (b : Matrix (Fin 2) (Fin 2) F) * ((G * G : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro b
    have e0 : α (α b) = b := by
      have := congrArg (fun γ : MulAut (SpecialLinearGroup (Fin 2) F) => γ b) hα2
      simpa using this
    have e1 : G * (G * SpecialLinearGroup.toGL b * G⁻¹) * G⁻¹ = SpecialLinearGroup.toGL b := by
      rw [← hα, ← hα, e0]
    have e2 : (G * G) * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL b * (G * G) := by
      calc (G * G) * SpecialLinearGroup.toGL b
          = (G * (G * SpecialLinearGroup.toGL b * G⁻¹) * G⁻¹) * (G * G) := by group
        _ = SpecialLinearGroup.toGL b * (G * G) := by rw [e1]
    exact congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) e2
  obtain ⟨lam, hlam⟩ := exists_smul_one_of_commute_sl _ hcomm
  have hlam' : (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
      lam • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul]; exact hlam
  have hns : ∀ c : F, (G : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
    intro c hc
    apply hα1
    apply MulEquiv.ext
    intro b
    apply SpecialLinearGroup.toGL_injective
    rw [hα]
    have hcm : G * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL b * G := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hc]
      simp
    rw [hcm]
    group
    rfl
  have hdet : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 G.isUnit).ne_zero
  obtain ⟨x, hx2, hanti⟩ := exists_anticommuting_sl hF2 (G : Matrix (Fin 2) (Fin 2) F) lam hlam'
    hdet hns
  refine ⟨x, hx2, ?_⟩
  have hαx : ((α x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hα x)
    simpa using this
  have hGinv : (G : Matrix (Fin 2) (Fin 2) F) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmul : α x * x = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hαx]
    have h1 : (G : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -(x : Matrix (Fin 2) (Fin 2) F) := by
      rw [hanti, Matrix.neg_mul, Matrix.mul_assoc, hGinv, Matrix.mul_one]
    rw [h1, Matrix.neg_mul, hx2]
    simp
  exact eq_inv_of_mul_eq_one_left hmul

theorem exists_inverted_sl_field (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1) (γ : PGammaL2 F)
    (hγ : thetaEquiv hodd h3 γ = psl2MulAutOf α) (hσ : γ.right ≠ 1) :
    ∃ x : SpecialLinearGroup (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F) * x = -1 ∧ α x = x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hγ2 : γ * γ = 1 := by
    apply (thetaEquiv hodd h3).injective
    rw [map_mul, hγ, map_one]
    have : psl2MulAutOf α * psl2MulAutOf α = psl2MulAutOf (α * α) :=
      (map_mul (psl2AutHom (F := F)) α α).symm
    rw [this, hα2]
    exact (map_one (psl2AutHom (F := F)))
  have hσσ : γ.right * γ.right = 1 := by
    have := congrArg SemidirectProduct.right hγ2
    simpa using this
  have hord : orderOf γ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hγ2) (by
    intro h; apply hσ; rw [h]; rfl)
  obtain ⟨C, hC⟩ := H90.pgammaL2_involution_conj_inr γ hord hσ
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_surjective C
  obtain ⟨σ, hσdef⟩ : ∃ σ : F ≃+* F, σ = γ.right := ⟨_, rfl⟩
  rw [← hσdef] at hC hσ hσσ
  obtain ⟨α', hα'⟩ : ∃ α' : MulAut (SpecialLinearGroup (Fin 2) F),
      α' = (slConjugation F c)⁻¹ * α * slConjugation F c := ⟨_, rfl⟩
  have hΘ : thetaEquiv hodd h3 (SemidirectProduct.inr σ) = psl2MulAutOf α' := by
    rw [← hC, map_mul, map_mul, map_inv, hγ, hα']
    show _ = (psl2AutHom (F := F)) ((slConjugation F c)⁻¹ * α * slConjugation F c)
    rw [map_mul, map_mul, map_inv]
    change _ = (psl2MulAutOf (slConjugation F c))⁻¹ * psl2MulAutOf α * psl2MulAutOf (slConjugation F c)
    rw [psl2MulAutOf_slConjugation hodd h3 c, hc]
  have hsemi := semilinear_of_pGammaL2 hodd h3 α' (SemidirectProduct.inr σ) hΘ 1 (by simp)
  simp only [SemidirectProduct.right_inr] at hsemi
  obtain ⟨y, hy⟩ : ∃ y : F, σ y ≠ y := by
    by_contra h
    push Not at h
    exact hσ (RingEquiv.ext h)
  set ε : F := y - σ y with hε
  have hσσ' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : F ≃+* F => τ z) hσσ
    simpa using this
  have hσε : σ ε = -ε := by
    rw [hε, map_sub, hσσ']; ring
  have hε0 : ε ≠ 0 := by
    intro h0
    apply hy
    rw [hε] at h0
    linear_combination -h0
  have hdet0 : (!![0, -ε⁻¹; ε, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Matrix.det_fin_two_of]
    field_simp
    ring
  set x₀ : SpecialLinearGroup (Fin 2) F := ⟨!![0, -ε⁻¹; ε, 0], hdet0⟩ with hx₀
  have hx₀sq : (x₀ : Matrix (Fin 2) (Fin 2) F) * x₀ = -1 := by
    show (!![0, -ε⁻¹; ε, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -ε⁻¹; ε, 0] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε0]
  have hα'x₀ : α' x₀ = x₀⁻¹ := by
    have h1 := hsemi x₀
    have h2 : ((α' x₀ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -(x₀ : Matrix (Fin 2) (Fin 2) F) := by
      have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
      simp only [one_mul, inv_one, mul_one] at this
      rw [show ((SpecialLinearGroup.toGL (α' x₀) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (α' x₀ : Matrix (Fin 2) (Fin 2) F) from rfl] at this
      rw [this]
      show (Matrix.map (!![0, -ε⁻¹; ε, 0] : Matrix (Fin 2) (Fin 2) F) σ) = -(!![0, -ε⁻¹; ε, 0])
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hσε, map_inv₀]
    have hmul : α' x₀ * x₀ = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.neg_mul, hx₀sq]
      simp
    exact eq_inv_of_mul_eq_one_left hmul
  refine ⟨slConjugation F c x₀, ?_, ?_⟩
  · have h1 : ((slConjugation F c x₀ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (c : Matrix (Fin 2) (Fin 2) F) * (x₀ : Matrix (Fin 2) (Fin 2) F) *
          ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (slConjugation_toGL F c x₀)
      simpa using this
    have hcc : ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hcc' : (c : Matrix (Fin 2) (Fin 2) F) * ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1]
    calc (c : Matrix (Fin 2) (Fin 2) F) * (x₀ : Matrix (Fin 2) (Fin 2) F) *
          ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((c : Matrix (Fin 2) (Fin 2) F) * (x₀ : Matrix (Fin 2) (Fin 2) F) *
            ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
        = (c : Matrix (Fin 2) (Fin 2) F) * ((x₀ : Matrix (Fin 2) (Fin 2) F) *
            (((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F)) *
              (x₀ : Matrix (Fin 2) (Fin 2) F)) * ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [hcc, Matrix.mul_one, hx₀sq, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hcc']
  · have hαeq : α = slConjugation F c * α' * (slConjugation F c)⁻¹ := by rw [hα']; group
    rw [hαeq]
    simp [MulAut.mul_apply, hα'x₀]

end L113B

section L113C

variable {F : Type} [Field F] [Finite F]

theorem exists_inverted_sl (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ x : SpecialLinearGroup (Fin 2) F, (x : Matrix (Fin 2) (Fin 2) F) * x = -1 ∧ α x = x⁻¹ := by
  obtain ⟨γ, hγ⟩ : ∃ γ : PGammaL2 F, thetaEquiv hodd h3 γ = psl2MulAutOf α :=
    ⟨(thetaEquiv hodd h3).symm (psl2MulAutOf α), (thetaEquiv hodd h3).apply_symm_apply _⟩
  by_cases hσ : γ.right = 1
  · obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective γ.left
    have hsemi := semilinear_of_pGammaL2 hodd h3 α γ hγ G hG
    rw [hσ] at hsemi
    refine exists_inverted_sl_inner hodd α hα2 hα1 G (fun b => ?_)
    rw [hsemi b]
    congr 2
  · exact exists_inverted_sl_field hodd h3 α hα2 γ hγ hσ

theorem ivk_1_13 :
    ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) → 3 < Nat.card F →
      ∀ (Khat : Type) [Group Khat] (_ : Khat ≃* SL2 F) (a : MulAut Khat), orderOf a = 2 →
        ∃ x : Khat, orderOf x = 4 ∧ a x = x⁻¹ := by
  intro F _ _ hodd h3 Khat _ e a ha2
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  let φ : Khat ≃* SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  obtain ⟨α, hα⟩ : ∃ α : MulAut (SpecialLinearGroup (Fin 2) F), α = MulAut.congr φ a := ⟨_, rfl⟩
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, pow_two] at this
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul, haa, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    apply ha1
    apply (MulAut.congr φ).injective
    rw [← hα, h, map_one]
  obtain ⟨x, hx2, hαx⟩ := exists_inverted_sl hodd h3 α hα2 hα1
  refine ⟨φ.symm x, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_four_of_sq_eq_neg_one h2 x hx2
  · have h1 : φ (a (φ.symm x)) = x⁻¹ := by
      have := hαx
      rw [hα] at this
      simpa [MulAut.congr_apply] using this
    apply φ.injective
    rw [h1, map_inv, MulEquiv.apply_symm_apply]

end L113C

end CFSG.GH74.GLS.IVK
