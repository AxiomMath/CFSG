module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoPSpUGraph
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4HBlocks4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups CFSG.ComponentClassification.CatalogueBAlternatingIsometry

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

omit h in
theorem smul_bJ (c x z : K) : c • bJ x z = bJ (c * x) (c * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bJ]

omit h in
theorem transpose_inv_of_alt {A : GL (Fin 4) K}
    (hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K)) :
    (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  have h1 : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = -1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, hAt, Matrix.transpose_one, Matrix.mul_neg] at this
    rw [← neg_neg ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (A : Matrix (Fin 4) (Fin 4) K)), this]
  calc (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ *
        ((A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
        rw [h1, Matrix.mul_one]
    _ = -(↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [← Matrix.mul_assoc, e, Matrix.neg_mul, Matrix.one_mul]

theorem dot_inv_mulVec_of_fixed {A : GL (Fin 4) K}
    (hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K)) {l : K}
    (hl0 : l ≠ 0) {v : Fin 4 → K}
    (hv : l • ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ fun i => h.bar (v i)) = v) (w : Fin 4 → K) :
    v ⬝ᵥ ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ w) = -l * stdHermForm h 4 v w := by
  have hAi : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hbar : (fun i => h.bar (v i)) = l⁻¹ • ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ v) := by
    conv_rhs => rw [← hv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hAi, Matrix.one_mulVec, smul_smul,
      inv_mul_cancel₀ hl0, one_smul]
  have e1 : stdHermForm h 4 v w = (fun i => h.bar (v i)) ⬝ᵥ w := by
    rw [stdHermForm_apply]
    rfl
  have e2 : ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ v) ⬝ᵥ w =
      -(v ⬝ᵥ ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ w)) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, transpose_inv_of_alt hAt,
      Matrix.neg_mulVec, dotProduct_neg]
  rw [e1, hbar, smul_dotProduct, smul_eq_mul, e2]
  field_simp

include h in
theorem exists_alt_frame (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1)
    (hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -(A : Matrix (Fin 4) (Fin 4) K))
    (P : GL (Fin 4) K)
    (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG) :
    ∃ (P' : GL (Fin 4) K) (_ : uStar h (P' : Matrix (Fin 4) (Fin 4) K) *
        (P' : Matrix (Fin 4) (Fin 4) K) = stdG) (y₁ : K),
      (P' : Matrix (Fin 4) (Fin 4) K).det = (P : Matrix (Fin 4) (Fin 4) K).det ∧ y₁ ≠ 0 ∧
        (P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (P' : Matrix (Fin 4) (Fin 4) K) = bJ y₁ (h.bar y₁)⁻¹ := by
  classical
  have : Finite K := h.finite
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hl
    exact one_ne_zero (by linear_combination hl : (1 : K) = 0)
  have hNl : h.norm l = -1 := norm_eq_neg_one_of_sq h hq hl
  have hbl : h.bar l = l := by
    rw [UnitaryFieldData.norm] at hNl
    have e : l * (h.bar l - l) = 0 := by linear_combination hNl - hl
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hl0)
  set τ₀ := antiunitaryMap h (A : Matrix (Fin 4) (Fin 4) K) with hτ₀
  have hμ : ∀ v, τ₀ (τ₀ v) = ((-1 : Kˣ) : K) • v := fun v => by
    rw [Units.val_neg, Units.val_one]
    exact antiunitaryMap_sq h _ (by rw [hAA, neg_one_smul]) v
  obtain ⟨-, -, ⟨t, ht⟩, hmain⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    (h.prime.odd_of_ne_two hp2) (by rw [Module.finrank_fin_fun]; norm_num)
    (stdHermForm_isSymm h 4) (stdHermForm_separatingLeft h 4) τ₀ (antiunitaryMap_bijective h A)
    (stdHermForm_antiunitaryMap h hAu) (-1) hμ
  set b : Kˣ := Units.mk0 l hl0 with hb
  have hbN : h.norm (b : K) = ((-1 : Kˣ)⁻¹ : Kˣ) := by
    rw [hb, Units.val_mk0, hNl, inv_neg, inv_one, Units.val_neg, Units.val_one]
  obtain ⟨-, hfinW, -, -, halt⟩ := hmain b t hbN ht
  obtain ⟨B, hBv, hBalt, hBnd, -, -⟩ := halt rfl
  obtain ⟨m, bW, hm, hb1, hb2, hb3⟩ := exists_blueprint_symplectic_basis B hBalt hBnd
  rw [hfinW, Module.finrank_fin_fun] at hm
  obtain rfl : m = 2 := by omega
  set bas : Fin 4 → conjFixed h ((b : K) • τ₀) :=
    ![bW (Sum.inl 0), bW (Sum.inl 1), bW (Sum.inr 0), bW (Sum.inr 1)] with hbas
  have hgram : ∀ j k : Fin 4, ((B (bas j) (bas k) : h.fixedField) : K) = omg j k := by
    have e3 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb3 i j)
    have e1 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb1 i j)
    have e2 := fun i j => congrArg (fun z : h.fixedField => (z : K)) (hb2 i j)
    have e4 : ∀ i j : Fin 2, ((B (bW (Sum.inr j)) (bW (Sum.inl i)) : h.fixedField) : K) =
        -(if i = j then 1 else 0) := by
      intro i j
      rw [← hBalt.neg_eq, Subfield.coe_neg, hb3]
      split_ifs <;> simp
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [hbas, omg, e1, e2, e3, e4]
  have hherm : ∀ j k : Fin 4, stdHermForm h 4 (bas j) (bas k) = t * omg j k := by
    intro j k
    rw [← hgram j k, hBv]
    field_simp
  have hfix : ∀ j : Fin 4, l • ((A : Matrix (Fin 4) (Fin 4) K) *ᵥ
      fun i => h.bar ((bas j : Fin 4 → K) i)) = bas j := by
    intro j
    have := (mem_conjFixed.1 (bas j).2)
    rw [LinearMap.smul_apply] at this
    exact this
  set R : Matrix (Fin 4) (Fin 4) K := Matrix.of fun i j => (bas j : Fin 4 → K) i with hR
  have hR1 : uStar h R * R = (t : K) • omg := by
    ext j k
    rw [Matrix.smul_apply, smul_eq_mul, ← hherm j k, stdHermForm_apply]
    simp [uStar, Matrix.mul_apply, hR]
  have hR2 : Rᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * R = (-(l * t)) • omg := by
    ext j k
    have e := dot_inv_mulVec_of_fixed h hAt hl0 (hfix j) (bas k : Fin 4 → K)
    rw [hherm j k] at e
    rw [Matrix.smul_apply, smul_eq_mul]
    have e' : (Rᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * R) j k =
        (bas j : Fin 4 → K) ⬝ᵥ ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *ᵥ (bas k : Fin 4 → K)) := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp only [Matrix.transpose_apply, hR, Matrix.of_apply, dotProduct, Matrix.mulVec,
        Matrix.mul_apply]
    rw [e', e]
    ring
  obtain ⟨μ, hμg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set θ : K := (μ : K) with hθdef
  have hθ0 : θ ≠ 0 := Units.ne_zero μ
  have hθb : h.bar θ ≠ θ := bar_ne_of_generator h hμg
  have ht0 : (t : K) ≠ 0 := Units.ne_zero t
  set S := sfr h θ t with hS
  have hRS : uStar h (R * S) * (R * S) = stdG := by
    rw [uStar_mul]
    calc uStar h S * uStar h R * (R * S) = uStar h S * (uStar h R * R) * S := by
          simp only [Matrix.mul_assoc]
      _ = (t : K) • (uStar h S * omg * S) := by
          rw [hR1, Matrix.mul_smul, Matrix.smul_mul]
      _ = stdG := by rw [uStar_sfr h hθ0 hθb ht ht0, smul_smul, mul_inv_cancel₀ ht0, one_smul]
  have hdetN : ∀ M : Matrix (Fin 4) (Fin 4) K, uStar h M * M = stdG →
      h.bar M.det * M.det = 1 := by
    intro M hM
    have := congrArg Matrix.det hM
    have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, hGd] at this
    have e : (uStar h M).det = h.bar M.det := by
      rw [uStar, det_transpose, RingHom.map_det]
      rfl
    rwa [e] at this
  have hNRS := hdetN _ hRS
  have hNP := hdetN _ hP
  have hRS0 : (R * S).det ≠ 0 := right_ne_zero_of_mul_eq_one hNRS
  have hP0 : (P : Matrix (Fin 4) (Fin 4) K).det ≠ 0 := right_ne_zero_of_mul_eq_one hNP
  have e1 : h.bar (P : Matrix (Fin 4) (Fin 4) K).det = ((P : Matrix (Fin 4) (Fin 4) K).det)⁻¹ :=
    eq_inv_of_mul_eq_one_left hNP
  have e2 : h.bar (R * S).det = ((R * S).det)⁻¹ := eq_inv_of_mul_eq_one_left hNRS
  obtain ⟨u, hu⟩ : ∃ u : K, u = (P : Matrix (Fin 4) (Fin 4) K).det * ((R * S).det)⁻¹ :=
    ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact mul_ne_zero hP0 (inv_ne_zero hRS0)
  have huq : u ^ (p ^ f + 1) = 1 := by
    have e : u ^ (p ^ f + 1) = u * h.bar u := by rw [pow_succ', h.bar_apply]
    rw [e, hu, map_mul, map_inv₀, e1, e2]
    field_simp
  obtain ⟨d, hd⟩ := exists_mul_inv_bar_eq h (Units.mk0 u hu0) (by rw [Units.val_mk0]; exact huq)
  have hd0 : (d : K) ≠ 0 := Units.ne_zero d
  have hbd0 : h.bar (d : K) ≠ 0 := fun h0 => hd0 ((map_eq_zero h.bar).1 h0)
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin 4) (Fin 4) K, E = stdE h (d : K) := ⟨_, rfl⟩
  have hdetE : E.det = u := by
    have e3 : E.det = (d : K) * (h.bar (d : K))⁻¹ := by
      rw [hE, stdE, det_diagonal, Fin.prod_univ_four]
      simp
    rw [e3, hd, Units.val_mk0]
  obtain ⟨P'm, hP'm⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K, M = R * S * E := ⟨_, rfl⟩
  have hdet : P'm.det = (P : Matrix (Fin 4) (Fin 4) K).det := by
    rw [hP'm, det_mul, hdetE, hu]
    field_simp
  have hP'0 : P'm.det ≠ 0 := by rw [hdet]; exact hP0
  obtain ⟨P', hP'v⟩ : ∃ P' : GL (Fin 4) K, (P' : Matrix (Fin 4) (Fin 4) K) = P'm :=
    ⟨GeneralLinearGroup.mkOfDetNeZero P'm hP'0, GeneralLinearGroup.val_mkOfDetNeZero _ _⟩
  have hG : uStar h (P' : Matrix (Fin 4) (Fin 4) K) * (P' : Matrix (Fin 4) (Fin 4) K) = stdG := by
    rw [hP'v, hP'm, uStar_mul]
    calc uStar h E * uStar h (R * S) * (R * S * E) =
        uStar h E * (uStar h (R * S) * (R * S)) * E := by simp only [Matrix.mul_assoc]
      _ = stdG := by rw [hRS, hE]; exact uStar_stdE_mul h _ hd0
  set x₀ : K := (h.bar θ - θ) / h.bar θ with hx₀
  set z₀ : K := θ / ((t : K) ^ 2 * (θ - h.bar θ)) with hz₀
  have hY : (P' : Matrix (Fin 4) (Fin 4) K)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) *
      (P' : Matrix (Fin 4) (Fin 4) K) =
        bJ (-(l * t) * (x₀ * d)) (-(l * t) * (z₀ * (h.bar (d : K))⁻¹)) := by
    rw [hP'v, hP'm]
    calc (R * S * E)ᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R * S * E) =
        Eᵀ * (Sᵀ * (Rᵀ * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * R) * S) * E := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (-(l * t)) • (Eᵀ * (Sᵀ * omg * S) * E) := by
          rw [hR2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = _ := by
          rw [transpose_sfr h hθ0 hθb ht0, hE, stdE_transpose_bJ, smul_bJ]
  have hθ' : h.bar θ ≠ 0 := fun h0 => hθ0 ((map_eq_zero h.bar).1 h0)
  have hx0 : x₀ ≠ 0 := div_ne_zero (sub_ne_zero.2 hθb) hθ'
  have hz0 : z₀ ≠ 0 := div_ne_zero hθ0 (mul_ne_zero (pow_ne_zero 2 ht0)
    (sub_ne_zero.2 (Ne.symm hθb)))
  have hlt : -(l * t) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hl0 ht0)
  have hx0b : h.bar x₀ = (θ - h.bar θ) / θ := by rw [hx₀, map_div₀, map_sub, h.bar_bar]
  have hxz : h.bar x₀ * z₀ = ((t : K) ^ 2)⁻¹ := by
    have hdd' : θ - h.bar θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθb)
    rw [hx0b, hz₀]
    field_simp
  have key : h.bar (-(l * t) * (x₀ * d)) * (-(l * t) * (z₀ * (h.bar (d : K))⁻¹)) = 1 := by
    rw [map_mul, map_neg, map_mul, map_mul, hbl, ht]
    calc -(l * -(t : K)) * (h.bar x₀ * h.bar (d : K)) * (-(l * t) * (z₀ * (h.bar (d : K))⁻¹)) =
        -(l ^ 2) * ((t : K) ^ 2 * (h.bar x₀ * z₀)) * (h.bar (d : K) * (h.bar (d : K))⁻¹) := by
          ring
      _ = 1 := by
          rw [hxz, mul_inv_cancel₀ (pow_ne_zero 2 ht0), mul_inv_cancel₀ hbd0, hl]
          ring
  have hy₂ : -(l * t) * (z₀ * (h.bar (d : K))⁻¹) = (h.bar (-(l * t) * (x₀ * d)))⁻¹ :=
    eq_inv_of_mul_eq_one_right key
  refine ⟨P', hG, _, by rw [hP'v, hdet], mul_ne_zero hlt (mul_ne_zero hx0 hd0), ?_⟩
  rw [hY, hy₂]

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
