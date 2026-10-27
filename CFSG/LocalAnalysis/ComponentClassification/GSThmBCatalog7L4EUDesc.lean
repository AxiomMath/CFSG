module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowSForm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OutU
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentForm
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4EU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatFactsL4U4 CFSG.LinearGroups
open CFSG.ComponentClassification.CatFactsL4U4.UnitaryOut (uStar uStar_mul uStar_one)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem isSquare_of_norm_eq_sq (hp2 : p ≠ 2) {d s : K} (hd : d ≠ 0) (hs : h.bar s = s)
    (hds : d * h.bar d = s ^ 2) : IsSquare d := by
  classical
  have : Finite K := h.finite
  have := Fintype.ofFinite K
  have : CharP K p := h.charP
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set q := p ^ f with hq
  have hcard : Fintype.card K = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, h.card_eq_sq]
  have hqodd : Odd q := (h.prime.odd_of_ne_two hp2).pow
  have hs0 : s ≠ 0 := by
    rintro rfl
    have hb0 : h.bar d ≠ 0 := fun h0 => hd ((map_eq_zero h.bar).1 h0)
    rw [zero_pow two_ne_zero] at hds
    exact mul_ne_zero hd hb0 hds
  rw [FiniteField.isSquare_iff hK2 hd, hcard]
  obtain ⟨m, hm⟩ := hqodd
  have hexp : q ^ 2 / 2 = (q + 1) * m := by
    rw [hm]
    have e : (2 * m + 1) ^ 2 = 2 * ((2 * m + 2) * m) + 1 := by ring
    rw [e, Nat.mul_add_div (by norm_num : 0 < 2), show (1 : ℕ) / 2 = 0 from rfl, add_zero]
  have hbar : h.bar d = d ^ q := h.bar_apply d
  have hsq : s ^ q = s := by rw [← h.bar_apply, hs]
  have hs1 : s ^ (2 * m) = 1 := by
    have h1 : s ^ (2 * m) * s = s := by rw [← pow_succ, ← hm, hsq]
    exact (mul_eq_right₀ hs0).mp h1
  rw [hexp, pow_mul, pow_succ, ← hbar, mul_comm (h.bar d) d, hds, ← pow_mul, hs1]

theorem det_sq_of_split_descent (hp2 : p ≠ 2) {A : Matrix (Fin 4) (Fin 4) K} {b t : Kˣ}
    {τ : (Fin 4 → K) →ₛₗ[h.bar] (Fin 4 → K)}
    (hτ : ∀ v, τ v = (b : K) • (A *ᵥ fun i => h.bar (v i)))
    (hb : h.norm (b : K) = 1) (ht : h.bar (t : K) = -(t : K))
    (hfin : Module.finrank h.fixedField (conjFixed h τ) = 4)
    (B' : LinearMap.BilinForm h.fixedField (conjFixed h τ))
    (hB' : ∀ v w, (B' v w : K) = stdHermForm h 4 v w) (hsym : B'.IsSymm)
    (ψ : conjFixed h τ ≃ₗ[h.fixedField] Matrix (Fin 2) (Fin 2) h.fixedField)
    (hψ : ∀ v, CatalogueBOrthogonalDescent.originalQuadratic B' v = (ψ v).det) :
    ∃ u : K, h.norm u = 1 ∧ A.det = u ^ 2 := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  have h2₀ : (2 : h.fixedField) ≠ 0 := fun h0 => h2 (by
    have h1 := congrArg h.fixedField.subtype h0
    rwa [map_ofNat, map_zero] at h1)
  have : Module.Free h.fixedField (conjFixed h τ) := Module.Free.of_divisionRing _ _
  have : Module.Finite h.fixedField (conjFixed h τ) := finite_conjFixed
  let bk : Module.Basis (Fin 4) h.fixedField (conjFixed h τ) :=
    Module.finBasisOfFinrankEq _ _ hfin
  set P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun a i => ((bk i : conjFixed h τ) : Fin 4 → K) a
    with hP
  have hfix : (b : K) • (A * P.map h.bar) = P := by
    ext a i
    have h1 := congrFun (show τ (bk i : Fin 4 → K) = bk i from (bk i).2) a
    rw [hτ] at h1
    simpa [hP, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h1
  have hli : LinearIndependent K (fun i => ((bk i : conjFixed h τ) : Fin 4 → K)) :=
    linearIndependent_conjFixed ht t.ne_zero h2 bk
  have hPu : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hP0 : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hPu).ne_zero
  set G₀ : Matrix (Fin 4) (Fin 4) h.fixedField := LinearMap.BilinForm.toMatrix bk B' with hG₀
  have hG : uStar h P * P = G₀.map h.fixedField.subtype := by
    ext i j
    simp [uStar, Matrix.mul_apply, hG₀, hB', stdHermForm_apply, hP]
  have hbP : h.bar P.det = (P.map h.bar).det := by
    rw [show P.map h.bar = h.bar.mapMatrix P from rfl, ← RingHom.map_det]
  have hdetG : P.det * h.bar P.det = ((G₀.det : h.fixedField) : K) := by
    have h1 := congrArg Matrix.det hG
    rw [det_mul, uStar, det_transpose, ← hbP,
      show G₀.map h.fixedField.subtype = h.fixedField.subtype.mapMatrix G₀ from rfl,
      ← RingHom.map_det] at h1
    rw [mul_comm]
    exact h1
  have hG0 : G₀.det ≠ 0 := by
    intro h0
    rw [h0, ZeroMemClass.coe_zero] at hdetG
    exact mul_ne_zero hP0 (fun h1 => hP0 ((map_eq_zero h.bar).1 h1)) hdetG
  set G₁ : Matrix (Fin 4) (Fin 4) h.fixedField := (2 : h.fixedField)⁻¹ • G₀ with hG₁
  have hG10 : G₁.det ≠ 0 := by
    rw [hG₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero h2₀)) hG0
  set A' : GL (Fin 4) h.fixedField := (GeneralLinearGroup.mkOfDetNeZero G₁ hG10)⁻¹ with hA'
  have hA'inv : ((A'⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) = G₁ := by
    rw [hA', inv_inv]
    rfl
  have hG₁t : G₁ᵀ = G₁ := by
    ext i j
    simp only [hG₁, hG₀, Matrix.transpose_apply, Matrix.smul_apply,
      LinearMap.BilinForm.toMatrix_apply, hsym.eq (bk i) (bk j)]
  have hA't : (A' : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = A' := by
    rw [hA']
    exact OddSelector.transpose_inv_eq_of_transpose_eq hG₁t
  set ψ' : (Fin 4 → h.fixedField) ≃ₗ[h.fixedField] Matrix (Fin 2) (Fin 2) h.fixedField :=
    bk.equivFun.symm.trans ψ with hψ'
  have hψ'v : ∀ v, v ⬝ᵥ (((A'⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4)
      h.fixedField) *ᵥ v) = (ψ' v).det := by
    intro v
    rw [hA'inv, hG₁, Matrix.smul_mulVec, dotProduct_smul, hG₀,
      LinearMap.BilinForm.dotProduct_toMatrix_mulVec, hψ', LinearEquiv.trans_apply, ← hψ,
      CatalogueBOrthogonalDescent.originalQuadratic_apply, smul_eq_mul]
    field_simp
  obtain ⟨s, hs⟩ := OddSelector.Catalog7L4E.isSquare_det_of_split h2₀ hA't ψ' hψ'v
  have hdetA' : (GeneralLinearGroup.det A' : h.fixedField) * G₁.det = 1 := by
    rw [hA', map_inv, Units.val_inv_eq_inv_val, GeneralLinearGroup.val_det_apply,
      GeneralLinearGroup.val_mkOfDetNeZero, inv_mul_cancel₀ hG10]
  set s₀ : h.fixedField := 4 * (s : h.fixedField)⁻¹ with hs₀
  have hG0s : G₀.det = s₀ ^ 2 := by
    have e1 : G₀ = (2 : h.fixedField) • G₁ := by
      rw [hG₁, smul_smul, mul_inv_cancel₀ h2₀, one_smul]
    rw [e1, det_smul, Fintype.card_fin]
    rw [hs, Units.val_pow_eq_pow_val] at hdetA'
    have hsne : (s : h.fixedField) ≠ 0 := s.ne_zero
    rw [hs₀]
    field_simp
    linear_combination 16 * hdetA'
  have hs₀b : h.bar (s₀ : K) = s₀ := (h.mem_fixedField).mp s₀.2
  have hNP : P.det * h.bar P.det = (s₀ : K) ^ 2 := by
    rw [hdetG, hG0s]
    simp
  obtain ⟨e, he⟩ := isSquare_of_norm_eq_sq h hp2 hP0 hs₀b hNP
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    exact hP0 he
  have hbe0 : h.bar e ≠ 0 := fun h0 => he0 ((map_eq_zero h.bar).1 h0)
  have hbb0 : h.bar (b : K) ≠ 0 := fun h0 => hb0 ((map_eq_zero h.bar).1 h0)
  have hdet := congrArg Matrix.det hfix
  rw [det_smul, det_mul, Fintype.card_fin, ← hbP, he, map_mul] at hdet
  have hbb : (b : K) * h.bar (b : K) = 1 := hb
  refine ⟨e * ((b : K) ^ 2 * h.bar e)⁻¹, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, map_mul, map_inv₀, map_mul, map_pow, h.bar_bar]
    field_simp
    linear_combination (-((b : K) * h.bar (b : K) + 1)) * hbb
  · field_simp
    linear_combination hdet

end Catalog7L4EU

end CFSG.ComponentClassification.GSThmB
