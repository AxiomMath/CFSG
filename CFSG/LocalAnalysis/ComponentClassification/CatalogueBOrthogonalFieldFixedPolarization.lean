module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssemblyAllDimensions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentOriginal

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed

open CatalogueBOrthogonalDescent CatalogueBLinearTwoDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem semilinear_polar_similarity (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) (x y : V) :
    Q.polarBilin (tau0 x) (tau0 y) = (mu : K) * sigma (Q.polarBilin x y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← tau0.map_add, hsim, hsim, hsim, map_sub, map_sub]
  ring

theorem originalQuadratic_polar_eq (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0) :
    originalQuadratic Q.polarBilin = Q := by
  ext x
  rw [originalQuadratic_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar_self]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  exact mul_div_cancel_left₀ (Q x) h2

variable [Finite K]

theorem subfield_card_odd (hodd : Odd (Nat.card K)) (k : Subfield K) :
    Odd (Nat.card k) := by
  let : Fintype k := Fintype.ofFinite k
  have hchar : ringChar k ≠ 2 := by
    rw [Algebra.ringChar_eq k K]
    exact CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  apply Nat.odd_iff.mpr
  simpa only [Nat.card_eq_fintype_card] using FiniteField.odd_card_of_char_ne_two hchar

variable [Module.Finite K V]

theorem semilinearCentralizer_pComponent_quasisimple
    (hodd : Odd (Nat.card K)) (sigma : K ≃+* K)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : 0 < Module.finrank K V) (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (tau0 : V ≃+ V) (mu lambda : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (p : ℕ) [Fact p.Prime] (L : Subgroup (semilinearOrthogonalCentralizer Q tau0))
    (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  let : Nontrivial V := (Module.finrank_pos_iff (R := K) (M := V)).mp hdim
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hsym : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hform := semilinear_polar_similarity Q sigma tau0 mu hsim
  have hfixed := square_scalar_fixed sigma tau0 (lambda : K) hsemi hsquare
  have hmu := square_multiplier_identity sigma hsigma Q.polarBilin hQ tau0
    (mu : K) (lambda : K) hform hsquare
  obtain ⟨b, c, hb, hc⟩ := exists_normalizing_units sigma hsigma hne mu lambda hfixed hmu
  let T := normalizedOperator tau0 b
  let hs := normalizedOperator_semilinear sigma tau0 b hsemi
  let hf := normalized_form_identity sigma Q.polarBilin tau0 mu b c hform hc
  have hT := normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb
  let : Module.Finite (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
    obtain ⟨e, d, hd⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hs
    exact Module.Finite.of_basis d
  have hnd := descendedBilinear_nondegenerate sigma T hs Q.polarBilin c hf
    hsigma hne h2 hT hsym hQ
  have hQ0 : (descendedQuadratic sigma T hs Q.polarBilin c hf).polarBilin.Nondegenerate := by
    rw [descendedQuadratic_polarBilin sigma T hs Q.polarBilin c hf hsym h2]
    exact hnd
  let e : semilinearOrthogonalCentralizer Q tau0 ≃*
      TauCeti.QuadraticMap.orthogonalGroup
        (originalDescendedQuadratic sigma tau0 b hsemi Q.polarBilin mu c hform hc) := by
    exact Eq.ndrec (motive := fun R : QuadraticForm K V =>
      semilinearOrthogonalCentralizer R tau0 ≃*
        TauCeti.QuadraticMap.orthogonalGroup
          (originalDescendedQuadratic sigma tau0 b hsemi Q.polarBilin mu c hform hc))
      (originalDescentCentralizerEquiv sigma tau0 b hsemi Q.polarBilin mu c hform hc
        hsigma hne h2 hsym lambda hsquare hb) (originalQuadratic_polar_eq Q h2)
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p e
    (CatalogueBOrthogonalAssembly.orthogonal_all_dimensional_pComponent_quasisimple
      (subfield_card_odd hodd (fixedSubfield K sigma))
      (originalDescendedQuadratic sigma tau0 b hsemi Q.polarBilin mu c hform hc) hQ0 p) L hL

end CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed
