module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerUGraph

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel

@[expose] def u42Sgn (E : Type) [Field E] : (Fin 2 ⊕ Fin 2) → E
  | Sum.inl _ => 1
  | Sum.inr _ => -1

theorem u42Sgn_ne_zero {E : Type} [Field E] (j : Fin 2 ⊕ Fin 2) : u42Sgn E j ≠ 0 := by
  rcases j with j | j <;> simp [u42Sgn]

theorem u42Sgn_sq {E : Type} [Field E] (j : Fin 2 ⊕ Fin 2) : u42Sgn E j * u42Sgn E j = 1 := by
  rcases j with j | j <;> simp [u42Sgn]

theorem u42Sgn_bar {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E)
    (j : Fin 2 ⊕ Fin 2) : h.bar (u42Sgn E j) = u42Sgn E j := by
  rcases j with j | j <;> simp [u42Sgn]


theorem u42_alt_abstract {p f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData p f E) (hp : Odd p)
    {V : Type} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (hV : finrank E V = 4) {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm)
    (hnd : Hf.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V) (hτ₀ : Function.Bijective τ₀)
    (hτ₀H : ∀ v w, Hf (τ₀ v) (τ₀ w) = h.bar (Hf v w)) (hμ : ∀ v, τ₀ (τ₀ v) = (-1 : E) • v) :
    ∃ (b : Eˣ) (g : LinearMap.GeneralLinearGroup E V), h.norm (b : E) = -1 ∧
      g ∈ sesqUnitaryGroup Hf ∧ LinearMap.det ((g : LinearMap.GeneralLinearGroup E V) :
        V →ₗ[E] V) = (b : E) ^ 4 ∧
      ∀ v, τ₀ ((g : V →ₗ[E] V) v) = (h.bar (b : E) / (b : E)) • (g : V →ₗ[E] V) (τ₀ v) := by
  have : Finite E := h.finite
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hp (by decide)
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨-, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h hp
    (by omega : 1 ≤ finrank E V) hH hnd τ₀ hτ₀ hτ₀H (-1 : Eˣ) (by simpa using hμ)
  obtain ⟨hττ, hfinW, -, -, hB2⟩ := hall b t hb ht
  obtain ⟨B, hBv, halt, hBnd, -, -⟩ := hB2 rfl
  have hbN : h.norm (b : E) = -1 := by simpa using hb
  haveI : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  obtain ⟨m, bW, hm, hll, hrr, hlr⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      B halt hBnd
  have hm2 : m = 2 := by omega
  subst hm2
  have hb0 : (b : E) ≠ 0 := b.ne_zero
  have ht0 : (t : E) ≠ 0 := t.ne_zero
  let bV : Basis (Fin 2 ⊕ Fin 2) E V := conjFixedBasis hττ ht ht0 h2 bW
  have hbV : ∀ j, bV j = (bW j : V) := conjFixedBasis_apply hττ ht ht0 h2 bW
  have hτb : ∀ j, τ₀ (bV j) = (b : E)⁻¹ • bV j := by
    intro j
    have h1 : ((b : E) • τ₀) (bV j) = bV j := by
      rw [hbV]
      exact mem_conjFixed.mp (bW j).2
    rw [LinearMap.smul_apply] at h1
    exact (eq_inv_smul_iff₀ hb0).2 h1
  have hHf : ∀ i j, Hf (bV i) (bV j) = (t : E) * ((B (bW i) (bW j) : h.fixedField) : E) := by
    intro i j
    rw [hbV, hbV, hBv, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]
  have hc0 : ∀ j, (b : E) * u42Sgn E j ≠ 0 := fun j => mul_ne_zero hb0 (u42Sgn_ne_zero j)
  let gl : V →ₗ[E] V := bV.constr E (fun j => ((b : E) * u42Sgn E j) • bV j)
  let gl' : V →ₗ[E] V := bV.constr E (fun j => ((b : E) * u42Sgn E j)⁻¹ • bV j)
  have hgl : ∀ j, gl (bV j) = ((b : E) * u42Sgn E j) • bV j := fun j => bV.constr_basis E _ j
  have hgl' : ∀ j, gl' (bV j) = ((b : E) * u42Sgn E j)⁻¹ • bV j := fun j => bV.constr_basis E _ j
  have hinv1 : gl * gl' = 1 := by
    refine bV.ext fun j => ?_
    rw [Module.End.mul_apply, hgl', map_smul, hgl, smul_smul, inv_mul_cancel₀ (hc0 j), one_smul]
    rfl
  have hinv2 : gl' * gl = 1 := by
    refine bV.ext fun j => ?_
    rw [Module.End.mul_apply, hgl, map_smul, hgl', smul_smul, mul_inv_cancel₀ (hc0 j), one_smul]
    rfl
  let g : LinearMap.GeneralLinearGroup E V := ⟨gl, gl', hinv1, hinv2⟩
  have hgcoe : ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) = gl := rfl
  have hbasis : ∀ i j, Hf (gl (bV i)) (gl (bV j)) = Hf (bV i) (bV j) := by
    intro i j
    have hN' : (b : E) * h.bar (b : E) = -1 := hbN
    simp only [hgl, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_smul,
      RingHom.id_apply, map_mul, u42Sgn_bar h]
    rcases i with i | i <;> rcases j with j | j
    · simp [hHf, hll, u42Sgn]
    · simp only [u42Sgn, hHf]
      linear_combination
        (-((t : E) * ((B (bW (Sum.inl i)) (bW (Sum.inr j)) : h.fixedField) : E))) * hN'
    · simp only [u42Sgn, hHf]
      linear_combination
        (-((t : E) * ((B (bW (Sum.inr i)) (bW (Sum.inl j)) : h.fixedField) : E))) * hN'
    · simp [hHf, hrr, u42Sgn]
  have hstep : ∀ i y, Hf (gl (bV i)) (gl y) = Hf (bV i) y := by
    intro i y
    have e : (Hf (gl (bV i))).comp gl = Hf (bV i) := bV.ext fun j => by
      simp only [LinearMap.comp_apply]
      exact hbasis i j
    exact congrArg (fun L => L y) e
  have hgU : g ∈ sesqUnitaryGroup Hf := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    have e : (Hf.flip (gl y)).comp gl = Hf.flip y := bV.ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.flip_apply]
      exact hstep i y
    have := congrArg (fun L => L x) e
    simpa using this
  have hdet : LinearMap.det gl = (b : E) ^ 4 := by
    rw [← LinearMap.det_toMatrix bV gl]
    have hmat : LinearMap.toMatrix bV bV gl =
        Matrix.diagonal (fun j => (b : E) * u42Sgn E j) := by
      ext i j
      rw [LinearMap.toMatrix_apply, hgl, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [hmat, Matrix.det_diagonal, Fintype.prod_sum_type]
    simp [u42Sgn, Fin.prod_univ_two]
    ring
  have hcompat : ∀ v, τ₀ (gl v) = (h.bar (b : E) / (b : E)) • gl (τ₀ v) := by
    intro v
    have e : τ₀.comp gl = ((h.bar (b : E) / (b : E)) • gl).comp τ₀ := bV.ext fun j => by
      simp only [LinearMap.comp_apply, hgl, LinearMap.smul_apply, hτb, map_smulₛₗ, map_smul,
        smul_smul, map_mul, u42Sgn_bar h j]
      congr 1
      simp only [RingHom.id_apply]
      field_simp
    exact congrArg (fun L => L v) e
  exact ⟨b, g, hbN, hgU, hdet, hcompat⟩


theorem u42_alt_element {K : Type} [Field K] (h : UnitaryFieldData 3 1 K)
    (A : ↥(primeFormUnitary h (idGram K 4)))
    (hAc : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar = (-1 : K) • 1) :
    ∃ (g : ↥(primeFormUnitary h (idGram K 4))) (z : Kˣ),
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = -1 ∧ h.norm (z : K) = 1 ∧
        ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar =
          (z : K) • (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  haveI : Finite K := h.finite
  have hodd : Odd 3 := ⟨1, by norm_num⟩
  have hτ₀ : Function.Bijective (semilinearMatrixMap h
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) :=
    CFSG.ComponentClassification.CatLeafProof.OddInner.semilinearMatrixMap_bijective_of h
      (c := -1) (by simp) hAc
  have hτ₀B := CFSG.ComponentClassification.CatLeafProof.OddInner.idForm_semilinearMatrixMap h A.2
  have hμ : ∀ v, semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      (semilinearMatrixMap h ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) v) = (-1 : K) • v :=
    CFSG.ComponentClassification.CatLeafProof.OddInner.semilinearMatrixMap_sq_of h hAc
  obtain ⟨b, g', hbN, hgU, hdet, hcompat⟩ := u42_alt_abstract h hodd
    (V := Fin 4 → K) (by simp) (idForm_isSymm h 4) (idForm_separatingLeft h 4) _ hτ₀ hτ₀B hμ
  obtain ⟨g, hg⟩ := exists_toLinU hgU
  have hGv : ∀ v : Fin 4 → K,
      ((g' : LinearMap.GeneralLinearGroup K (Fin 4 → K)) : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) v =
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v := fun v => by
    rw [← hg]
    rfl
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  have hbb0 : h.bar (b : K) ≠ 0 := (map_ne_zero h.bar).2 hb0
  refine ⟨g, Units.mk0 (h.bar (b : K) / (b : K)) (div_ne_zero hbb0 hb0), ?_, ?_, ?_⟩
  · have h1 : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = (b : K) ^ 4 := by
      rw [← hdet, ← hg]
      change _ = LinearMap.det (Matrix.toLin' ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
      rw [LinearMap.det_toLin']
    rw [h1, ← hbN, h.norm_eq_pow]
    norm_num
  · rw [UnitaryFieldData.norm, Units.val_mk0, map_div₀, h.bar_bar]
    field_simp
  · set G : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hG
    set A' : Matrix (Fin 4) (Fin 4) K := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hA'
    have hbarv : ∀ v : Fin 4 → K, (fun i => h.bar ((G *ᵥ v) i)) =
        G.map h.bar *ᵥ fun i => h.bar (v i) := fun v => by
      funext i
      exact RingHom.map_mulVec h.bar G v i
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    have h1 := hcompat (fun i => h.bar (w i))
    rw [hGv, hGv, semilinearMatrixMap_apply, semilinearMatrixMap_apply, hbarv] at h1
    have hww : (fun i => h.bar ((fun i => h.bar (w i)) i)) = w :=
      funext fun i => h.bar_bar (w i)
    rw [hww, mulVec_mulVec, mulVec_mulVec] at h1
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mk0, smul_mulVec]
    exact h1

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
