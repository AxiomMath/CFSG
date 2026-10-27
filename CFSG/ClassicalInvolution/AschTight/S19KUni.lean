module

public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
public import CFSG.ClassicalInvolution.AschTight.S19KGen
public import CFSG.ClassicalInvolution.AschTight.S19KUniStd
public import CFSG.ClassicalInvolution.AschTight.S19KTrace

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

open CFSG.ClassicalInvolution CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits
open scoped MatrixGroups

@[expose] def slMap2 {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂) :
    SL(2, F₁) ≃* SL(2, F₂) where
  toFun := Matrix.SpecialLinearGroup.map (e : F₁ →+* F₂)
  invFun := Matrix.SpecialLinearGroup.map (e.symm : F₂ →+* F₁)
  left_inv A := Subtype.ext (by ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
  right_inv A := Subtype.ext (by ext i j; simp [Matrix.SpecialLinearGroup.map_apply_coe])
  map_mul' := map_mul _

theorem trace_slMap2 {F₁ F₂ : Type} [Field F₁] [Field F₂] (e : F₁ ≃+* F₂) (A : SL(2, F₁)) :
    ((slMap2 e A : SL(2, F₂)) : Matrix (Fin 2) (Fin 2) F₂).trace =
      e ((A : Matrix (Fin 2) (Fin 2) F₁).trace) := by
  change ((Matrix.SpecialLinearGroup.map (e : F₁ →+* F₂) A : SL(2, F₂)) :
    Matrix (Fin 2) (Fin 2) F₂).trace = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

theorem trace_mapMatrixU {K : Type} [Field K] (τ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) :
    (τ.mapMatrix M).trace = τ M.trace := by
  simp [RingEquiv.mapMatrix_apply, Matrix.trace]

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem uni_lift_data (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    {F' : Type} [Field F'] [Finite F'] (hF' : Nat.card F' = p ^ f) {E : Type} [Group E]
    (θ : Phan.Su K p f 3 →* E) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Phan.Su K p f 3)) (φ : MulAut E)
    (hφ : ∃ (ι : ↥((rootU K p f).map θ) ≃* SL(2, F')) (g : GL (Fin 2) F'),
      ∀ x : ↥((rootU K p f).map θ),
        ((ι.symm (Asc77.AscL62.semilinHom g (RingEquiv.refl _) (ι x)) :
          ↥((rootU K p f).map θ)) : E) = φ x) :
    ∃ (α : Phan.Su K p f 3 →* Phan.Su K p f 3) (G : GL (Fin 3) K) (τ : K ≃+* K),
      (∀ x, θ (α x) = φ (θ x)) ∧
      (∀ x, (((α x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (G : Matrix (Fin 3) (Fin 3) K) *
          τ.mapMatrix (((x : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∧
      ((G : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f)).transpose *
        (G : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      IsBlockDiag (G : Matrix (Fin 3) (Fin 3) K) ∧
      (τ = RingEquiv.refl K ∨ τ = unitaryInvolution K p f) := by
  obtain ⟨ι, g, hι⟩ := hφ
  obtain ⟨α, G, τ, hα, hform, hiso, -⟩ :=
    ModelFacts.UnitaryAut.unitaryAutClassification_isometry_of_card hK hp hq (le_refl 3) E θ hθ
      hker φ
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hcard := card_fixedSubfield (F := K) (p := p) (f := f) hK
  have hcl2 := Models.isClassicalSL2_rootSU2 (K := K) (p := p) (f := f) hK hp (n := 3)
    (by norm_num)
  have : Group.IsPerfect (rootU K p f) := hcl2.isPerfect (by omega)
  have hR : ∀ r ∈ rootU K p f, r ∈ Subgroup.center (Phan.Su K p f 3) → r = 1 :=
    fun r hr hc => eq_one_of_mem_center_rootSU2 hK hp hf hr hc
  have hφL : ∀ x ∈ (rootU K p f).map θ, φ x ∈ (rootU K p f).map θ := fun x hx => by
    rw [← hι ⟨x, hx⟩]
    exact (ι.symm _).2
  have hαR := mem_of_lift θ hker hR hφL hα
  obtain ⟨ι₀, hι₀⟩ := exists_stdEquivU hK
  have : Fintype (fixedSubfield K p f) := Fintype.ofFinite _
  have : Fintype F' := Fintype.ofFinite _
  let ρ : fixedSubfield K p f ≃+* F' := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, hF'])
  have hodd' : Odd (Nat.card F') := by
    rw [hF']
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  have htr := trace_eq_of_conj hodd' (by omega) (ι₀.trans (slMap2 ρ))
    ((restrictEquiv θ hker hR).trans ι) (liftRestrict α hαR) g
    (semilin_restrict θ hker hR hα hαR ι g hι)
  have htr3 : ∀ r : rootU K p f, τ ((((r : Phan.Su K p f 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).trace =
      ((((r : Phan.Su K p f 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).trace := by
    intro r
    have h1 := htr r
    simp only [MulEquiv.trans_apply, trace_slMap2] at h1
    have h2 := ρ.injective h1
    have h3 := hι₀ (liftRestrict α hαR r)
    rw [coe_liftRestrict, hform, Matrix.trace_units_conj, trace_mapMatrixU, h2, ← hι₀] at h3
    exact h3
  have hτ : ∀ c : K, unitaryInvolution K p f c = c → τ c = c := by
    intro c hc
    have h1 := htr3 (ι₀.symm (traceSL ⟨c, mem_fixedSubfield.mpr hc⟩))
    rw [hι₀, MulEquiv.apply_symm_apply, trace_traceSL, map_add, map_one] at h1
    exact add_right_cancel h1
  refine ⟨α, G, τ, hα, hform, hiso, ?_, ringEquiv_eq_of_fixes hK τ hτ⟩
  set z₀ := Models.rootInvSU K p f (n := 3) (by norm_num)
  have hz₀R : z₀ ∈ rootU K p f := Models.rootInvSU_mem_rootSU2 _
  have hz₀2 : z₀ ^ 2 = 1 := by rw [← hcl2.orderOf_eq_two]; exact pow_orderOf_eq_one z₀
  have hαz : α z₀ = z₀ := by
    refine hcl2.eq_of_orderOf_eq_two (Models.odd_natCard_fixedSubfield hK hp) (hαR _ hz₀R)
      (orderOf_eq_prime ?_ ?_)
    · rw [← map_pow, hz₀2, map_one]
    · intro h1
      have h3 : θ z₀ = 1 := by
        apply φ.injective
        rw [← hα, h1, map_one, map_one]
      have h4 := hR z₀ hz₀R (hker h3)
      have h5 := hcl2.orderOf_eq_two
      rw [h4, orderOf_one] at h5
      exact absurd h5 (by norm_num)
  have h2 : (2 : K) ≠ 0 := Models.two_ne_zero_of_charP_ne_two hp
  have h1 := hform z₀
  rw [hαz, coe_rootInvSU_three] at h1
  have hτz : τ.mapMatrix !![(-1 : K), 0, 0; 0, -1, 0; 0, 0, 1] =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [RingEquiv.mapMatrix_apply]
  rw [hτz] at h1
  refine isBlockDiag_of_commute_negBlock h2 _ ?_
  calc (G : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] =
      (G : Matrix (Fin 3) (Fin 3) K) * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] *
        (((G⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (G : Matrix (Fin 3) (Fin 3) K)) := by
        rw [Units.inv_mul, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, ← h1]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
