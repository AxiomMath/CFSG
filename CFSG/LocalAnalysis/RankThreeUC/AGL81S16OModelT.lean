module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

variable {F : Type} [Field F] {b c : F}

@[expose] def cB1 (b : F) (w : OW F) : F := (w (Sum.inr (Sum.inl idx0)) + w (Sum.inl idx0)) / b

@[expose] def cA2 (b c : F) (w : OW F) : F :=
  (w (Sum.inr (Sum.inl idx1)) + c * w (Sum.inl idx1)) / b

@[expose] def Tfun (b c : F) (w : OW F) : Fin 3 → QuadraticAlgebra F (-c) b :=
  ![⟨w (Sum.inl idx0) + cA2 b c w, cB1 b w⟩, ⟨cA2 b c w, w (Sum.inl idx1) + cB1 b w⟩,
    ⟨w (Sum.inr (Sum.inr 0)), w (Sum.inr (Sum.inr 1))⟩]

@[expose] def Tinv (b c : F) (z : Fin 3 → QuadraticAlgebra F (-c) b) : OW F :=
  mkW !![(z 0).re + (z 1).re, (z 0).im + (z 1).im;
      c * ((z 0).im + (z 1).im) + b * (z 1).re, (z 0).re + (z 1).re + b * (z 0).im]
    ![(z 2).re, (z 2).im]

theorem Tfun_add (b c : F) (w w' : OW F) : Tfun b c (w + w') = Tfun b c w + Tfun b c w' := by
  funext i
  fin_cases i <;> (apply QuadraticAlgebra.ext <;> simp [Tfun, cB1, cA2, add_div] <;> ring)

theorem Tfun_smul (b c : F) (r : F) (w : OW F) : Tfun b c (r • w) = r • Tfun b c w := by
  funext i
  fin_cases i <;> (apply QuadraticAlgebra.ext <;> simp [Tfun, cB1, cA2] <;> ring)

variable [CharP F 2]

theorem cA2_spec (hb : b ≠ 0) (w : OW F) :
    b * cA2 b c w = w (Sum.inr (Sum.inl idx1)) + c * w (Sum.inl idx1) :=
  mul_div_cancel₀ _ hb

theorem cB1_spec (hb : b ≠ 0) (w : OW F) :
    b * cB1 b w = w (Sum.inr (Sum.inl idx0)) + w (Sum.inl idx0) :=
  mul_div_cancel₀ _ hb

theorem Tinv_Tfun (hb : b ≠ 0) (w : OW F) : Tinv b c (Tfun b c w) = w := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hp : b * cA2 b c w = w (Sum.inr (Sum.inl 1)) + c * w (Sum.inl 1) := cA2_spec (c := c) hb w
  have hq : b * cB1 b w = w (Sum.inr (Sum.inl 0)) + w (Sum.inl 0) := cB1_spec hb w
  conv_rhs => rw [← mkW_xM_nV w]
  unfold Tinv
  congr 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Tfun, xM, idx0, idx1]
    · linear_combination cA2 b c w * h2
    · linear_combination cB1 b w * h2
    · linear_combination (c * cB1 b w + c * w (Sum.inl 1)) * h2 + hp
    · linear_combination (w (Sum.inl 0) + cA2 b c w) * h2 + hq

theorem Tfun_Tinv (hb : b ≠ 0) (z : Fin 3 → QuadraticAlgebra F (-c) b) :
    Tfun b c (Tinv b c z) = z := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hq : cB1 b (Tinv b c z) = (z 0).im := by
    unfold cB1
    rw [div_eq_iff hb]
    simp [Tinv, mkW, idx0, idx1]
    linear_combination ((z 0).re + (z 1).re) * h2
  have hp : cA2 b c (Tinv b c z) = (z 1).re := by
    unfold cA2
    rw [div_eq_iff hb]
    simp [Tinv, mkW, idx0, idx1]
    linear_combination (c * ((z 0).im + (z 1).im)) * h2
  funext i
  fin_cases i <;> (apply QuadraticAlgebra.ext <;>
    simp only [Tfun, hq, hp, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] <;> simp [Tinv, mkW, idx0, idx1] <;>
    first | linear_combination (z 1).re * h2 | linear_combination (z 0).im * h2)

@[expose] noncomputable def Tequiv (hb : b ≠ 0) :
    OW F ≃ₗ[F] (Fin 3 → QuadraticAlgebra F (-c) b) where
  toFun := Tfun b c
  map_add' := Tfun_add b c
  map_smul' r w := Tfun_smul b c r w
  invFun := Tinv b c
  left_inv := Tinv_Tfun hb
  right_inv := Tfun_Tinv hb

theorem Tequiv_apply (hb : b ≠ 0) (w : OW F) : Tequiv (c := c) hb w = Tfun b c w := rfl

theorem quadMinus_eq_norm_sum (hb : b ≠ 0) (w : OW F) :
    quadMinus 3 F b c w = QuadraticAlgebra.norm (Tfun b c w 0) +
      QuadraticAlgebra.norm (Tfun b c w 1) + QuadraticAlgebra.norm (Tfun b c w 2) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hp := cA2_spec (c := c) hb w
  have hq := cB1_spec hb w
  rw [quadMinus_eq_det_add]
  simp only [Tfun, QuadraticAlgebra.norm_def, xM, nV, QN, Matrix.det_fin_two_of,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
  linear_combination (-(w (Sum.inl idx0))) * hq + (-(w (Sum.inl idx1))) * hp +
    (-(w (Sum.inl idx1) * w (Sum.inr (Sum.inl idx1)) + w (Sum.inl idx0) ^ 2 +
      c * w (Sum.inl idx1) ^ 2 + w (Sum.inl idx0) * cA2 b c w + cA2 b c w ^ 2 +
      b * cA2 b c w * cB1 b w + c * cB1 b w ^ 2 + c * w (Sum.inl idx1) * cB1 b w)) * h2

theorem ne_zero_of_irred [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb0
  haveI := Fintype.ofFinite F
  have hF : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hF c
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply hirr r
  rw [hb0, hr]
  linear_combination (r * r) * h2

theorem factRoot (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) :=
  ⟨fun r hr => hirr r (by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination hr + (b * r) * h2)⟩

theorem pow_card_succ_eq_norm [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hb : b ≠ 0)
    (z : QuadraticAlgebra F (-c) b) :
    z ^ (Nat.card F + 1) = algebraMap F (QuadraticAlgebra F (-c) b) (QuadraticAlgebra.norm z) := by
  let D := CFSG.RankThree.PartOne.KCOrthogonal.evenNormPlaneOfBin (K := F) (β := b) (γ := c) hb
  have h1 := D.algebraMap_N z
  have h2 := D.sigma_eq_pow z
  have h3 : D.N z = QuadraticAlgebra.norm z :=
    CFSG.RankThree.PartOne.KCOrthogonal.qaNormForm_apply z
  rw [h3] at h1
  rw [h1, h2, pow_succ, mul_comm]

theorem norm_unit_of_pow_eq_one [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] (hb : b ≠ 0)
    {a : QuadraticAlgebra F (-c) b} (ha : a ^ (Nat.card F + 1) = 1) :
    QuadraticAlgebra.norm a = 1 := by
  rw [pow_card_succ_eq_norm hb] at ha
  exact (algebraMap F (QuadraticAlgebra F (-c) b)).injective (ha.trans (map_one _).symm)

section Tori

abbrev QA (b c : F) : Type := QuadraticAlgebra F (-c) b

@[expose] noncomputable def triMul (u₀ u₁ u₂ : (QA b c)ˣ) :
    (Fin 3 → QA b c) ≃ₗ[F] (Fin 3 → QA b c) :=
  LinearEquiv.ofLinear
    { toFun := fun z => ![(u₀ : QA b c) * z 0, (u₁ : QA b c) * z 1, (u₂ : QA b c) * z 2]
      map_add' := fun z z' => by
        funext i
        fin_cases i <;> simp [mul_add]
      map_smul' := fun r z => by
        funext i
        fin_cases i <;> simp [mul_smul_comm] }
    { toFun := fun z => ![((u₀⁻¹ : (QA b c)ˣ) : QA b c) * z 0,
        ((u₁⁻¹ : (QA b c)ˣ) : QA b c) * z 1, ((u₂⁻¹ : (QA b c)ˣ) : QA b c) * z 2]
      map_add' := fun z z' => by
        funext i
        fin_cases i <;> simp [mul_add]
      map_smul' := fun r z => by
        funext i
        fin_cases i <;> simp [mul_smul_comm] }
    (LinearMap.ext fun z => by
      funext i
      fin_cases i <;> simp [← mul_assoc])
    (LinearMap.ext fun z => by
      funext i
      fin_cases i <;> simp [← mul_assoc])

theorem triMul_apply (u₀ u₁ u₂ : (QA b c)ˣ) (z : Fin 3 → QA b c) :
    triMul u₀ u₁ u₂ z = ![(u₀ : QA b c) * z 0, (u₁ : QA b c) * z 1, (u₂ : QA b c) * z 2] := rfl

theorem triMul_mul_apply (u₀ u₁ u₂ v₀ v₁ v₂ : (QA b c)ˣ) (z : Fin 3 → QA b c) :
    triMul u₀ u₁ u₂ (triMul v₀ v₁ v₂ z) = triMul (u₀ * v₀) (u₁ * v₁) (u₂ * v₂) z := by
  funext i
  fin_cases i <;> simp [triMul_apply, mul_assoc]

theorem triMul_one_apply (z : Fin 3 → QA b c) : triMul 1 1 1 z = z := by
  funext i
  fin_cases i <;> simp [triMul_apply]

noncomputable abbrev Mu (b c : F) : Subgroup (QA b c)ˣ := rootsOfUnity (Nat.card F + 1) (QA b c)

@[expose] noncomputable def Tau (hb : b ≠ 0) :
    (↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) →* (OW F ≃ₗ[F] OW F) where
  toFun t := ((Tequiv (c := c) hb).trans (triMul (t.1 : (QA b c)ˣ) (t.2.1 : (QA b c)ˣ)
    (t.2.2 : (QA b c)ˣ))).trans (Tequiv (c := c) hb).symm
  map_one' := LinearEquiv.ext fun w => by
    simp only [LinearEquiv.trans_apply]
    have : (triMul (1 : (QA b c)ˣ) 1 1) (Tequiv (c := c) hb w) = Tequiv (c := c) hb w :=
      triMul_one_apply _
    simpa using congrArg (Tequiv (c := c) hb).symm this
  map_mul' t t' := LinearEquiv.ext fun w => by
    simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
    rw [triMul_mul_apply]
    rfl

theorem Tequiv_Tau (hb : b ≠ 0) (t : ↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) (w : OW F) :
    Tequiv (c := c) hb (Tau hb t w) = triMul (t.1 : (QA b c)ˣ) (t.2.1 : (QA b c)ˣ)
      (t.2.2 : (QA b c)ˣ) (Tequiv (c := c) hb w) := by
  show Tequiv (c := c) hb (((Tequiv (c := c) hb).trans (triMul _ _ _)).trans
    (Tequiv (c := c) hb).symm w) = _
  simp

theorem Tau_injective (hb : b ≠ 0) : Function.Injective (Tau (c := c) hb) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h : ∀ z : Fin 3 → QA b c, triMul (t.1 : (QA b c)ˣ) (t.2.1 : (QA b c)ˣ)
      (t.2.2 : (QA b c)ˣ) z = z := by
    intro z
    have h1 := Tequiv_Tau (c := c) hb t ((Tequiv (c := c) hb).symm z)
    rw [ht] at h1
    simpa using h1.symm
  have h0 := fun i => congrFun (h ![1, 1, 1]) i
  have e0 : (t.1 : (QA b c)ˣ) = 1 := Units.ext (by simpa [triMul_apply] using h0 0)
  have e1 : (t.2.1 : (QA b c)ˣ) = 1 := Units.ext (by simpa [triMul_apply] using h0 1)
  have e2 : (t.2.2 : (QA b c)ˣ) = 1 := Units.ext (by simpa [triMul_apply] using h0 2)
  exact Prod.ext (Subtype.ext e0) (Prod.ext (Subtype.ext e1) (Subtype.ext e2))

variable [Finite F] [CharP F 2] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem quad_Tau (hb : b ≠ 0) (t : ↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) (w : OW F) :
    quadMinus 3 F b c (Tau hb t w) = quadMinus 3 F b c w := by
  have hn : ∀ u : ↥(Mu b c), QuadraticAlgebra.norm ((u : (QA b c)ˣ) : QA b c) = 1 := by
    intro u
    apply norm_unit_of_pow_eq_one hb
    have := (mem_rootsOfUnity _ _).mp u.2
    simpa using congrArg Units.val this
  rw [quadMinus_eq_norm_sum hb, quadMinus_eq_norm_sum hb w]
  have h := Tequiv_Tau (c := c) hb t w
  have hT : ∀ i, Tfun b c (Tau hb t w) i = (triMul (t.1 : (QA b c)ˣ) (t.2.1 : (QA b c)ˣ)
      (t.2.2 : (QA b c)ˣ) (Tfun b c w)) i := fun i => congrFun h i
  rw [hT 0, hT 1, hT 2]
  simp [triMul_apply, hn]

@[expose] noncomputable def tauGL (hb : b ≠ 0) :
    (↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
  ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm.toMonoidHom).comp (Tau (c := c) hb)

theorem tauGL_mulVec (hb : b ≠ 0) (t : ↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) (x : OW F) :
    ((tauGL hb t : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
      Tau hb t x := by
  rw [← toLinEquiv_apply]
  simp [tauGL]

@[expose] noncomputable def shiftE : (Fin 3 → QA b c) ≃ₗ[F] (Fin 3 → QA b c) :=
  LinearEquiv.funCongrLeft F (QA b c) (Equiv.addRight (1 : Fin 3))

@[expose] noncomputable def sigmaLin (b c : F) (hb : b ≠ 0) : OW F ≃ₗ[F] OW F :=
  ((Tequiv (c := c) hb).trans shiftE).trans (Tequiv (c := c) hb).symm

theorem Tequiv_sigma (hb : b ≠ 0) (w : OW F) :
    Tequiv (c := c) hb (sigmaLin b c hb w) = shiftE (Tequiv (c := c) hb w) := by
  show Tequiv (c := c) hb (((Tequiv (c := c) hb).trans shiftE).trans
    (Tequiv (c := c) hb).symm w) = _
  simp

theorem sigmaLin_pow_three (hb : b ≠ 0) : sigmaLin b c hb ^ 3 = 1 := by
  refine LinearEquiv.ext fun w => ?_
  have h : ∀ z : Fin 3 → QA b c, shiftE (shiftE (shiftE z)) = z := by
    intro z
    funext i
    fin_cases i <;> rfl
  have e1 := Tequiv_sigma (c := c) hb w
  have e2 := Tequiv_sigma (c := c) hb (sigmaLin b c hb w)
  have e3 := Tequiv_sigma (c := c) hb (sigmaLin b c hb (sigmaLin b c hb w))
  apply (Tequiv (c := c) hb).injective
  rw [show (sigmaLin b c hb ^ 3) w = sigmaLin b c hb (sigmaLin b c hb (sigmaLin b c hb w)) from rfl,
    e3, e2, e1, h]
  rfl

theorem quad_sigma (hb : b ≠ 0) (w : OW F) :
    quadMinus 3 F b c (sigmaLin b c hb w) = quadMinus 3 F b c w := by
  rw [quadMinus_eq_norm_sum hb, quadMinus_eq_norm_sum hb w]
  have h := Tequiv_sigma (c := c) hb w
  have hT : ∀ i, Tfun b c (sigmaLin b c hb w) i = Tfun b c w (i + 1) := fun i => congrFun h i
  rw [hT 0, hT 1, hT 2]
  have e0 : (0 : Fin 3) + 1 = 1 := rfl
  have e1 : (1 : Fin 3) + 1 = 2 := rfl
  have e2 : (2 : Fin 3) + 1 = 0 := rfl
  rw [e0, e1, e2]
  ring

@[expose] noncomputable def sigmaGL (b c : F) (hb : b ≠ 0) :
    GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F :=
  (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm (sigmaLin b c hb)

theorem sigmaGL_mulVec (hb : b ≠ 0) (x : OW F) :
    ((sigmaGL b c hb : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x =
      sigmaLin b c hb x := by
  rw [← toLinEquiv_apply]
  simp [sigmaGL]

end Tori

structure NormModel (F : Type) [Field F] [Finite F] (b c : F) where
  E : Type
  [instField : Field E]
  [instAlgebra : Algebra F E]
  [instFinite : Finite E]
  card_E : Nat.card E = Nat.card F ^ 2
  T : OW F ≃ₗ[F] (Fin 3 → E)
  norm_eq : ∀ x : OW F,
    algebraMap F E (StatedQuadMinus 3 F b c x) = ∑ i, (T x i) ^ (Nat.card F + 1)
  τ : (↥(rootsOfUnity (Nat.card F + 1) E) × ↥(rootsOfUnity (Nat.card F + 1) E) ×
    ↥(rootsOfUnity (Nat.card F + 1) E)) →* GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F
  τ_injective : Function.Injective τ
  τ_mem : ∀ a, τ a ∈ StatedOmega (StatedQuadMinus 3 F b c)
  τ_apply : ∀ (a) (x : OW F),
    T (((τ a : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
      ![((a.1 : Eˣ) : E) * T x 0, ((a.2.1 : Eˣ) : E) * T x 1, ((a.2.2 : Eˣ) : E) * T x 2]
  σ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F
  σ_mem : σ ∈ StatedOmega (StatedQuadMinus 3 F b c)
  σ_pow : σ ^ 3 = 1
  σ_apply : ∀ x : OW F,
    T (((σ : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
      Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ x) =
      fun i => T x (i + 1)

attribute [instance] NormModel.instField NormModel.instAlgebra NormModel.instFinite

theorem nonempty_normModel [Finite F] [CharP F 2] {n : ℕ}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    Nonempty (NormModel F b c) := by
  have hb : b ≠ 0 := ne_zero_of_irred hirr
  haveI : Fact (∀ r : F, r ^ 2 ≠ -c + b * r) := factRoot hirr
  haveI : Finite (QA b c) := Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd (-c) b).symm
  have hodd : Odd (Nat.card F + 1) := by
    rw [hF]
    exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hquad : ∀ x : OW F, algebraMap F (QA b c) (StatedQuadMinus 3 F b c x) =
      ∑ i, (Tequiv (c := c) hb x i) ^ (Nat.card F + 1) := by
    intro x
    rw [← coe_quadMinus 3 F b c]
    show algebraMap F (QA b c) (quadMinus 3 F b c x) = _
    rw [quadMinus_eq_norm_sum hb, map_add, map_add, Fin.sum_univ_three]
    simp only [Tequiv_apply, pow_card_succ_eq_norm hb]
  have hτiso : ∀ (t : ↥(Mu b c) × ↥(Mu b c) × ↥(Mu b c)) (v : OW F),
      StatedQuadMinus 3 F b c (((tauGL hb t : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v) =
        StatedQuadMinus 3 F b c v := by
    intro t v
    rw [tauGL_mulVec, ← coe_quadMinus 3 F b c]
    exact quad_Tau hb t v
  have hσiso : ∀ v : OW F,
      StatedQuadMinus 3 F b c (((sigmaGL b c hb : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) *ᵥ v) =
        StatedQuadMinus 3 F b c v := by
    intro v
    rw [sigmaGL_mulVec, ← coe_quadMinus 3 F b c]
    exact quad_sigma hb v
  refine ⟨{ E := QA b c
            card_E := ?_
            T := Tequiv (c := c) hb
            norm_eq := hquad
            τ := tauGL hb
            τ_injective := ?_
            τ_mem := ?_
            τ_apply := ?_
            σ := sigmaGL b c hb
            σ_mem := ?_
            σ_pow := ?_
            σ_apply := ?_ }⟩
  · rw [Nat.card_congr (QuadraticAlgebra.equivProd (-c) b), Nat.card_prod, sq]
  · intro t t' h
    apply Tau_injective hb
    apply (toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm.injective
    exact h
  · intro t
    refine odd_isometry_mem_omega hirr (hτiso t) ?_
    have h1 : (tauGL hb t) ^ (Nat.card F + 1) = 1 := by
      rw [← map_pow]
      have : t ^ (Nat.card F + 1) = 1 := by
        refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · exact (mem_rootsOfUnity _ _).mp t.1.2
        · exact (mem_rootsOfUnity _ _).mp t.2.1.2
        · exact (mem_rootsOfUnity _ _).mp t.2.2.2
      rw [this, map_one]
    exact Odd.of_dvd_nat hodd (orderOf_dvd_of_pow_eq_one h1)
  · intro t x
    rw [tauGL_mulVec, Tequiv_Tau]
    rfl
  · refine odd_isometry_mem_omega hirr hσiso ?_
    have h1 : (sigmaGL b c hb) ^ 3 = 1 := by
      show ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm (sigmaLin b c hb)) ^ 3 = 1
      rw [← map_pow, sigmaLin_pow_three, map_one]
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h1)
  · show ((toLinEquiv (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).symm (sigmaLin b c hb)) ^ 3 = 1
    rw [← map_pow, sigmaLin_pow_three, map_one]
  · intro x
    rw [sigmaGL_mulVec]
    exact funext fun i => congrFun (Tequiv_sigma (c := c) hb x) i

end CFSG.LocalAnalysis.RankThreeUC
