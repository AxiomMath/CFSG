module

public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic
public import CFSG.ClassicalInvolution.WeakCT.TorusAgree

public section

namespace CFSG.ClassicalInvolution.Models.TwistedPairs

open CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

section FixedField

variable {E : Type} [Field E] (θ : E →+* E)

@[expose] def fixedField : Subfield E := RingHom.eqLocusField θ (RingHom.id E)

theorem mem_fixedField {c : E} : c ∈ fixedField θ ↔ θ c = c := Iff.rfl

@[expose] def involEquiv (hθ : ∀ c, θ (θ c) = c) : E ≃+* E where
  toFun := θ
  invFun := θ
  left_inv := hθ
  right_inv := hθ
  map_mul' := map_mul θ
  map_add' := map_add θ

theorem involEquiv_apply (hθ : ∀ c, θ (θ c) = c) (c : E) : involEquiv θ hθ c = θ c := rfl

end FixedField

section Sigma

variable {E : Type} [Field E]

@[expose] def unitaryJ : Matrix (Fin 4) (Fin 4) E :=
  !![0, 0, 0, -1; 0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0]

@[expose] def unitaryJInv : Matrix (Fin 4) (Fin 4) E :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; -1, 0, 0, 0]

theorem unitaryJ_mul : (unitaryJ : Matrix (Fin 4) (Fin 4) E) * unitaryJInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryJ, unitaryJInv, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def sigmaA (ψ : E ≃+* E) : SL(4, E) ≃* SL(4, E) :=
  (fieldAutSL ψ 4).trans ((invTransposeSL 4).trans (conjSL unitaryJ unitaryJInv unitaryJ_mul))

theorem coe_blockSL_four_zero (A : SL(2, E)) :
    ((blockSL E 4 2 0 (by omega) A : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem coe_blockSL_four_one (A : SL(2, E)) :
    ((blockSL E 4 2 1 (by omega) A : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      !![1, 0, 0, 0; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; 0, 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem coe_blockSL_four_two (A : SL(2, E)) :
    ((blockSL E 4 2 2 (by omega) A : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem coe_invTransposeSL_two (M : SL(2, E)) :
    ((invTransposeSL 2 M : SL(2, E)) : Matrix (Fin 2) (Fin 2) E) =
      !![M 1 1, -M 1 0; -M 0 1, M 0 0] := by
  rw [coe_invTransposeSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem sigmaA_blockSL2_zero (ψ : E ≃+* E) (A : SL(2, E)) :
    sigmaA ψ (blockSL2 E 3 0 A) = blockSL2 E 3 2 (fieldAutSL ψ 2 A) := by
  show conjSL unitaryJ unitaryJInv unitaryJ_mul
    (invTransposeSL 4 (fieldAutSL ψ 4 (blockSL E 4 2 0 (by omega) A))) =
      blockSL E 4 2 2 (by omega) (fieldAutSL ψ 2 A)
  rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
  generalize fieldAutSL ψ 2 A = M
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_blockSL_four_zero, coe_blockSL_four_two, coe_invTransposeSL_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [unitaryJ, unitaryJInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem sigmaA_blockSL2_one (ψ : E ≃+* E) (A : SL(2, E)) :
    sigmaA ψ (blockSL2 E 3 1 A) = blockSL2 E 3 1 (fieldAutSL ψ 2 A) := by
  show conjSL unitaryJ unitaryJInv unitaryJ_mul
    (invTransposeSL 4 (fieldAutSL ψ 4 (blockSL E 4 2 1 (by omega) A))) =
      blockSL E 4 2 1 (by omega) (fieldAutSL ψ 2 A)
  rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
  generalize fieldAutSL ψ 2 A = M
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_blockSL_four_one, coe_blockSL_four_one, coe_invTransposeSL_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [unitaryJ, unitaryJInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem sigmaA_blockSL2_two (ψ : E ≃+* E) (A : SL(2, E)) :
    sigmaA ψ (blockSL2 E 3 2 A) = blockSL2 E 3 0 (fieldAutSL ψ 2 A) := by
  show conjSL unitaryJ unitaryJInv unitaryJ_mul
    (invTransposeSL 4 (fieldAutSL ψ 4 (blockSL E 4 2 2 (by omega) A))) =
      blockSL E 4 2 0 (by omega) (fieldAutSL ψ 2 A)
  rw [fieldAutSL_blockSL, invTransposeSL_blockSL]
  generalize fieldAutSL ψ 2 A = M
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_blockSL_four_two, coe_blockSL_four_zero, coe_invTransposeSL_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [unitaryJ, unitaryJInv, Matrix.mul_apply, Fin.sum_univ_four]

theorem fieldAutSL_fieldAutSL (ψ : E ≃+* E) (hψ : ∀ c, ψ (ψ c) = c) (d : ℕ) (A : SL(d, E)) :
    fieldAutSL ψ d (fieldAutSL ψ d A) = A :=
  Subtype.ext (Matrix.ext fun _ _ => hψ _)

end Sigma

section Group

variable {E : Type} [Field E] (θ : E →+* E) (hθ : ∀ c, θ (θ c) = c)

@[expose] def unitaryGroup : Subgroup SL(4, E) :=
  MonoidHom.eqLocus (sigmaA (involEquiv θ hθ)).toMonoidHom (MonoidHom.id _)

theorem mem_unitaryGroup {g : SL(4, E)} :
    g ∈ unitaryGroup θ hθ ↔ sigmaA (involEquiv θ hθ) g = g :=
  Iff.rfl

@[expose] def liftSL (d : ℕ) : SL(d, fixedField θ) →* SL(d, E) :=
  Matrix.SpecialLinearGroup.map (fixedField θ).subtype

theorem liftSL_injective (d : ℕ) : Function.Injective (liftSL θ d) := by
  intro A B h
  have := congrArg (fun M : SL(d, E) => (M : Matrix (Fin d) (Fin d) E)) h
  refine Subtype.ext (Matrix.ext fun i j => Subtype.ext ?_)
  exact congrFun (congrFun this i) j

theorem coe_liftSL (d : ℕ) (A : SL(d, fixedField θ)) (i j : Fin d) :
    ((liftSL θ d A : SL(d, E)) : Matrix (Fin d) (Fin d) E) i j = ((A i j : fixedField θ) : E) :=
  rfl

theorem map_liftSL (d : ℕ) (A : SL(d, fixedField θ)) :
    Matrix.SpecialLinearGroup.map θ (liftSL θ d A) = liftSL θ d A :=
  Subtype.ext (Matrix.ext fun i j => (A i j).2)

theorem fieldAutSL_liftSL (d : ℕ) (A : SL(d, fixedField θ)) :
    fieldAutSL (involEquiv θ hθ) d (liftSL θ d A) = liftSL θ d A :=
  map_liftSL θ d A

@[expose] def usbSL : SL(2, E) →* SL(4, E) :=
  ((blockSL2 E 3 0).noncommCoprod (blockSL2 E 3 2)
    (fun a b => blockSL2_comm 3 0 2 (by decide) a b)).comp
    ((MonoidHom.id _).prod (fieldAutSL (involEquiv θ hθ) 2).toMonoidHom)

theorem usbSL_apply (B : SL(2, E)) :
    usbSL θ hθ B = blockSL2 E 3 0 B * blockSL2 E 3 2 (fieldAutSL (involEquiv θ hθ) 2 B) :=
  rfl

theorem coe_usbSL (B : SL(2, E)) :
    ((usbSL θ hθ B : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      !![B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0; 0, 0, θ (B 0 0), θ (B 0 1);
        0, 0, θ (B 1 0), θ (B 1 1)] := by
  rw [usbSL_apply, Matrix.SpecialLinearGroup.coe_mul]
  change (blockSL E 4 2 0 (by omega) B : Matrix (Fin 4) (Fin 4) E) *
    (blockSL E 4 2 2 (by omega) (fieldAutSL (involEquiv θ hθ) 2 B) : Matrix (Fin 4) (Fin 4) E) = _
  rw [coe_blockSL_four_zero, coe_blockSL_four_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, coe_fieldAutSL, involEquiv_apply]

theorem usbSL_mem (B : SL(2, E)) : usbSL θ hθ B ∈ unitaryGroup θ hθ := by
  rw [mem_unitaryGroup, usbSL_apply, map_mul, sigmaA_blockSL2_zero, sigmaA_blockSL2_two,
    fieldAutSL_fieldAutSL _ (hθ) 2 B]
  exact (blockSL2_comm 3 0 2 (by decide) _ _).symm

@[expose] def ulbSL : SL(2, fixedField θ) →* SL(4, E) :=
  (blockSL2 E 3 1).comp (liftSL θ 2)

theorem ulbSL_mem (A : SL(2, fixedField θ)) : ulbSL θ A ∈ unitaryGroup θ hθ := by
  rw [mem_unitaryGroup]
  change sigmaA (involEquiv θ hθ) (blockSL2 E 3 1 (liftSL θ 2 A)) = blockSL2 E 3 1 (liftSL θ 2 A)
  rw [sigmaA_blockSL2_one, fieldAutSL_liftSL θ hθ]

@[expose] def ulb : SL(2, fixedField θ) →* unitaryGroup θ hθ :=
  (ulbSL θ).codRestrict (unitaryGroup θ hθ) (ulbSL_mem θ hθ)

@[expose] def usb : SL(2, E) →* unitaryGroup θ hθ :=
  (usbSL θ hθ).codRestrict (unitaryGroup θ hθ) (usbSL_mem θ hθ)

theorem coe_ulb (A : SL(2, fixedField θ)) : ((ulb θ hθ A : unitaryGroup θ hθ) : SL(4, E)) =
    blockSL2 E 3 1 (liftSL θ 2 A) :=
  rfl

theorem coe_usb (B : SL(2, E)) : ((usb θ hθ B : unitaryGroup θ hθ) : SL(4, E)) = usbSL θ hθ B :=
  rfl

theorem ulb_injective : Function.Injective (ulb θ hθ) := by
  intro A B h
  have h' : blockSL2 E 3 1 (liftSL θ 2 A) = blockSL2 E 3 1 (liftSL θ 2 B) :=
    congrArg Subtype.val h
  exact liftSL_injective θ 2 (blockSL2_injective 3 1 h')

theorem usb_injective : Function.Injective (usb θ hθ) := by
  intro A B h
  have h' : usbSL θ hθ A = usbSL θ hθ B := congrArg Subtype.val h
  have h0 : blockSL2 E 3 0 A = blockSL2 E 3 0 B := by
    have := congrArg (fun g : SL(4, E) => (g : Matrix (Fin 4) (Fin 4) E)) h'
    rw [coe_usbSL, coe_usbSL] at this
    refine Subtype.ext ?_
    change ((blockSL E 4 2 0 (by omega) A : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) =
      ((blockSL E 4 2 0 (by omega) B : SL(4, E)) : Matrix (Fin 4) (Fin 4) E)
    rw [coe_blockSL_four_zero, coe_blockSL_four_zero]
    ext a b
    have := congrFun (congrFun this a) b
    fin_cases a <;> fin_cases b <;> simp_all
  exact blockSL2_injective 3 0 h0

theorem usbSL_torusHom_conj (t : Eˣ) (M : SL(2, E)) :
    usbSL θ hθ (torusHom E t) * blockSL2 E 3 1 M * (usbSL θ hθ (torusHom E t))⁻¹ =
      blockSL2 E 3 1 (diagConj2 (t * Units.map (θ : E →* E) t)⁻¹ 1 M) := by
  have hinv : (usbSL θ hθ (torusHom E t))⁻¹ = usbSL θ hθ (torusHom E t⁻¹) := by
    rw [← map_inv, ← map_inv]
  rw [hinv]
  have ht : (t : E) ≠ 0 := t.ne_zero
  have ht' : θ (t : E) ≠ 0 := fun h => ht ((map_eq_zero θ).1 h)
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_usbSL, coe_usbSL]
  change _ * ((blockSL E 4 2 1 (by omega) M : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) * _ =
    ((blockSL E 4 2 1 (by omega) (diagConj2 (t * Units.map (θ : E →* E) t)⁻¹ 1 M) : SL(4, E)) :
      Matrix (Fin 4) (Fin 4) E)
  rw [coe_blockSL_four_one, coe_blockSL_four_one, coe_diagConj2]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, coe_torusHom,
      Matrix.diagonal_apply, Units.val_inv_eq_inv_val] <;> field_simp

theorem blockSL2_one_torusHom_conj_usbSL (s : Eˣ) (hs : θ (s : E) = s) (B : SL(2, E)) :
    blockSL2 E 3 1 (torusHom E s) * usbSL θ hθ B * (blockSL2 E 3 1 (torusHom E s))⁻¹ =
      usbSL θ hθ (diagConj2 s⁻¹ 1 B) := by
  have hinv : (blockSL2 E 3 1 (torusHom E s))⁻¹ = blockSL2 E 3 1 (torusHom E s⁻¹) := by
    rw [← map_inv, ← map_inv]
  rw [hinv]
  have hs0 : (s : E) ≠ 0 := s.ne_zero
  have hs' : θ (((s⁻¹ : Eˣ)) : E) = ((s⁻¹ : Eˣ) : E) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs]
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_usbSL, coe_usbSL]
  change ((blockSL E 4 2 1 (by omega) (torusHom E s) : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) * _ *
    ((blockSL E 4 2 1 (by omega) (torusHom E s⁻¹) : SL(4, E)) : Matrix (Fin 4) (Fin 4) E) = _
  rw [coe_blockSL_four_one, coe_blockSL_four_one]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, coe_torusHom, coe_diagConj2,
      Matrix.diagonal_apply, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hs] <;> field_simp

@[expose] def unitaryNu (t : Eˣ) : (fixedField θ)ˣ :=
  Units.mk0 ⟨((t : E) * θ t)⁻¹, by
    show θ (((t : E) * θ t)⁻¹) = ((t : E) * θ t)⁻¹
    rw [map_inv₀, map_mul, hθ, mul_comm]⟩
    (fun h => by
      have h' : ((t : E) * θ t)⁻¹ = 0 := congrArg Subtype.val h
      have ht : (t : E) ≠ 0 := t.ne_zero
      have ht' : θ (t : E) ≠ 0 := fun h0 => ht ((map_eq_zero θ).1 h0)
      exact (inv_ne_zero (mul_ne_zero ht ht')) h')

theorem coe_unitaryNu (t : Eˣ) :
    (Units.map (fixedField θ).subtype.toMonoidHom (unitaryNu θ hθ t) : Eˣ) =
      (t * Units.map (θ : E →* E) t)⁻¹ :=
  Units.ext (by simp [unitaryNu, Units.val_inv_eq_inv_val])

@[expose] def unitaryMu (s : (fixedField θ)ˣ) : Eˣ :=
  Units.map (fixedField θ).subtype.toMonoidHom s⁻¹

theorem liftSL_diagConj2 (ν : (fixedField θ)ˣ) (A : SL(2, fixedField θ)) :
    liftSL θ 2 (diagConj2 ν 1 A) =
      diagConj2 (Units.map (fixedField θ).subtype.toMonoidHom ν) 1 (liftSL θ 2 A) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [coe_diagConj2]
  show (((diagConj2 ν 1 A : SL(2, fixedField θ)) i j : fixedField θ) : E) = _
  rw [coe_diagConj2]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, coe_liftSL]

theorem liftSL_torusHom (s : (fixedField θ)ˣ) :
    liftSL θ 2 (torusHom (fixedField θ) s) =
      torusHom E (Units.map (fixedField θ).subtype.toMonoidHom s) := by
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [coe_torusHom]
  fin_cases i <;> fin_cases j <;> simp [coe_torusHom, coe_liftSL]

@[expose] def unitaryModel : TwistedB2Model (fixedField θ) E (unitaryGroup θ hθ) where
  lb := ulb θ hθ
  sb := usb θ hθ
  nu := unitaryNu θ hθ
  mu := unitaryMu θ
  conj_sl t A := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ulb, coe_usb]
    rw [usbSL_torusHom_conj, liftSL_diagConj2, coe_unitaryNu]
  conj_ls s B := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ulb, coe_usb]
    rw [liftSL_torusHom, blockSL2_one_torusHom_conj_usbSL θ hθ
      (Units.map (fixedField θ).subtype.toMonoidHom s) s.val.property, unitaryMu, map_inv]

theorem exists_unitaryNu_ne [Finite E] (hF : 4 ≤ Nat.card (fixedField θ)) :
    ∃ t, (unitaryModel θ hθ).nu t ≠ 1 := by
  obtain ⟨r, hr⟩ := exists_unit_sq_ne_one (K := fixedField θ) hF
  refine ⟨Units.map (fixedField θ).subtype.toMonoidHom r, fun h => hr ?_⟩
  have h1 : ((((Units.map (fixedField θ).subtype.toMonoidHom r : Eˣ) : E)) *
      θ ((Units.map (fixedField θ).subtype.toMonoidHom r : Eˣ) : E))⁻¹ = 1 :=
    congrArg (fun u : (fixedField θ)ˣ => ((u : fixedField θ) : E)) h
  have hfix : θ ((Units.map (fixedField θ).subtype.toMonoidHom r : Eˣ) : E) =
      ((Units.map (fixedField θ).subtype.toMonoidHom r : Eˣ) : E) := r.val.property
  rw [hfix] at h1
  have h2 := inv_eq_one.1 h1
  refine Units.ext (Subtype.ext ?_)
  simpa [sq] using h2

theorem exists_unitaryMu_ne [Finite E] (hF : 3 ≤ Nat.card (fixedField θ)) :
    ∃ s, (unitaryModel θ hθ).mu s ≠ 1 := by
  obtain ⟨s, hs⟩ := exists_unit_ne_one (K := fixedField θ) hF
  refine ⟨s, fun h => hs ?_⟩
  have h1 : Units.map (fixedField θ).subtype.toMonoidHom s⁻¹ =
      Units.map (fixedField θ).subtype.toMonoidHom 1 := by rw [map_one]; exact h
  exact inv_eq_one.1 (Units.map_injective (fixedField θ).subtype.injective h1)

@[expose] def UnitaryB2BlockStandardPair {X : Type} [Group X] (W U V : Subgroup X) : Prop :=
  (unitaryModel θ hθ).StandardPair W U V

end Group

end CFSG.ClassicalInvolution.Models.TwistedPairs
