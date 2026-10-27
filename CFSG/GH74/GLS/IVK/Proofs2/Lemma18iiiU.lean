module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvections

public section

open scoped MatrixGroups

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma18iii

namespace UnipPair

section Conjugation

variable {F : Type} [Field F]

@[expose] def conjSL (h : GL (Fin 2) F) : SL(2, F) →* SL(2, F) where
  toFun A := ⟨(h : Matrix (Fin 2) (Fin 2) F) * A * (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, h.mul_inv,
      Matrix.det_one]⟩
  map_one' := Subtype.ext <| by
    change (h : Matrix (Fin 2) (Fin 2) F) * 1 * (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.mul_one]
    exact h.mul_inv
  map_mul' A B := Subtype.ext <| by
    change (h : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) * B) *
        (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * A * (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F) *
        ((h : Matrix (Fin 2) (Fin 2) F) * B * (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F))
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F) (h : Matrix (Fin 2) (Fin 2) F),
      h.inv_mul, Matrix.one_mul]

theorem coe_conjSL (h : GL (Fin 2) F) (A : SL(2, F)) :
    ((conjSL h A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * A * (↑h⁻¹ : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem conjSL_inv_conjSL (h : GL (Fin 2) F) (A : SL(2, F)) : conjSL h⁻¹ (conjSL h A) = A := by
  apply Subtype.ext
  rw [coe_conjSL, coe_conjSL, inv_inv]
  simp [Matrix.mul_assoc]

theorem conjSL_injective (h : GL (Fin 2) F) : Function.Injective (conjSL h) :=
  Function.LeftInverse.injective (conjSL_inv_conjSL h)

theorem conjSL_neg (h : GL (Fin 2) F) (A : SL(2, F)) : conjSL h (-A) = -conjSL h A := by
  apply Subtype.ext
  rw [coe_conjSL, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_neg,
    coe_conjSL, Matrix.mul_neg, Matrix.neg_mul]

end Conjugation

section Embedding

variable {K F : Type} [Field K] [Field F] (f : K →+* F)

theorem coe_map (A : SL(2, K)) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.map f A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      f ((A : Matrix (Fin 2) (Fin 2) K) i j) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_neg_SL (A : SL(2, K)) :
    Matrix.SpecialLinearGroup.map f (-A) = -Matrix.SpecialLinearGroup.map f A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, coe_map, map_neg]

theorem map_injective_SL :
    Function.Injective (Matrix.SpecialLinearGroup.map f : SL(2, K) →* SL(2, F)) := by
  intro A B hAB
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F) i j) hAB
  simp only [coe_map] at h
  exact f.injective h

theorem coe_map_unip (t : K) :
    (Matrix.SpecialLinearGroup.map f (CFSG.PSL2Table.unip t) : Matrix (Fin 2) (Fin 2) F) =
      !![1, f t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_map]

end Embedding

section Kernel

variable {F : Type} [Field F] {K : Type} [Field K]

theorem ker_comp_mk (ψ : SL(2, K) →* SL(2, F)) (hψ : Function.Injective ψ) (hneg : ψ (-1) = -1) :
    ((CFSG.PSL2Table.mk : SL(2, F) →* PSL(2, F)).comp ψ).ker = Subgroup.center SL(2, K) := by
  ext X
  have h1 : ψ X = 1 ↔ X = 1 := by
    rw [← map_one ψ]
    exact hψ.eq_iff
  have h2 : ψ X = -1 ↔ X = -1 := by
    rw [← hneg]
    exact hψ.eq_iff
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, CFSG.PSL2Table.mk_eq_one_iff, h1, h2,
    CFSG.PSL2Table.mem_center_SL_iff]

end Kernel

section Generation

variable (K : Type) [Field K]

@[expose] def lower : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

variable {K}

theorem coe_lower : (lower K : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] := rfl

theorem weyl_mul_unip : CFSG.PSL2Table.weyl * CFSG.PSL2Table.unip (-1 : K) =
    lower K * CFSG.PSL2Table.weyl := by
  apply CFSG.PSL2Table.SL_ext <;> simp [CFSG.PSL2Table.mul_apply_SL, coe_lower]

theorem closure_unip_lower (p : ℕ) [Fact p.Prime] :
    Subgroup.closure ({CFSG.PSL2Table.unip (-1 : ZMod p), lower (ZMod p)} :
      Set SL(2, ZMod p)) = ⊤ := by
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  exact CFSG.Glauberman.Dickson.standard_two_transvections_generate_of_finrank_one (p := p)
    (K := ZMod p) (-1) (neg_ne_zero.mpr h1) (Module.finrank_self (ZMod p))

end Generation

theorem closure_pair_equiv {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (φ : SL(2, ZMod p) →* G)
    (hker : φ.ker = Subgroup.center SL(2, ZMod p)) (a : G)
    (ha : φ (CFSG.PSL2Table.unip (-1 : ZMod p)) = a) :
    Nonempty (↥(Subgroup.closure ({a, φ CFSG.PSL2Table.weyl * a * (φ CFSG.PSL2Table.weyl)⁻¹} :
      Set G)) ≃* PSL(2, ZMod p)) := by
  subst ha
  have hW : (CFSG.PSL2Table.weyl : SL(2, ZMod p)) * CFSG.PSL2Table.unip (-1 : ZMod p) *
      CFSG.PSL2Table.weyl⁻¹ = lower (ZMod p) :=
    mul_inv_eq_iff_eq_mul.mpr weyl_mul_unip
  have hL : φ CFSG.PSL2Table.weyl * φ (CFSG.PSL2Table.unip (-1 : ZMod p)) *
      (φ CFSG.PSL2Table.weyl)⁻¹ = φ (lower (ZMod p)) := by
    rw [← hW, map_mul, map_mul, map_inv]
  have hcl : Subgroup.closure ({φ (CFSG.PSL2Table.unip (-1 : ZMod p)),
      φ CFSG.PSL2Table.weyl * φ (CFSG.PSL2Table.unip (-1 : ZMod p)) *
        (φ CFSG.PSL2Table.weyl)⁻¹} : Set G) = φ.range := by
    rw [hL, ← Set.image_pair, ← MonoidHom.map_closure, closure_unip_lower,
      ← MonoidHom.range_eq_map]
  exact ⟨(MulEquiv.subgroupCongr hcl).trans ((QuotientGroup.quotientKerEquivRange φ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker))⟩

section Intertwiner

variable {F : Type} [Field F]

theorem exists_intertwiner (Y : SL(2, F)) (hY1 : Y ≠ 1)
    (hY : (Y : Matrix (Fin 2) (Fin 2) F).trace = 2) :
    ∃ h : GL (Fin 2) F, (Y : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * !![1, -1; 0, 1] := by
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : F, (Y : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have h := Y.2
    rwa [hm, Matrix.det_fin_two_of] at h
  have htr : a + d = 2 := by
    rwa [hm, Matrix.trace_fin_two_of] at hY
  by_cases hc : c = 0
  · have ha : a = 1 := by
      have h2 : (a - 1) ^ 2 = 0 := by linear_combination (-1 : F) * hdet + a * htr - b * hc
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hd : d = 1 := by linear_combination htr - ha
    have hb : b ≠ 0 := by
      intro hb0
      apply hY1
      apply Subtype.ext
      rw [hm, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two, ha, hb0, hc, hd]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![-b, 0; 0, 1] ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using hb
    · rw [hm, ha, hc, hd]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![1 - a, 1; -c, 0] ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using hc
    · rw [hm]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination hdet - a * htr
      · linear_combination (-c) * htr

end Intertwiner

end UnipPair

end Lemma18iii

open Lemma18iii.UnipPair in
theorem unipotent_closure_pair {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (_hp2 : p ≠ 2) (Y : SL(2, F)) (hY1 : Y ≠ 1)
    (hY : (Y : Matrix (Fin 2) (Fin 2) F).trace = 2) :
    ∃ g : PSL(2, F), Nonempty
      (Subgroup.closure ({CFSG.PSL2Table.mk Y, g * CFSG.PSL2Table.mk Y * g⁻¹} :
        Set (PSL(2, F))) ≃* PSL(2, ZMod p)) := by
  obtain ⟨h, hh⟩ := exists_intertwiner Y hY1 hY
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  let ψ : SL(2, ZMod p) →* SL(2, F) := (conjSL h).comp (Matrix.SpecialLinearGroup.map f)
  let φ : SL(2, ZMod p) →* PSL(2, F) := CFSG.PSL2Table.mk.comp ψ
  have hψinj : Function.Injective ψ := (conjSL_injective h).comp (map_injective_SL f)
  have hψneg : ψ (-1) = -1 := by
    change conjSL h (Matrix.SpecialLinearGroup.map f (-1)) = -1
    rw [map_neg_SL, map_one, conjSL_neg, map_one]
  have hf : f (-1 : ZMod p) = -1 := (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  have hcoe : (Matrix.SpecialLinearGroup.map f (CFSG.PSL2Table.unip (-1 : ZMod p)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, -1; 0, 1] := by
    rw [coe_map_unip, hf]
  have hψU : conjSL h (Matrix.SpecialLinearGroup.map f (CFSG.PSL2Table.unip (-1 : ZMod p))) =
      Y := by
    apply Subtype.ext
    rw [coe_conjSL, hcoe, ← hh]
    exact Units.mul_inv_cancel_right _ h
  exact ⟨φ CFSG.PSL2Table.weyl, closure_pair_equiv φ (ker_comp_mk ψ hψinj hψneg) _
    (congrArg CFSG.PSL2Table.mk hψU)⟩

end CFSG.GH74.GLS.IVK.Proofs2
