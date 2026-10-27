module

public import CFSG.LieType.SpinGeom.AtE0
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Transport

variable {K : Type} [Field K]

@[expose] def pullW {C : Type} [AddCommGroup C] (g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
    (W : AddSubgroup ((Fin (2 * 4) → K) × C)) : AddSubgroup ((Fin (2 * 4) → K) × C) where
  carrier := {w | (g *ᵥ w.1, w.2) ∈ W}
  zero_mem' := by
    show (g *ᵥ (0 : Fin (2 * 4) → K), (0 : C)) ∈ W
    rw [Matrix.mulVec_zero]
    exact W.zero_mem
  add_mem' := fun {a b} ha hb => by
    have := W.add_mem ha hb
    simpa [Matrix.mulVec_add] using this
  neg_mem' := fun {a} ha => by
    have := W.neg_mem ha
    simpa [Matrix.mulVec_neg] using this


theorem card_pullW {C : Type} [AddCommGroup C] {g gi : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K}
    (h1 : ∀ v, gi *ᵥ (g *ᵥ v) = v) (h2 : ∀ v, g *ᵥ (gi *ᵥ v) = v)
    (W : AddSubgroup ((Fin (2 * 4) → K) × C)) : Nat.card (pullW g W) = Nat.card W := by
  let eV : (Fin (2 * 4) → K) ≃ (Fin (2 * 4) → K) := ⟨fun v => g *ᵥ v, fun v => gi *ᵥ v, h1, h2⟩
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.prodCongr eV (Equiv.refl C)) fun w => Iff.rfl)

end Transport

section Reduce

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem om8_inv_mulVec (h : Om8 K) (v : Fin (2 * 4) → K) :
    (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      ((((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec]
  have : ((h⁻¹ * h : Om8 K) : GL (Fin (2 * 4)) K) = 1 := by rw [inv_mul_cancel]; rfl
  have e := congrArg (fun u : GL (Fin (2 * 4)) K => (u : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K))
    this
  simp only [Units.val_one] at e
  rw [show (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
    (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 from e,
    Matrix.one_mulVec]


omit [Finite K] [CharP K 2] in
theorem om8_mulVec_inv (h : Om8 K) (v : Fin (2 * 4) → K) :
    (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      ((((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
      v := by
  have := om8_inv_mulVec h⁻¹ v
  rwa [inv_inv] at this

omit [Finite K] [CharP K 2] in
theorem polar_mulVec_om8 (h : Om8 K) (x y : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K)
        ((((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x)
        ((((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y) =
      polar (coordinateQuadPlus 4 K) x y := by
  simp only [QuadraticMap.polar, ← Matrix.mulVec_add, coordinateQuadPlus_mulVec_om8]


theorem spinGeom_false_of_transitive (hq : 4 ≤ Nat.card K)
    (hTrans : ∀ b : Fin (2 * 4) → K, b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
      ∃ h ∈ spinSeven K,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = b)
    (s : ℕ) (QC : QuadraticForm K (Fin (2 * s) → K)) (b : Fin (2 * 4) → K)
    (hb0 : b ≠ 0) (hbQ : coordinateQuadPlus 4 K b = 0)
    (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
    (A : Subgroup (GL (Fin (2 * 4)) K))
    (hA : A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype)
    (hAfix : ∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b)
    (h3 : ∀ t : K, (t • b, (0 : Fin (2 * s) → K)) ∈ W)
    (h4 : ∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0)
    (h5 : ∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 b = 0)
    (h6 : ∀ M ∈ spinSeven K, Odd (orderOf M) →
      ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b →
      (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
        w.2) ∈ W) ∧
      ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A)
    (h7 : ∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x b = 0 →
      ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W)
    (h8 : ∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
      (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • b)
    (h9 : ∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
      ∃ t : K, w = (t • b, 0))
    (hcount : Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s)) : False := by
  obtain ⟨h, hh, hhb⟩ := hTrans b hb0 hbQ
  have hgi := om8_inv_mulVec h
  have hg := om8_mulVec_inv h
  set g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
    ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) with hg_def
  set gi : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
    (((h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) with hgi_def
  set hG : GL (Fin (2 * 4)) K := (h : GL (Fin (2 * 4)) K) with hG_def
  have hiB : gi *ᵥ b = frameE K 0 := by rw [← hhb, hgi]
  have hact : ∀ (a : GL (Fin (2 * 4)) K) (x : Fin (2 * 4) → K),
      ((hG⁻¹ * a * hG : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x =
        gi *ᵥ ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (g *ᵥ x)) := by
    intro a x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rfl
  have hga : ∀ (a : GL (Fin (2 * 4)) K) (x : Fin (2 * 4) → K),
      g *ᵥ (((hG⁻¹ * a * hG : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x) =
        (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (g *ᵥ x) := by
    intro a x
    rw [hact, hg]
  refine spinGeom_atE0 hq hTrans s QC (pullW g W) (A.map (MulAut.conj hG).symm.toMonoidHom)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
    obtain ⟨M₁, hM₁, hM₁a⟩ := Subgroup.mem_map.1 (hA ha)
    refine Subgroup.mem_map.2 ⟨h⁻¹ * M₁ * h, mul_mem (mul_mem (inv_mem hh) hM₁) hh, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, ← hM₁a]
    rfl
  ·
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, hact, hhb, hAfix a ha, hiB]
  ·
    intro t
    show (g *ᵥ (t • frameE K 0), (0 : Fin (2 * s) → K)) ∈ W
    rw [Matrix.mulVec_smul, hhb]
    exact h3 t
  ·
    intro w hw
    have := h4 _ hw
    rwa [coordinateQuadPlus_mulVec_om8] at this
  ·
    intro w hw
    have := h5 _ hw
    rwa [← hhb, polar_mulVec_om8] at this
  ·
    intro M hM hodd hMfix
    have hM'mem : h * M * h⁻¹ ∈ spinSeven K := mul_mem (mul_mem hh hM) (inv_mem hh)
    have hM'odd : Odd (orderOf (h * M * h⁻¹)) := by
      have hs : SemiconjBy h M (h * M * h⁻¹) := by
        unfold SemiconjBy
        simp [mul_assoc]
      rwa [← hs.orderOf_eq]
    have hM'mat : ∀ x : Fin (2 * 4) → K,
        (((h * M * h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          x = g *ᵥ ((((M : Om8 K) : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (gi *ᵥ x)) := by
      intro x
      simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
    have hM'b : (((h * M * h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b := by
      rw [hM'mat, hiB, hMfix, hhb]
    obtain ⟨hW, hAA⟩ := h6 _ hM'mem hM'odd hM'b
    refine ⟨fun w hw => ?_, fun a' ha' => ?_⟩
    · show (g *ᵥ ((((M : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1), w.2) ∈ W
      have := hW _ hw
      rwa [hM'mat, hgi] at this
    · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
      refine Subgroup.mem_map.2 ⟨((h * M * h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) * a *
        ((h * M * h⁻¹ : Om8 K) : GL (Fin (2 * 4)) K)⁻¹, hAA a ha, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [← hG_def]
      group
  ·
    intro a' ha' x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
    have hpol : polar (coordinateQuadPlus 4 K) (g *ᵥ x) b = 0 := by
      rw [← hhb, polar_mulVec_om8]
      exact hx
    have := h7 a ha _ hpol
    show (g *ᵥ ((((MulAut.conj hG).symm a : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x), (0 : Fin (2 * s) → K)) ∈ W
    rw [MulAut.conj_symm_apply, Matrix.mulVec_sub, hga]
    exact this
  ·
    intro a' ha' w hw
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ha'
    obtain ⟨t, ht⟩ := h8 a ha _ hw
    refine ⟨t, ?_⟩
    have e : ((((MulAut.conj hG).symm.toMonoidHom a : GL (Fin (2 * 4)) K)) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 =
        gi *ᵥ ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (g *ᵥ w.1) - g *ᵥ w.1) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, hact, Matrix.mulVec_sub, hgi]
    rw [e, ht, Matrix.mulVec_smul, hiB]
  ·
    intro w hw hfix
    obtain ⟨t, ht⟩ := h9 _ hw fun a ha => by
      have h1 := hfix _ (Subgroup.mem_map.2 ⟨a, ha, rfl⟩)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, hact] at h1
      calc (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (g *ᵥ w.1) =
          g *ᵥ (gi *ᵥ ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ (g *ᵥ w.1))) := (hg _).symm
        _ = _ := by rw [h1]
    refine ⟨t, Prod.ext ?_ (Prod.ext_iff.1 ht).2⟩
    have h1 : g *ᵥ w.1 = t • b := (Prod.ext_iff.1 ht).1
    calc w.1 = gi *ᵥ (g *ᵥ w.1) := (hgi _).symm
      _ = t • frameE K 0 := by rw [h1, Matrix.mulVec_smul, hiB]
  ·
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_pullW hgi hg]
    exact hcount


theorem spinGeom_of_transitive
    (hTrans : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b : Fin (2 * 4) → K), b ≠ 0 →
      coordinateQuadPlus 4 K b = 0 → ∃ h ∈ spinSeven K,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = b) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → ∀ (s : ℕ)
        (QC : QuadraticForm K (Fin (2 * s) → K)) (b : Fin (2 * 4) → K),
        b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
        ∀ (W : AddSubgroup ((Fin (2 * 4) → K) × (Fin (2 * s) → K)))
          (A : Subgroup (GL (Fin (2 * 4)) K)),
          A ≤ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype →
          (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b) →
          (∀ t : K, (t • b, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ w ∈ W, coordinateQuadPlus 4 K w.1 + QC w.2 = 0) →
          (∀ w ∈ W, polar (coordinateQuadPlus 4 K) w.1 b = 0) →
          (∀ M ∈ spinSeven K, Odd (orderOf M) →
            ((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ b = b →
            (∀ w ∈ W, (((M : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1,
              w.2) ∈ W) ∧
            ∀ a ∈ A, (M : GL (Fin (2 * 4)) K) * a * (M : GL (Fin (2 * 4)) K)⁻¹ ∈ A) →
          (∀ a ∈ A, ∀ x : Fin (2 * 4) → K, polar (coordinateQuadPlus 4 K) x b = 0 →
            ((a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x - x, (0 : Fin (2 * s) → K)) ∈ W) →
          (∀ a ∈ A, ∀ w ∈ W, ∃ t : K,
            (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 - w.1 = t • b) →
          (∀ w ∈ W, (∀ a ∈ A, (a : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w.1 = w.1) →
            ∃ t : K, w = (t • b, 0)) →
          Nat.card A * Nat.card W = Nat.card K ^ (2 * 4 - 1 + 2 * s) → False :=
  fun K _ _ _ hq s QC b hb0 hbQ W A hA hAfix h3 h4 h5 h6 h7 h8 h9 hcount =>
    spinGeom_false_of_transitive hq (hTrans K) s QC b hb0 hbQ W A hA hAfix h3 h4 h5 h6 h7 h8 h9
      hcount

end Reduce

end CFSG.LieType.SpinGeom
