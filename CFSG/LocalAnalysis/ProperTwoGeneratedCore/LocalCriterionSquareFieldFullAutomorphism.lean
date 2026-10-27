module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2 psl2FieldAut pgl2FieldAut psl2FieldAut_apply
  psl2FieldAut_toPGL psl2RingEquiv_mk)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (semilinearAction
  semilinearAction_inl semilinearAction_inr semilinearAction_injective
  semilinearAction_surjective pglAction_toPGL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner congr_conj)

variable {F : Type u} [Field F]

theorem conj_comp_sl2FieldAction (sigma : RingAut F) :
    (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).comp (sl2FieldAction sigma).toMonoidHom =
      (MulAut.conj (sl2FieldAction sigma)).toMonoidHom.comp MulAut.conj := by
  ext h g
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]

@[expose] def gammaToMulAut (F : Type u) [Field F] : Gamma F →* MulAut SL(2, F) :=
  SemidirectProduct.lift MulAut.conj sl2FieldAction conj_comp_sl2FieldAction

@[simp] theorem gammaToMulAut_apply (a : Gamma F) (g : SL(2, F)) :
    gammaToMulAut F a g =
      a.left * Matrix.SpecialLinearGroup.map a.right.toRingHom g * a.left⁻¹ := rfl

@[simp] theorem gammaToMulAut_inl (h : SL(2, F)) :
    gammaToMulAut F (SemidirectProduct.inl h) = MulAut.conj h :=
  SemidirectProduct.lift_inl _ _ _ h

@[simp] theorem gammaToMulAut_inr (sigma : RingAut F) :
    gammaToMulAut F (SemidirectProduct.inr sigma) = sl2FieldAction sigma :=
  SemidirectProduct.lift_inr _ _ _ sigma

theorem gammaToMulAut_mulVec_semilinearApply (a : Gamma F) (g : SL(2, F)) (v : Fin 2 → F) :
    Matrix.mulVec (gammaToMulAut F a g : Matrix (Fin 2) (Fin 2) F)
        (semilinearApply a.left a.right v) =
      semilinearApply a.left a.right (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F) v) := by
  have hinv : ((a.left⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * a.left = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hmap : (fun i => a.right (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) F) v i)) =
      Matrix.mulVec (a.right.toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) F))
        (fun i => a.right (v i)) :=
    funext fun i => a.right.toRingHom.map_mulVec (g : Matrix (Fin 2) (Fin 2) F) v i
  rw [gammaToMulAut_apply, semilinearApply, semilinearApply, hmap, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_assoc, hinv, Matrix.mul_one, Matrix.SpecialLinearGroup.map_apply_coe]

theorem linearKernel_map_gammaToMulAut :
    (linearKernel F).map (gammaToMulAut F) =
      (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
  rw [linearKernel_eq_projection_ker, ← SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.map_range, gammaToMulAut, SemidirectProduct.lift_comp_inl]

section CharTwo

variable [CharP F 2]

theorem sl2_center_eq_bot : Subgroup.center SL(2, F) = ⊥ := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr1 : r = 1 := by
      apply frobenius_inj F 2
      simpa [frobenius_def] using hr
    ext i j
    rw [← hA, hr1]
    simp [Matrix.one_apply]
  · rintro rfl
    exact ⟨1, by simp, by simp⟩

@[expose] def sl2EquivPSL2 : SL(2, F) ≃* PSL2 F :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(2, F)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', sl2_center_eq_bot]),
      QuotientGroup.mk'_surjective _⟩

theorem sl2EquivPSL2_apply (g : SL(2, F)) :
    sl2EquivPSL2 g = QuotientGroup.mk' (Subgroup.center SL(2, F)) g := rfl

theorem congr_sl2FieldAction (sigma : RingAut F) :
    MulAut.congr sl2EquivPSL2 (sl2FieldAction sigma) = psl2FieldAut F sigma := by
  ext x
  obtain ⟨g, rfl⟩ := sl2EquivPSL2.surjective x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, psl2FieldAut_apply, sl2EquivPSL2_apply, sl2EquivPSL2_apply,
    psl2RingEquiv_mk]
  rfl

variable [Finite F]

theorem sl2_toPGL_bijective :
    Function.Bijective (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* PGL2 F) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, fun x => ?_⟩
  · rw [Matrix.SpecialLinearGroup.toPGL_ker, sl2_center_eq_bot]
  · have hroots (r : Fˣ) : ∃ k : Fˣ, k ^ Fintype.card (Fin 2) = r := by
      obtain ⟨b, hb⟩ := isSquare_of_charTwo' (r : F)
      have hb0 : b ≠ 0 := by
        rintro rfl
        simp at hb
      exact ⟨Units.mk0 b hb0, Units.ext (by simp [hb, pow_two])⟩
    obtain ⟨y, rfl⟩ := Matrix.ProjectiveSpecialLinearGroup.toPGL_surj_of_roots hroots x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨g, rfl⟩

@[expose] def sl2EquivPGL2 : SL(2, F) ≃* PGL2 F :=
  MulEquiv.ofBijective _ sl2_toPGL_bijective

theorem sl2EquivPGL2_apply (g : SL(2, F)) :
    sl2EquivPGL2 g = Matrix.ProjectiveSpecialLinearGroup.toPGL (sl2EquivPSL2 g) := rfl

theorem sl2EquivPGL2_fieldAction (sigma : RingAut F) :
    (sl2FieldAction sigma).trans sl2EquivPGL2 = sl2EquivPGL2.trans (pgl2FieldAut F sigma) := by
  ext g
  change sl2EquivPGL2 (sl2FieldAction sigma g) = pgl2FieldAut F sigma (sl2EquivPGL2 g)
  rw [sl2EquivPGL2_apply, sl2EquivPGL2_apply, ← psl2FieldAut_toPGL, psl2FieldAut_apply,
    sl2EquivPSL2_apply, sl2EquivPSL2_apply, psl2RingEquiv_mk]
  rfl

@[expose] def gammaEquivPGammaL2 : Gamma F ≃* PGammaL2 F :=
  SemidirectProduct.congr sl2EquivPGL2 (MulEquiv.refl _) sl2EquivPGL2_fieldAction

theorem gammaEquivPGammaL2_inl (h : SL(2, F)) :
    gammaEquivPGammaL2 (SemidirectProduct.inl h) = SemidirectProduct.inl (sl2EquivPGL2 h) :=
  rfl

theorem gammaEquivPGammaL2_inr (sigma : RingAut F) :
    gammaEquivPGammaL2 (SemidirectProduct.inr sigma) = SemidirectProduct.inr sigma :=
  SemidirectProduct.ext (map_one sl2EquivPGL2) rfl

theorem congr_gammaToMulAut (a : Gamma F) :
    MulAut.congr sl2EquivPSL2 (gammaToMulAut F a) = semilinearAction F (gammaEquivPGammaL2 a) := by
  have hhom : (MulAut.congr sl2EquivPSL2).toMonoidHom.comp (gammaToMulAut F) =
      (semilinearAction F).comp gammaEquivPGammaL2.toMonoidHom := by
    apply SemidirectProduct.hom_ext
    · ext h : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [gammaToMulAut_inl, congr_conj, gammaEquivPGammaL2_inl, semilinearAction_inl,
        sl2EquivPGL2_apply, pglAction_toPGL]
    · ext sigma : 1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [gammaToMulAut_inr, congr_sl2FieldAction, gammaEquivPGammaL2_inr,
        semilinearAction_inr]
  exact DFunLike.congr_fun hhom a

theorem gammaToMulAut_bijective : Function.Bijective (gammaToMulAut F) := by
  have hcomp : (MulAut.congr sl2EquivPSL2) ∘ (gammaToMulAut F) =
      (semilinearAction F) ∘ gammaEquivPGammaL2 := funext congr_gammaToMulAut
  have hbij : Function.Bijective ((semilinearAction F) ∘ gammaEquivPGammaL2) :=
    (Function.Bijective.comp ⟨semilinearAction_injective F, semilinearAction_surjective F⟩
      gammaEquivPGammaL2.bijective)
  rw [← hcomp] at hbij
  exact ((MulAut.congr sl2EquivPSL2).bijective.of_comp_iff' _).mp hbij

end CharTwo

section Card

variable {n : ℕ}

theorem gammaToMulAut_bijective_of_card (hcard : Nat.card F = 2 ^ n) :
    Function.Bijective (gammaToMulAut F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have : CharP F 2 := char_two_of_card hcard
  exact gammaToMulAut_bijective

@[expose] def gammaEquivMulAut (_hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n) :
    Gamma F ≃* MulAut SL(2, F) :=
  MulEquiv.ofBijective (gammaToMulAut F) (gammaToMulAut_bijective_of_card hcard)

@[simp] theorem gammaEquivMulAut_apply (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (a : Gamma F) : gammaEquivMulAut hn hcard a = gammaToMulAut F a := rfl

def mulAutToRingAut (hcard : Nat.card F = 2 ^ n) : MulAut SL(2, F) →* RingAut F :=
  SemidirectProduct.rightHom.comp
    (MulEquiv.ofBijective _ (gammaToMulAut_bijective_of_card hcard)).symm.toMonoidHom

theorem mulAutToRingAut_gammaToMulAut (hcard : Nat.card F = 2 ^ n) (a : Gamma F) :
    mulAutToRingAut hcard (gammaToMulAut F a) = a.right :=
  congrArg SemidirectProduct.right
    ((MulEquiv.ofBijective _ (gammaToMulAut_bijective_of_card hcard)).symm_apply_apply a)

theorem mulAutToRingAut_surjective (hcard : Nat.card F = 2 ^ n) :
    Function.Surjective (mulAutToRingAut hcard) := fun sigma =>
  ⟨gammaToMulAut F (SemidirectProduct.inr sigma), by
    rw [mulAutToRingAut_gammaToMulAut, SemidirectProduct.right_inr]⟩

theorem inner_eq_ker_mulAutToRingAut (hcard : Nat.card F = 2 ^ n) :
    inner SL(2, F) = (mulAutToRingAut hcard).ker := by
  ext α
  obtain ⟨a, rfl⟩ := (gammaToMulAut_bijective_of_card hcard).2 α
  rw [MonoidHom.mem_ker, mulAutToRingAut_gammaToMulAut]
  constructor
  · rintro ⟨h, hh⟩
    rw [← gammaToMulAut_inl] at hh
    rw [← (gammaToMulAut_bijective_of_card hcard).1 hh, SemidirectProduct.right_inl]
  · intro ha
    refine ⟨a.left, ?_⟩
    rw [← gammaToMulAut_inl]
    congr 1
    exact SemidirectProduct.ext rfl ha.symm

def outerEquivRingAut (hcard : Nat.card F = 2 ^ n) : Outer SL(2, F) ≃* RingAut F :=
  (QuotientGroup.quotientMulEquivOfEq (inner_eq_ker_mulAutToRingAut hcard)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (mulAutToRingAut_surjective hcard))

@[simp] theorem outerEquivRingAut_mk (hcard : Nat.card F = 2 ^ n) (α : MulAut SL(2, F)) :
    outerEquivRingAut hcard (QuotientGroup.mk α) = mulAutToRingAut hcard α := by
  rw [outerEquivRingAut, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem even_SL2_full_automorphism_semilinear_model (_hn : 1 ≤ n)
    (hcard : Nat.card F = 2 ^ n) :
    Function.Bijective (gammaToMulAut F) ∧
      (linearKernel F).map (gammaToMulAut F) =
        (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range ∧
      IsCyclic (Outer SL(2, F)) ∧ Nat.card (Outer SL(2, F)) = n ∧
      ∀ α : MulAut SL(2, F), ∃! p : SL(2, F) × RingAut F,
        ∀ g, α g = p.1 * Matrix.SpecialLinearGroup.map p.2.toRingHom g * p.1⁻¹ := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij := gammaToMulAut_bijective_of_card hcard
  obtain ⟨hauto, hcyclic⟩ := ringAut_card_and_cyclic hcard
  refine ⟨hbij, linearKernel_map_gammaToMulAut, (outerEquivRingAut hcard).isCyclic.mpr hcyclic,
    (Nat.card_congr (outerEquivRingAut hcard).toEquiv).trans hauto, fun α => ?_⟩
  obtain ⟨a, rfl⟩ := hbij.2 α
  refine ⟨(a.left, a.right), fun g => gammaToMulAut_apply a g, ?_⟩
  rintro ⟨h, sigma⟩ hp
  have heq : gammaToMulAut F ⟨h, sigma⟩ = gammaToMulAut F a :=
    MulEquiv.ext fun g => (hp g).symm
  have ha := hbij.1 heq
  subst ha
  rfl

end Card

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
