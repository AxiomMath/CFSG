module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOField
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClUGraphFix

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.U (barEq barEq_apply map_bar_fmap exists_fmap_of_bar
  fmap_injective eq_one_of_odd_of_fix fix_fixedField_of_fix_circle)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL orthComponentData OrthNF
  signMat reflGL reflGL_mem rotGL rotGL_mem rotMat_neg_one_zero rotMat_apply_left
  commutatorElement_reflGL_rotGL mul_conj_mul_inv)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}

theorem ClO.field_fix_of_components (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {wF : Fin d → h.fixedField}
    (hwF : ∀ i, wF i ≠ 0) (hd3 : 3 ≤ d) (hexc : ¬ (Nat.card h.fixedField = 3 ∧ d ≤ 4))
    (hinj : Function.Injective (MulAut.conj :
      StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) →*
        MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF))))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (barPair h h2 hwF) = oκ _ (barPair h h2 hwF) * y)
    (hRc : ∀ s, oκ _ (barPair h h2 hwF) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    {g : similarityPairs (oQ (diagGL (wK_ne_zero h hwF)))} (hy : oκ _ g ∈ Ro)
    {X : GL (Fin d) h.fixedField}
    (hX : X ∈ ⁅CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hwF),
      CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hwF)⁆) :
    (g.val.left : Matrix (Fin d) (Fin d) K) *
        ((iotaF h X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map g.val.right *
        ((g.val.left⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((iotaF h X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have := h.finite
  have hHeq := matrixDerived_oQ h2 (diagGL (wK_ne_zero h hwF)) (diagGL_transpose _)
  have hIH := omegaF_le h h2 hwF
  set t := oκ (oQ (diagGL (wK_ne_zero h hwF))) (barPair h h2 hwF) with ht
  set φ := (matrixDerivedConjugation (oQ (diagGL (wK_ne_zero h hwF)))
    (barPair h h2 hwF)).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ (diagGL (wK_ne_zero h hwF))),
      (((φ Y : matrixDerived _) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar := by
    intro Y
    change ((matrixDerivedConjugation _ (barPair h h2 hwF) Y : matrixDerived _) :
      GL (Fin d) K).val = _
    rw [matrixDerivedConjugation_val, barPair_left, barPair_right, inv_one, mul_one, one_mul]
    rfl
  have hφt : ∀ Y, t (projH (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) Y) =
      projH (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) (φ Y) := fun Y => kappa_lift _ Y
  set F := (omegaF h hwF).subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) with hF
  have hF1 : ∀ Y ∈ F, φ Y = Y := by
    intro Y hY
    obtain ⟨X', -, hX'⟩ := mem_subgroupOf.1 hY
    apply Subtype.ext
    apply Units.ext
    rw [hφc, ← hX', coe_iotaF, map_bar_fmap]
  have hF2 : ∀ g' : matrixDerived (oQ (diagGL (wK_ne_zero h hwF))), g'⁻¹ * φ g' ∈
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) →
      ∀ Y ∈ F, g' * Y * g'⁻¹ ∈ F := by
    intro g' hg' Y hY
    obtain ⟨c, hc⟩ := hg'
    have hc' : (((g' : matrixDerived _) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar =
        (c : K) • (((g' : matrixDerived _) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      have e : ((g' : GL (Fin d) K))⁻¹ * ((φ g' : matrixDerived _) : GL (Fin d) K) =
          GeneralLinearGroup.scalar (Fin d) c := hc.symm
      have e2 : ((φ g' : matrixDerived _) : GL (Fin d) K) =
          (g' : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c := by
        rw [← e, mul_inv_cancel_left]
      have e3 := congrArg (fun M : GL (Fin d) K => (M : Matrix (Fin d) (Fin d) K)) e2
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at e3
      rw [← hφc, e3, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
        Matrix.mul_one]
    have hgI : (g' : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K
        (diagGL (wK_ne_zero h hwF)) :=
      Subgroup.commutator_le_self _ (by rw [← hHeq]; exact g'.2)
    rw [mem_subgroupOf] at hY ⊢
    exact conj_mem_omegaF h hwF hgI hc' hY
  obtain ⟨hperf, m, L, hsup, hL⟩ := orthComponentData (two_ne_zero_fixedField h hp2) hd3
    (diagGL hwF) (diagGL_transpose hwF) hexc
  set L' := fun i => (L i).map (iotaF h) with hL'
  have hL'le : ∀ i, L' i ≤ matrixDerived (oQ (diagGL (wK_ne_zero h hwF))) := fun i =>
    (map_mono (hL i).2.1).trans hIH
  have hfixL : ∀ i, ∀ Y : matrixDerived (oQ (diagGL (wK_ne_zero h hwF))),
      (Y : GL (Fin d) K) ∈ L' i →
      oκ (oQ (diagGL (wK_ne_zero h hwF))) g (projH _ Y) = projH _ Y := by
    intro i Y hY
    obtain ⟨hq, hLI, hLn⟩ := hL i
    set Lh := (L' i).subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))) with hLh
    have hq' : IsQuasisimple (L' i) :=
      LocalCores.isQuasisimple_of_mulEquiv ((L i).equivMapOfInjective _ (iotaF_injective h)) hq
    have hLhq : IsQuasisimple Lh :=
      LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe (hL'le i)).symm hq'
    have hLF : Lh ≤ F := fun Z hZ => mem_subgroupOf.2 (map_mono hLI (mem_subgroupOf.1 hZ))
    have hLn' : ∀ x ∈ F, ∀ l ∈ Lh, x * l * x⁻¹ ∈ Lh := by
      intro x hx l hl
      refine mem_subgroupOf.2 ?_
      obtain ⟨x₀, hx₀, hxx⟩ := mem_subgroupOf.1 hx
      obtain ⟨l₀, hl₀, hll⟩ := mem_subgroupOf.1 hl
      refine ⟨x₀ * l₀ * x₀⁻¹, hLn _ hx₀ _ hl₀, ?_⟩
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hxx, ← hll]
    exact ClU.fix_of_lift_sub hinj hRodd hRi hRc φ
      (matrixDerivedConjugation (oQ (diagGL (wK_ne_zero h hwF))) (barPair h h2 hwF)).injective
      hφt (fun Z hZ => hF1 Z hZ)
      (fun x hx Z hZ => hF2 x (by
        rw [show φ x = x from hx, inv_mul_cancel]
        exact one_mem _) Z hZ) hLF hLn' hLhq hy (mem_subgroupOf.2 hY)
  have hFsup : F ≤ MonoidHom.eqLocus ((oκ (oQ (diagGL (wK_ne_zero h hwF))) g).toMonoidHom.comp
      (projH (matrixDerived (oQ (diagGL (wK_ne_zero h hwF))))))
        (projH (matrixDerived (oQ (diagGL (wK_ne_zero h hwF))))) := by
    intro Y hY
    have hY' : (Y : GL (Fin d) K) ∈ ⨆ i, L' i := by
      rw [hL', ← Subgroup.map_iSup, hsup]
      exact mem_subgroupOf.1 hY
    have hmap : (⨆ i, (L' i).subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hwF))))).map
        (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))).subtype = ⨆ i, L' i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hL'le i)]
    rw [← hmap] at hY'
    obtain ⟨Y', hY'L, e⟩ := hY'
    rw [← Subtype.ext e]
    refine (iSup_le fun i Z hZ => ?_ :
      (⨆ i, (L' i).subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hwF))))) ≤ _) hY'L
    exact hfixL i Z (mem_subgroupOf.1 hZ)
  have hperfF : ⁅F, F⁆ = F := by
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL (wK_ne_zero h hwF)))).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hIH, omegaF,
      ← Subgroup.map_commutator, hperf]
  exact kappa_eq_of_fix g hperfF (fun Y hY => hFsup hY)
    (X := ⟨iotaF h X, hIH ⟨X, hX, rfl⟩⟩) (mem_subgroupOf.2 ⟨X, hX, rfl⟩)

theorem ClO.field_eq_one (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) (hd : 5 ≤ d)
    {wF : Fin d → h.fixedField} (hwF : OrthNF wF)
    (hker : OKer (oQ (diagGL (wK_ne_zero h hwF.1))))
    (hinj : Function.Injective (MulAut.conj :
      StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1)))) →*
        MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1)))))))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1))))))}
    (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ (barPair h h2 hwF.1) = oκ _ (barPair h h2 hwF.1) * y)
    (hRc : ∀ s, oκ _ (barPair h h2 hwF.1) s = s → Odd (orderOf s) →
      ∀ y ∈ Ro, MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro)
    (hsurj : ∀ y ∈ Ro, ∃ g : similarityPairs (oQ (diagGL (wK_ne_zero h hwF.1))),
      y = oκ _ g) :
    ∀ y ∈ Ro, y = 1 := by
  have := h.finite
  obtain ⟨hw0, I₀, hI₀3, hI₀c, hI₀w⟩ := hwF
  have hexc : ¬ (Nat.card h.fixedField = 3 ∧ d ≤ 4) := fun ⟨_, h4⟩ => by omega
  intro y hy
  obtain ⟨g, rfl⟩ := hsurj y hy
  set D := g.val.left with hD
  set τ := g.val.right with hτ
  have hodd := ClSp.odd_orderOf_of_mem hRodd hy
  have hτm : τ ^ orderOf (oκ _ g) = 1 := hker.right_pow_eq_one (pow_orderOf_eq_one _)
  have hfix := fun (X : GL (Fin d) h.fixedField) hX =>
    ClO.field_fix_of_components h hp2 h2 hw0 (by omega) hexc hinj hRodd hRi hRc hy (X := X) hX
  have hcomm : ∀ {i j : Fin d}, i ∈ I₀ → j ∈ I₀ → (hij : i ≠ j) → ∀ {a b : h.fixedField}
      (hab : a ^ 2 + b ^ 2 = 1), ⁅reflGL (K := h.fixedField) i, rotGL i j hij hab⁆ ∈
        ⁅CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hw0),
          CatalogueBGraphForm.isometryGroup d h.fixedField (diagGL hw0)⁆ :=
    fun hi hj hij _ _ hab => commutator_mem_commutator (reflGL_mem hw0 _)
      (rotGL_mem hw0 hij (hI₀w _ hi _ hj) hab)
  have hS : ∀ i ∈ I₀, ∀ j ∈ I₀, i ≠ j → (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
      signMat K {i, j} * D := by
    intro i hi j hj hij
    have hab : (0 : h.fixedField) ^ 2 + 1 ^ 2 = 1 := by ring
    have e := hfix _ (hcomm hi hj hij hab)
    rw [coe_iotaF, commutatorElement_reflGL_rotGL, show (0 : h.fixedField) ^ 2 - 1 ^ 2 = -1 by
      ring, show -(2 * (0 : h.fixedField) * 1) = 0 by ring, rotMat_neg_one_zero hij] at e
    have hsK : (signMat h.fixedField {i, j}).map h.fixedField.subtype = signMat K {i, j} := by
      ext x z
      simp only [signMat, map_apply, diagonal_apply]
      split_ifs <;> simp
    rw [hsK, map_signMat_field] at e
    calc (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} =
        (D : Matrix (Fin d) (Fin d) K) * signMat K {i, j} *
          (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * D) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = signMat K {i, j} * D := by rw [← Matrix.mul_assoc, e]
  have hiso₀ : ∀ x z, x ≠ z → (x ∈ I₀ ∨ z ∈ I₀) → (D : Matrix (Fin d) (Fin d) K) x z = 0 :=
    fun x z hxz hxI => offDiag_eq_zero_of_commute_sign_on h2 hI₀3 hS hxz hxI
  have hdiag : ∀ x z, x ≠ z → (D : Matrix (Fin d) (Fin d) K) x z = 0 := by
    intro x z hxz
    by_cases hx : x ∈ I₀
    · exact hiso₀ x z hxz (Or.inl hx)
    by_cases hz : z ∈ I₀
    · exact hiso₀ x z hxz (Or.inr hz)
    exact absurd (hI₀c x z hx hz) hxz
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I₀, ∃ j ∈ I₀, i ≠ j := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < I₀.card)
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by
      have := Finset.pred_card_le_card_erase (s := I₀) (a := i); omega : 0 < (I₀.erase i).card)
    exact ⟨i, hi, j, (Finset.mem_erase.1 hj).2, Ne.symm (Finset.mem_erase.1 hj).1⟩
  have hcirc : ∀ a b : h.fixedField, a ^ 2 + b ^ 2 = 1 → τ (a : K) = a := by
    intro a b hab
    have e := hfix _ (hcomm hi hj hij hab)
    have e' := congrFun (congrFun e i) i
    rw [conj_apply_diag_of_isolated (fun x hx => hdiag i x (Ne.symm hx))
      (fun x hx => hdiag x i hx), map_apply, coe_iotaF, map_apply] at e'
    have hMii : ((⁅reflGL (K := h.fixedField) i, rotGL i j hij hab⁆ : GL (Fin d) h.fixedField) :
        Matrix (Fin d) (Fin d) h.fixedField) i i = a ^ 2 - b ^ 2 := by
      rw [commutatorElement_reflGL_rotGL, rotMat_apply_left hij]
    rw [hMii] at e'
    have hb : b ^ 2 = 1 - a ^ 2 := by linear_combination hab
    rw [hb] at e'
    simp only [Subfield.subtype_apply] at e'
    push_cast at e'
    simp only [map_sub, map_pow, map_one] at e'
    have hτa2 : τ (a : K) ^ 2 = (a : K) ^ 2 := by
      have : (2 : K) * (τ (a : K) ^ 2 - (a : K) ^ 2) = 0 := by linear_combination e'
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with e3 | e3
    · exact e3
    · have hpow : ∀ m : ℕ, (τ ^ m) (a : K) = (-1) ^ m * a := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]
          change (τ ^ m) (τ (a : K)) = _
          rw [e3, map_neg, ih, pow_succ]
          ring
      have := hpow (orderOf (oκ _ g))
      rw [hτm, hodd.neg_one_pow] at this
      change (a : K) = -1 * a at this
      have ha0 : (a : K) = 0 := by
        have : (2 : K) * a = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_left h2
      rw [e3, ha0, neg_zero]
  have hτF := fix_fixedField_of_fix_circle h hp2 hcirc
  have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm fun c hc => hτF ⟨c, hc⟩
  exact eq_one_of_odd_of_sq hodd (kappa_sq_eq_one_of_diag h2 (wK_ne_zero h hw0) hτ1 hdiag)

end CFSG.ComponentClassification.Foote5.OddLieCore
