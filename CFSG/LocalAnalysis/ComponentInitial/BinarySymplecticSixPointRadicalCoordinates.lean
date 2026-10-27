module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixPointRadical

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Module Submodule SymplecticFlag CFSG.Assembly.LowTwoRank SymplecticTorusWeyl
open LinearMap (BilinForm)

@[expose] def t0Mat (a a' : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![1, a, a'; 0, 1, 0; 0, 0, 1]

@[expose] def jMat (c x x' : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![c, x, x'; x, 0, 0; x', 0, 0]

theorem t0Mat_mul : ∀ a a' c c' : ZMod 2, t0Mat a a' * t0Mat c c' = t0Mat (a + c) (a' + c') := by
  decide

theorem t0Mat_zero : t0Mat 0 0 = 1 := by
  decide

theorem t0Mat_mul_self (a a' : ZMod 2) : t0Mat a a' * t0Mat a a' = 1 := by
  rw [t0Mat_mul, zmod_two_add_self_eq_zero, zmod_two_add_self_eq_zero, t0Mat_zero]

theorem t0Mat_injective : ∀ a a' c c' : ZMod 2, t0Mat a a' = t0Mat c c' → a = c ∧ a' = c' := by
  decide

theorem jMat_transpose (c x x' : ZMod 2) : (jMat c x x')ᵀ = jMat c x x' := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def t0Unit (a a' : ZMod 2) : GL (Fin 3) (ZMod 2) :=
  ⟨t0Mat a a', t0Mat a a', t0Mat_mul_self a a', t0Mat_mul_self a a'⟩

theorem coe_t0Unit (a a' : ZMod 2) :
    ((t0Unit a a' : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = t0Mat a a' :=
  rfl

@[expose] def lagrangianT0 : Subgroup (GL (Fin 3) (ZMod 2)) where
  carrier := Set.range fun p : ZMod 2 × ZMod 2 => t0Unit p.1 p.2
  one_mem' := ⟨(0, 0), Units.ext t0Mat_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, a'⟩, rfl⟩ ⟨⟨c, c'⟩, rfl⟩
    exact ⟨(a + c, a' + c'), Units.ext (t0Mat_mul a a' c c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a, a'⟩, rfl⟩
    exact ⟨(a, a'), (inv_eq_of_mul_eq_one_right (Units.ext (t0Mat_mul_self a a'))).symm⟩

theorem mem_lagrangianT0 {D : GL (Fin 3) (ZMod 2)} :
    D ∈ lagrangianT0 ↔ ∃ a a' : ZMod 2, D = t0Unit a a' := by
  constructor
  · rintro ⟨⟨a, a'⟩, rfl⟩
    exact ⟨a, a', rfl⟩
  · rintro ⟨a, a', rfl⟩
    exact ⟨(a, a'), rfl⟩

theorem card_lagrangianT0 : Nat.card lagrangianT0 = 4 := by
  have hinj : Function.Injective fun p : ZMod 2 × ZMod 2 => t0Unit p.1 p.2 := by
    rintro ⟨a, a'⟩ ⟨c, c'⟩ h
    obtain ⟨h1, h2⟩ := t0Mat_injective a a' c c' (congrArg Units.val h)
    rw [h1, h2]
  have h := Nat.card_range_of_injective hinj
  rw [Nat.card_prod, Nat.card_zmod] at h
  exact h

@[expose] def alt3Mat (z z' t : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![0, z, z'; z, 0, t; z', t, 0]

theorem t0_fixed_symMat : ∀ x : SixBits,
    (t0Mat 1 0 * symMat x * (t0Mat 1 0)ᵀ = symMat x ∧
      t0Mat 0 1 * symMat x * (t0Mat 0 1)ᵀ = symMat x) ↔
      symMat x = jMat x.1 x.2.2.2.1 x.2.2.2.2.1 := by
  decide

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem t0_square_commute_symMat : ∀ x y : SixBits,
    t0Mat 1 0 * symMat x * (t0Mat 1 0)ᵀ = symMat x →
    t0Mat 0 1 * symMat y * (t0Mat 0 1)ᵀ = symMat y →
    symMat x + t0Mat 1 0 * symMat y * (t0Mat 1 0)ᵀ =
      symMat y + t0Mat 0 1 * symMat x * (t0Mat 0 1)ᵀ →
    symMat x = jMat x.1 x.2.2.2.1 x.2.2.2.2.1 ∧ symMat y = jMat y.1 y.2.2.2.1 y.2.2.2.2.1 := by
  decide

theorem isUnitriangular_t0Mat (a a' : ZMod 2) : IsUnitriangular (t0Mat a a') :=
  isUnitriangular_utMat a 0 a'

theorem t0Mat_inv (a a' : ZMod 2) : (t0Mat a a')⁻¹ = t0Mat a a' :=
  Matrix.inv_eq_left_inv (t0Mat_mul_self a a')

theorem t0Unit_inv (a a' : ZMod 2) : (t0Unit a a')⁻¹ = t0Unit a a' :=
  inv_eq_of_mul_eq_one_right (Units.ext (t0Mat_mul_self a a'))

theorem t0Mat_mul_jMat : ∀ c x x' y y' : ZMod 2,
    t0Mat y y' * jMat (c + x * y + x' * y') x x' = jMat c x x' := by
  decide

theorem jMat_mul_t0Mat_transpose : ∀ c x x' y y' : ZMod 2,
    jMat (c + x * y + x' * y') x x' * (t0Mat y y')ᵀ = jMat c x x' := by
  decide

theorem jMat_injective : ∀ c x x' c₀ y y' : ZMod 2, jMat c x x' = jMat c₀ y y' →
    c = c₀ ∧ x = y ∧ x' = y' := by
  decide

theorem eq_jMat_iff {B : Matrix (Fin 3) (Fin 3) (ZMod 2)} :
    (Bᵀ = B ∧ ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → B i j = 0) ↔ B = jMat (B 0 0) (B 0 1) (B 0 2) := by
  constructor
  · rintro ⟨hB, h0⟩
    have h : ∀ i j, B j i = B i j := fun i j => congrFun (congrFun hB i) j
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact h _ _ |
      exact h0 _ _ (by decide) (by decide)
  · intro hB
    refine ⟨by rw [hB]; exact jMat_transpose _ _ _, fun i j hi hj => ?_⟩
    rw [hB]
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl hi | exact absurd rfl hj

theorem pairedSympForm_three (v w : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 v w =
      v (Sum.inl 0) * w (Sum.inr 0) + v (Sum.inl 1) * w (Sum.inr 1) +
        v (Sum.inl 2) * w (Sum.inr 2) + (v (Sum.inr 0) * w (Sum.inl 0) +
          v (Sum.inr 1) * w (Sum.inl 1) + v (Sum.inr 2) * w (Sum.inl 2)) := by
  rw [pairedSympForm_apply]
  simp only [dotProduct, Fin.sum_univ_three, Function.comp_apply]
  rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

section Basis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
include he

theorem form_eq_pairedSympForm (x y : V) :
    b x y = pairedSympForm (ZMod 2) 3 ⇑(e.repr x) ⇑(e.repr y) := by
  rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e b x y, he, pairedSympForm,
    Matrix.toBilin'_apply']

theorem bilin_inl (j : Fin 3) (x : V) : b (e (Sum.inl j)) x = e.repr x (Sum.inr j) := by
  rw [form_eq_pairedSympForm he, e.repr_self, Finsupp.single_eq_pi_single,
    pairedSympForm_single_inl]

theorem bilin_inr (j : Fin 3) (x : V) : b (e (Sum.inr j)) x = e.repr x (Sum.inl j) := by
  rw [form_eq_pairedSympForm he, e.repr_self, Finsupp.single_eq_pi_single, pairedSympForm_three]
  fin_cases j <;> simp

theorem bilin_f_u : b (e (Sum.inr 0)) (e (Sum.inl 0)) = 1 := by
  rw [bilin_inr he, e.repr_self, Finsupp.single_eq_same]

omit he in
variable (e) in
@[expose] def pointSpan : Submodule (ZMod 2) V :=
  span (ZMod 2) (e '' {Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inr 2})

omit he in
theorem mem_pointSpan {x : V} :
    x ∈ pointSpan e ↔ e.repr x (Sum.inl 0) = 0 ∧ e.repr x (Sum.inr 0) = 0 := by
  rw [pointSpan, Basis.mem_span_image]
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> by_contra hne <;> have h' := h (Finsupp.mem_support_iff.2 hne) <;>
      simp at h'
  · rintro ⟨h1, h2⟩ i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    rcases i with i | i <;> fin_cases i <;> simp_all

theorem pointSpan_eq_pairOrth : pointSpan e = pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  ext x
  rw [mem_pointSpan, mem_pairOrth, bilin_inl he, bilin_inr he, and_comm]

omit he in
theorem finrank_eq_six (e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V) : finrank (ZMod 2) V = 6 := by
  rw [Module.finrank_eq_card_basis e]
  rfl

theorem card_pointSpan (hb : b.IsAlt) (hnd : b.Nondegenerate) :
    Nat.card (pointSpan e) = 16 := by
  have : FiniteDimensional (ZMod 2) V := e.finiteDimensional_of_finite
  have h := finrank_pairOrth hb hnd (bilin_f_u he)
  rw [finrank_eq_six e] at h
  rw [pointSpan_eq_pairOrth he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h4 : finrank (ZMod 2) (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) = 4 := by omega
  rw [h4]
  norm_num

omit he in
theorem toMatrix_pointMap_apply (w : V) (c : ZMod 2) (i j : Fin 3 ⊕ Fin 3) :
    LinearMap.toMatrix e e (pointMap b (e (Sum.inl 0)) w c) i j =
      Finsupp.single j 1 i + b (e j) w * Finsupp.single (Sum.inl 0) 1 i +
        b (e (Sum.inl 0)) (e j) * (e.repr w i + c * Finsupp.single (Sum.inl 0) 1 i) := by
  rw [LinearMap.toMatrix_apply, pointMap_apply]
  simp only [map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]

theorem toMatrix_pointMap {w : V} (hw : w ∈ pointSpan e) (c : ZMod 2) :
    LinearMap.toMatrix e e (pointMap b (e (Sum.inl 0)) w c) =
      fromBlocks (t0Mat (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)))
        (jMat c (e.repr w (Sum.inl 1)) (e.repr w (Sum.inl 2))) 0
        (t0Mat (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)))ᵀ := by
  obtain ⟨h1, h2⟩ := mem_pointSpan.1 hw
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [toMatrix_pointMap_apply, bilin_inl he, bilin_inr he, t0Mat, jMat, h1, h2]

omit he in
variable (e) in
@[expose] def pointVec (x x' y y' : ZMod 2) : V :=
  x • e (Sum.inl 1) + x' • e (Sum.inl 2) + y • e (Sum.inr 1) + y' • e (Sum.inr 2)

omit he in
theorem repr_pointVec (x x' y y' : ZMod 2) (i : Fin 3 ⊕ Fin 3) :
    e.repr (pointVec e x x' y y') i =
      x * Finsupp.single (Sum.inl 1) 1 i + x' * Finsupp.single (Sum.inl 2) 1 i +
        y * Finsupp.single (Sum.inr 1) 1 i + y' * Finsupp.single (Sum.inr 2) 1 i := by
  simp only [pointVec, map_add, map_smul, Basis.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]

omit he in
theorem pointVec_mem (x x' y y' : ZMod 2) : pointVec e x x' y y' ∈ pointSpan e :=
  mem_pointSpan.2 ⟨by simp [repr_pointVec], by simp [repr_pointVec]⟩

omit he in
theorem pointVec_coords (x x' y y' : ZMod 2) :
    e.repr (pointVec e x x' y y') (Sum.inl 1) = x ∧ e.repr (pointVec e x x' y y') (Sum.inl 2) = x' ∧
      e.repr (pointVec e x x' y y') (Sum.inr 1) = y ∧
        e.repr (pointVec e x x' y y') (Sum.inr 2) = y' := by
  simp [repr_pointVec]

theorem mem_pairOrth_of_mem_pointSpan {w : V} (hw : w ∈ pointSpan e) :
    w ∈ pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) := by
  rwa [← pointSpan_eq_pairOrth he]

theorem spMatrixOf_spCoord_pointElt (hb : b.IsAlt) {w : V} (hw : w ∈ pointSpan e) (c : ZMod 2) :
    spMatrixOf (spCoord he (pointElt hb
      (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) c)) =
      fromBlocks (t0Mat (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)))
        (jMat c (e.repr w (Sum.inl 1)) (e.repr w (Sum.inl 2))) 0
        (t0Mat (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)))ᵀ :=
  toMatrix_pointMap he hw c

theorem spCoord_pointElt_mem_unipotent (hb : b.IsAlt) {w : V} (hw : w ∈ pointSpan e)
    (c : ZMod 2) :
    spCoord he (pointElt hb (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) c) ∈
      unipotent 3 (ZMod 2) := by
  refine ⟨t0Mat (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)),
    jMat (c + e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) +
      e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)) (e.repr w (Sum.inl 1)) (e.repr w (Sum.inl 2)),
    isUnitriangular_t0Mat _ _, jMat_transpose _ _ _, ?_⟩
  change spMatrixOf _ = _
  rw [spMatrixOf_spCoord_pointElt he hb hw, blockMat, t0Mat_mul_jMat, t0Mat_inv]

theorem spCoord_pointElt_eq (hb : b.IsAlt) {w : V} (hw : w ∈ pointSpan e) (c : ZMod 2) :
    spCoord he (pointElt hb (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) c) =
      tauSym 3 (Multiplicative.ofAdd ⟨jMat (c + e.repr w (Sum.inl 1) * e.repr w (Sum.inr 1) +
        e.repr w (Sum.inl 2) * e.repr w (Sum.inr 2)) (e.repr w (Sum.inl 1)) (e.repr w (Sum.inl 2)),
        mem_binarySymMatrices.2 (jMat_transpose _ _ _)⟩) *
      leviSp (t0Unit (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2))) := by
  apply statedSp_ext
  change spMatrixOf _ = spMatrixOf (_ * _)
  rw [spMatrixOf_mul, spMatrixOf_spCoord_pointElt he hb hw, spMatrixOf_tauSym, spMatrixOf,
    coe_leviSp, t0Unit_inv, fromBlocks_multiply, toAdd_ofAdd]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [coe_t0Unit, jMat_mul_t0Mat_transpose]

theorem lagrangianLevi_spCoord_pointElt (hb : b.IsAlt) {w : V} (hw : w ∈ pointSpan e)
    (c : ZMod 2)
    (hS : spCoord he (pointElt hb (mem_pairOrth_left (mem_pairOrth_of_mem_pointSpan he hw)) c) ∈
      stabilizer 3 (ZMod 2) (lagrangianZero 3)) :
    lagrangianLevi 3 ⟨_, hS⟩ = t0Unit (e.repr w (Sum.inr 1)) (e.repr w (Sum.inr 2)) := by
  refine Units.ext ?_
  rw [coe_lagrangianLevi, spMatrixOf_spCoord_pointElt he hb hw, toBlocks_fromBlocks₁₁]
  rfl

end Basis

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
