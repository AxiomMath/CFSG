module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2F4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Blk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Check

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def pcM : Mat18 := toMat 18 18 pcBits

@[expose] def pciM : Mat18 := toMat 18 18 pciBits

theorem pcM_mul_pciM : pcM * pciM = 1 := by
  rw [pcM, pciM, ← toMat_bmul]
  apply toMat_eq_one_of_bIsId
  decide

theorem pciM_mul_pcM : pciM * pcM = 1 := by
  rw [pcM, pciM, ← toMat_bmul]
  apply toMat_eq_one_of_bIsId
  decide

@[expose] noncomputable def conjP : Mat18 →* Mat18 where
  toFun M := pciM * M * pcM
  map_one' := by rw [Matrix.mul_one, pciM_mul_pcM]
  map_mul' M N := by
    calc pciM * (M * N) * pcM = pciM * M * (pcM * pciM) * N * pcM := by
          rw [pcM_mul_pciM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = pciM * M * pcM * (pciM * N * pcM) := by simp only [Matrix.mul_assoc]

theorem conjP_apply (M : Mat18) : conjP M = pciM * M * pcM := rfl

theorem conjP_injective : Function.Injective conjP := by
  intro M N h
  have := congrArg (fun X => pcM * X * pciM) h
  simp only [conjP_apply, ← Matrix.mul_assoc, pcM_mul_pciM, Matrix.one_mul] at this
  simpa only [Matrix.mul_assoc, pcM_mul_pciM, Matrix.mul_one] using this

@[expose] noncomputable def lft : SL3 →* Mat18 where
  toFun a := conjP (reF9 (kr (a : M3) 1))
  map_one' := by rw [coe_SL3_one, kr_one, map_one, map_one]
  map_mul' a b := by
    rw [coe_SL3_mul, ← map_mul, ← map_mul, ← kr_mul, Matrix.mul_one]

@[expose] noncomputable def rgt : SL3 →* Mat18 where
  toFun b := conjP (reF9 (kr 1 ((b⁻¹ : SL3) : M3)ᵀ))
  map_one' := by rw [inv_one, coe_SL3_one, transpose_one, kr_one, map_one, map_one]
  map_mul' a b := by
    rw [← map_mul, ← map_mul, ← kr_mul, Matrix.mul_one, _root_.mul_inv_rev, coe_SL3_mul,
      transpose_mul]

theorem lft_apply (a : SL3) : lft a = conjP (reF9 (kr (a : M3) 1)) := rfl

theorem rgt_apply (b : SL3) : rgt b = conjP (reF9 (kr 1 ((b⁻¹ : SL3) : M3)ᵀ)) := rfl

theorem lft_rgt_comm (a b : SL3) : lft a * rgt b = rgt b * lft a := by
  rw [lft_apply, rgt_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← kr_mul, ← kr_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

@[expose] noncomputable def kact : SL3 →* Mat18 where
  toFun g := lft g * rgt (sigma3 g)
  map_one' := by rw [map_one, map_one, map_one, Matrix.mul_one]
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    calc lft g * lft h * (rgt (sigma3 g) * rgt (sigma3 h))
        = lft g * (lft h * rgt (sigma3 g)) * rgt (sigma3 h) := by simp only [Matrix.mul_assoc]
      _ = lft g * (rgt (sigma3 g) * lft h) * rgt (sigma3 h) := by rw [lft_rgt_comm]
      _ = lft g * rgt (sigma3 g) * (lft h * rgt (sigma3 h)) := by simp only [Matrix.mul_assoc]

theorem kact_apply (g : SL3) : kact g = lft g * rgt (sigma3 g) := rfl

theorem kact_eq (g : SL3) : kact g = conjP (reF9 (kr (g : M3) (frob3 (g : M3)))) := by
  rw [kact_apply, lft_apply, rgt_apply, ← map_mul, ← map_mul, ← kr_mul, Matrix.mul_one,
    Matrix.one_mul, coe_sigma3_inv, star3, transpose_transpose]

theorem code_mul (x y : F4) : ((x * y).code : ℕ) = mulN x.code y.code := by
  have key : ∀ x y : F4, decide (((x * y).code : ℕ) = mulN x.code y.code) = true := by decide
  exact of_decide_eq_true (key x y)

theorem code_kr (A B : M3) (r s : Fin 9) :
    ((kr A B r s).code : ℕ) = krCode (fun i j => (A i j).code) (fun i j => (B i j).code) r s := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective r
  obtain ⟨⟨k, l⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 3)).surjective s
  rw [kr_apply, code_mul, krCode]
  have h1 : (⟨((finProdFinEquiv (i, j) : Fin 9) : ℕ) / 3, by omega⟩ : Fin 3) = i := by
    ext; simp only [finProdFinEquiv_apply_val]; omega
  have h2 : (⟨((finProdFinEquiv (i, j) : Fin 9) : ℕ) % 3, by omega⟩ : Fin 3) = j := by
    ext; simp only [finProdFinEquiv_apply_val]; omega
  have h3 : (⟨((finProdFinEquiv (k, l) : Fin 9) : ℕ) / 3, by omega⟩ : Fin 3) = k := by
    ext; simp only [finProdFinEquiv_apply_val]; omega
  have h4 : (⟨((finProdFinEquiv (k, l) : Fin 9) : ℕ) % 3, by omega⟩ : Fin 3) = l := by
    ext; simp only [finProdFinEquiv_apply_val]; omega
  rw [h1, h2, h3, h4]

theorem toMat_reBits9 (M : Matrix (Fin 9) (Fin 9) F4) :
    toMat 18 18 (reBits9 fun i j => (M i j).code) = reF9 M := by
  ext r c
  obtain ⟨⟨i, β⟩, rfl⟩ := (finProdFinEquiv (m := 9) (n := 2)).surjective r
  obtain ⟨⟨j, γ⟩, rfl⟩ := (finProdFinEquiv (m := 9) (n := 2)).surjective c
  rw [reF9_apply, mF4_eq_reBit, toMat_apply, reBits9, getD_ofFn, testBit_bitsOf]
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  have h1 : ((γ : ℕ) + 2 * (j : ℕ)) < 18 := by omega
  have h2 : ((β : ℕ) + 2 * (i : ℕ)) / 2 = i := by omega
  have h3 : ((β : ℕ) + 2 * (i : ℕ)) % 2 = β := by omega
  have h4 : ((γ : ℕ) + 2 * (j : ℕ)) / 2 = j := by omega
  have h5 : ((γ : ℕ) + 2 * (j : ℕ)) % 2 = γ := by omega
  have hi : (⟨((β : ℕ) + 2 * (i : ℕ)) / 2, by omega⟩ : Fin 9) = i := Fin.ext h2
  have hj : Fin.ofNat 9 (((γ : ℕ) + 2 * (j : ℕ)) / 2) = j := Fin.ext (by simp [Fin.ofNat, h4])
  simp only [h1, decide_true, Bool.true_and, hi, hj, h3, h5]

theorem code_transvection3 {a b : Fin 3} (hab : a ≠ b) (c : F4) (i j : Fin 3) :
    ((Matrix.transvection a b c i j).code : ℕ) = trCode3 a b c.code i j := by
  have key : ∀ (a b : Fin 3) (c : F4) (i j : Fin 3), decide (a ≠ b →
      ((Matrix.transvection a b c i j).code : ℕ) = trCode3 a b c.code i j) = true := by
    decide
  exact of_decide_eq_true (key a b c i j) hab

theorem toMat_bd9Bits (A B : Array ℕ) :
    toMat 18 18 (bd9Bits A B) = bdN (n := 9) (toMat 9 9 A) (toMat 9 9 B) := by
  ext r c
  refine Fin.addCases (m := 9) (n := 9) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) c
  · rw [bdN_cc, toMat_apply, toMat_apply, bd9Bits, getD_ofFn]
    have hj : (j : ℕ) < 9 := j.isLt
    simp only [Fin.val_castAdd, i.isLt, ↓reduceIte]
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    simp [hj]
  · rw [bdN_cn, toMat_apply, bd9Bits, getD_ofFn]
    simp only [Fin.val_castAdd, Fin.val_natAdd, i.isLt, ↓reduceIte]
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    simp
  · rw [bdN_nc, toMat_apply, bd9Bits, getD_ofFn]
    have hj : ¬ (9 ≤ (j : ℕ)) := by omega
    simp [Nat.testBit_shiftLeft, hj]
  · rw [bdN_nn, toMat_apply, toMat_apply, bd9Bits, getD_ofFn]
    have : ¬ (9 + (i : ℕ) < 9) := by omega
    simp only [Fin.val_natAdd, this, ↓reduceIte, Nat.testBit_shiftLeft]
    rw [show (512 : ℕ) = 2 ^ 9 from rfl, Nat.testBit_mod_two_pow]
    simp [show 9 + (i : ℕ) - 9 = i by omega, show 9 + (j : ℕ) - 9 = j by omega]

theorem pairOf_ne (s : Fin 12) : (pairOf s).1 ≠ (pairOf s).2 := by
  revert s; decide

@[expose] def coefOf (s : Fin 12) : F4 := ⟨Fin.ofNat 4 (coefCode s)⟩

theorem code_coefOf (s : Fin 12) : ((coefOf s).code : ℕ) = coefCode s := by
  revert s; decide

@[expose] noncomputable def gen3 (s : Fin 12) : SL3 :=
  stT (F := F4) (m := 2) (by norm_num) (pairOf s).1 (pairOf s).2 (coefOf s)

theorem coe_gen3 (s : Fin 12) :
    ((gen3 s : SL3) : M3) = Matrix.transvection (pairOf s).1 (pairOf s).2 (coefOf s) := by
  rw [gen3, stT_eq_transvection _ (pairOf_ne s)]
  rfl

@[expose] def genA (s : Fin 12) : Mat9 := toMat 9 9 (genABits s)

theorem codes_kr_gen3 (s : Fin 12) :
    (fun i j => ((kr (Matrix.transvection (pairOf s).1 (pairOf s).2 (coefOf s))
      (frob3 (Matrix.transvection (pairOf s).1 (pairOf s).2 (coefOf s))) i j).code : ℕ)) =
      krCode (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s))
        (fun i j => frobCode (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s) i j)) := by
  funext r c
  rw [code_kr]
  have h1 : (fun i j => ((Matrix.transvection (pairOf s).1 (pairOf s).2 (coefOf s) i j).code : ℕ)) =
      trCode3 (pairOf s).1 (pairOf s).2 (coefCode s) := by
    funext i j
    rw [code_transvection3 (pairOf_ne s), code_coefOf]
  have h2 : (fun i j =>
      ((frob3 (Matrix.transvection (pairOf s).1 (pairOf s).2 (coefOf s)) i j).code : ℕ)) =
      fun i j => frobCode (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s) i j) := by
    funext i j
    rw [frob3_apply, code_frobF4, code_transvection3 (pairOf_ne s), code_coefOf]
  rw [h1, h2]

theorem kact_gen3_bits (s : Fin 12) :
    kact (gen3 s) = toMat 18 18 (kactBits (trCode3 (pairOf s).1 (pairOf s).2 (coefCode s))) := by
  rw [kact_eq, coe_gen3, kactBits, toMat_bmul, toMat_bmul, conjP_apply, pcM, pciM, ← codes_kr_gen3,
    toMat_reBits9]

theorem kact_gen3 (s : Fin 12) :
    kact (gen3 s) = bdN (n := 9) (genA s) (genA s) := by
  have h := kGenCheck_eq_true
  simp only [kGenCheck, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies] at h
  rw [kact_gen3_bits, h s, toMat_bd9Bits]
  rfl

noncomputable abbrev st3 (a b : Fin 3) (c : F4) : SL3 := stT (F := F4) (m := 2) (by norm_num) a b c

theorem st3_inv (a b : Fin 3) (c : F4) : (st3 a b c)⁻¹ = st3 a b c :=
  inv_eq_of_mul_eq_one_right (stT_mul_self _ a b c)

theorem pairOf_genIdx {a b : Fin 3} (hab : a ≠ b) (β : Fin 2) : pairOf (genIdx a b β) = (a, b) := by
  revert a b β; decide

theorem coefOf_genIdx (a b : Fin 3) (β : Fin 2) : coefOf (genIdx a b β) = ⟨Fin.ofNat 4 (β + 1)⟩ :=
  f4_ext (by revert a b β; decide)

theorem gen3_genIdx {a b : Fin 3} (hab : a ≠ b) (β : Fin 2) :
    gen3 (genIdx a b β) = st3 a b ⟨Fin.ofNat 4 (β + 1)⟩ := by
  rw [gen3, pairOf_genIdx hab, coefOf_genIdx]

@[expose] def ulBlock (M : Mat18) : Mat9 :=
  Matrix.of fun i j => M (Fin.castAdd 9 i) (Fin.castAdd 9 j)

theorem ulBlock_bdN (A B : Mat9) : ulBlock (bdN (n := 9) A B) = A := by
  ext i j; exact bdN_cc A B i j

@[expose] def KDiag (g : SL3) : Prop := kact g = bdN (n := 9) (ulBlock (kact g)) (ulBlock (kact g))

theorem kDiag_one : KDiag 1 := by
  rw [KDiag, map_one]
  have : ulBlock (1 : Mat18) = 1 := by rw [← bdN_one (n := 9), ulBlock_bdN]
  rw [this, bdN_one]

theorem kDiag_mul {g h : SL3} (hg : KDiag g) (hh : KDiag h) : KDiag (g * h) := by
  rw [KDiag] at *
  rw [map_mul, hg, hh, bdN_mul, ulBlock_bdN]

theorem kDiag_gen3 (s : Fin 12) : KDiag (gen3 s) := by
  rw [KDiag, kact_gen3, ulBlock_bdN]

theorem kDiag_st3 (a b : Fin 3) (c : F4) : KDiag (st3 a b c) := by
  by_cases hab : a = b
  · subst hab
    rw [st3, stT_diag]
    exact kDiag_one
  · have h1 := gen3_genIdx hab 0
    have h2 := gen3_genIdx hab 1
    have h0 : KDiag (st3 a b ⟨0⟩) := by
      rw [st3, show (⟨0⟩ : F4) = 0 from rfl, stT_zero]
      exact kDiag_one
    have hω1 : KDiag (st3 a b ⟨1⟩) := by
      have e : st3 a b ⟨1⟩ = gen3 (genIdx a b ((0 : Fin 2) : ℕ)) := by rw [h1]; rfl
      rw [e]; exact kDiag_gen3 _
    have hω2 : KDiag (st3 a b ⟨2⟩) := by
      have e : st3 a b ⟨2⟩ = gen3 (genIdx a b ((1 : Fin 2) : ℕ)) := by rw [h2]; rfl
      rw [e]; exact kDiag_gen3 _
    have hω3 : KDiag (st3 a b ⟨3⟩) := by
      have e : st3 a b ⟨3⟩ = st3 a b ⟨1⟩ * st3 a b ⟨2⟩ := by
        rw [st3, st3, st3, stT_add _ hab]
        rfl
      rw [e]; exact kDiag_mul hω1 hω2
    rcases c with ⟨k⟩
    fin_cases k
    · exact h0
    · exact hω1
    · exact hω2
    · exact hω3

theorem kDiag_all (g : SL3) : KDiag g := by
  have hg : g ∈ Subgroup.closure (Set.range fun p : Fin 3 × Fin 3 × F4 =>
      stT (F := F4) (m := 2) (by norm_num) p.1 p.2.1 p.2.2) := by
    rw [closure_stT]; exact Subgroup.mem_top g
  rw [← Subgroup.mem_toSubmonoid, Subgroup.closure_toSubmonoid] at hg
  induction hg using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨p, rfl⟩ | ⟨p, hp⟩
    · exact kDiag_st3 _ _ _
    · have : x = st3 p.1 p.2.1 p.2.2 := by
        rw [← inv_inv x, ← hp, st3_inv]
      rw [this]; exact kDiag_st3 _ _ _
  | one => exact kDiag_one
  | mul x y _ _ hx hy => exact kDiag_mul hx hy

@[expose] noncomputable def rhoA : SL3 →* Mat9 where
  toFun g := ulBlock (kact g)
  map_one' := by
    rw [map_one, ← bdN_one (n := 9), ulBlock_bdN]
  map_mul' g h := by
    rw [map_mul, kDiag_all g, kDiag_all h, bdN_mul, ulBlock_bdN, ulBlock_bdN, ulBlock_bdN]

theorem kact_eq_rhoN (g : SL3) : kact g = rhoN (rhoA g) := by
  rw [← bdN_self]; exact kDiag_all g

theorem rhoA_gen3 (s : Fin 12) : rhoA (gen3 s) = genA s := by
  change ulBlock (kact (gen3 s)) = genA s
  rw [kact_gen3, ulBlock_bdN]

theorem st3_eq_gen3_or {a b : Fin 3} (hab : a ≠ b) (c : F4) :
    st3 a b c = 1 ∨ st3 a b c = gen3 (genIdx a b 0) ∨ st3 a b c = gen3 (genIdx a b 1) ∨
      st3 a b c = gen3 (genIdx a b 0) * gen3 (genIdx a b 1) := by
  have h1 := gen3_genIdx hab 0
  have h2 := gen3_genIdx hab 1
  simp only [Fin.val_zero, Fin.val_one, zero_add, Fin.isValue] at h1 h2
  have e3 : gen3 (genIdx a b 0) * gen3 (genIdx a b 1) = st3 a b ⟨3⟩ := by
    rw [h1, h2, st3, st3, st3, stT_add _ hab]
    rfl
  rcases c with ⟨k⟩
  fin_cases k
  · left; exact stT_zero _ a b
  · right; left; exact h1.symm
  · right; right; left; exact h2.symm
  · right; right; right; exact e3.symm

theorem hom_ext_gen3 {M : Type*} [Monoid M] {f g : SL3 →* M}
    (h : ∀ s, f (gen3 s) = g (gen3 s)) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense (closure_stT (F := F4) (m := 2) (by norm_num)) ?_
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  change f (st3 a b c) = g (st3 a b c)
  by_cases hab : a = b
  · subst hab
    rw [st3, stT_diag, map_one, map_one]
  · rcases st3_eq_gen3_or hab c with e | e | e | e <;> rw [e]
    · rw [map_one, map_one]
    · exact h _
    · exact h _
    · rw [map_mul, map_mul, h, h]

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
