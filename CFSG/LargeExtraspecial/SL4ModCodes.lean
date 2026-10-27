module

public import CFSG.Sporadic.HS.SmallF2Spec
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LargeExtraspecial.SL4ModNativeBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Matrix CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Native
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular
  card_unitriangular)

abbrev SL4 : Type := SpecialLinearGroup (Fin 4) (ZMod 2)

abbrev U : Subgroup SL4 := unitriangular 4 (ZMod 2)

@[expose] def HasCode (g : SL4) (R : Array ℕ) : Prop :=
  (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = rowsMatrix 4 R

@[expose] def toMat (g : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2) := g.val

theorem HasCode.toMat_eq {g : SL4} {R : Array ℕ} (hg : HasCode g R) : toMat g = rowsMatrix 4 R :=
  hg

theorem HasCode.mul {g h : SL4} {R R' : Array ℕ} (hg : HasCode g R) (hh : HasCode h R') :
    HasCode (g * h) (mul4 R R') := by
  have hg' : g.val = rowsMatrix 4 R := hg
  have hh' : h.val = rowsMatrix 4 R' := hh
  change (g * h).val = rowsMatrix 4 (mul4 R R')
  rw [show (g * h).val = g.val * h.val from rfl, hg', hh', mul4, rowsMatrix_mulRows]

theorem hasCode_one : HasCode 1 id4 := by
  change (1 : SL4).val = rowsMatrix 4 id4
  rw [show (1 : SL4).val = 1 from rfl, id4, rowsMatrix_idRows]

theorem HasCode.eq {g h : SL4} {R R' : Array ℕ} (hg : HasCode g R) (hh : HasCode h R')
    (hR : R = R') : g = h :=
  Subtype.ext (hg.trans (hR ▸ hh.symm))

theorem det_rowsMatrix_of_mul {R R' : Array ℕ} (h : mul4 R R' = id4) :
    (rowsMatrix 4 R).det = 1 := by
  have hm : rowsMatrix 4 R * rowsMatrix 4 R' = 1 := by
    rw [← rowsMatrix_mulRows, ← mul4, h, id4, rowsMatrix_idRows]
  have hd := congrArg Matrix.det hm
  rw [det_mul, det_one] at hd
  have hne : (rowsMatrix 4 R).det ≠ 0 := left_ne_zero_of_mul_eq_one hd
  generalize (rowsMatrix 4 R).det = d at hne ⊢
  revert d
  decide

theorem rowsMatrix_uCode (e : ℕ) (r c : Fin 4) :
    rowsMatrix 4 (uCode e) r c =
      if (c.val == r.val || (decide (r.val < c.val) && e.testBit (uIdx r.val c.val))) = true
      then 1 else 0 := by
  rw [rowsMatrix_apply]
  unfold uCode
  rw [Array.getElem?_ofFn]
  simp only [r.isLt, ↓reduceDIte, Option.getD_some]
  unfold uRow
  rw [toVecD_ofBits]

theorem uCode_isUpper (e : ℕ) (r c : Fin 4) (h : c < r) : rowsMatrix 4 (uCode e) r c = 0 := by
  rw [rowsMatrix_uCode]
  have h1 : (c.val == r.val) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h' => (ne_of_lt h) (Fin.ext h')
  have h2 : decide (r.val < c.val) = false := by
    rw [decide_eq_false_iff_not]
    exact not_lt.mpr (le_of_lt h)
  rw [h1, h2]
  rfl

theorem uCode_diag (e : ℕ) (r : Fin 4) : rowsMatrix 4 (uCode e) r r = 1 := by
  rw [rowsMatrix_uCode]
  simp

@[expose] def uSL (e : ℕ) : SL4 :=
  ⟨rowsMatrix 4 (uCode e), by
    rw [det_of_isUpperTriangular (fun r c h => uCode_isUpper e r c h)]
    exact Finset.prod_eq_one fun r _ => uCode_diag e r⟩

theorem hasCode_uSL (e : ℕ) : HasCode (uSL e) (uCode e) := rfl

theorem uSL_mem (e : ℕ) : uSL e ∈ U :=
  mem_unitriangular.mpr ⟨fun r c h => uCode_isUpper e r c h, fun r => uCode_diag e r⟩

theorem rowsMatrix_of_isUCode {R : Array ℕ} (h : isUCode R = true) :
    (∀ r c : Fin 4, c < r → rowsMatrix 4 R r c = 0) ∧ ∀ r : Fin 4, rowsMatrix 4 R r r = 1 := by
  unfold isUCode at h
  rw [List.all_eq_true] at h
  have key : ∀ r c : Fin 4, (if c.val < r.val then !((R[r.val]?.getD 0).testBit c.val)
      else if c.val = r.val then (R[r.val]?.getD 0).testBit c.val else true) = true := by
    intro r c
    have := h r.val (List.mem_range.mpr r.isLt)
    rw [List.all_eq_true] at this
    exact this c.val (List.mem_range.mpr c.isLt)
  refine ⟨fun r c hrc => ?_, fun r => ?_⟩
  · have := key r c
    rw [ite_eq_left (show c.val < r.val from hrc), Bool.not_eq_true'] at this
    rw [rowsMatrix_apply, toVecD_apply, this]
    rfl
  · have := key r r
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl] at this
    rw [rowsMatrix_apply, toVecD_apply, this]
    rfl

theorem HasCode.mem_U {g : SL4} {R : Array ℕ} (hg : HasCode g R) (h : isUCode R = true) :
    g ∈ U := by
  obtain ⟨h1, h2⟩ := rowsMatrix_of_isUCode h
  refine mem_unitriangular.mpr ⟨fun r c hrc => ?_, fun r => ?_⟩
  · have hg' : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = rowsMatrix 4 R := hg
    rw [hg']
    exact h1 r c hrc
  · have hg' : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = rowsMatrix 4 R := hg
    rw [hg']
    exact h2 r


section Act

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (σ : SL4 →* (M ≃ₗ[ZMod 2] M))

theorem act_mul (g h : SL4) (y : M) : σ (g * h) y = σ g (σ h y) := by
  rw [map_mul, LinearEquiv.mul_apply]

theorem act_one (y : M) : σ 1 y = y := by
  rw [map_one]
  rfl

end Act

theorem genCode_mul_self (n : ℕ) : mul4 (genCode n) (genCode n) = id4 := by
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | 4 => decide +kernel
  | 5 => decide +kernel
  | _ + 6 => exact (by decide +kernel : mul4 #[1, 2, 4, 8] #[1, 2, 4, 8] = id4)

@[expose] def genN (n : ℕ) : SL4 :=
  ⟨rowsMatrix 4 (genCode n), det_rowsMatrix_of_mul (genCode_mul_self n)⟩

theorem hasCode_genN (n : ℕ) : HasCode (genN n) (genCode n) := rfl

theorem genN_mul_self (n : ℕ) : genN n * genN n = 1 :=
  ((hasCode_genN n).mul (hasCode_genN n)).eq hasCode_one (genCode_mul_self n)

theorem genN_inv (n : ℕ) : (genN n)⁻¹ = genN n := inv_eq_of_mul_eq_one_right (genN_mul_self n)

@[expose] def xx (i : Fin 3) : SL4 := genN i.val

@[expose] def nn (i : Fin 3) : SL4 := genN (i.val + 3)

theorem xx_mul_self (i : Fin 3) : xx i * xx i = 1 := genN_mul_self _

theorem nn_mul_self (i : Fin 3) : nn i * nn i = 1 := genN_mul_self _

theorem nn_inv (i : Fin 3) : (nn i)⁻¹ = nn i := genN_inv _

theorem xx_mem (i : Fin 3) : xx i ∈ U :=
  (hasCode_genN i.val).mem_U (by fin_cases i <;> decide +kernel)

@[expose] def wordProd (w : List ℕ) : SL4 := (w.map genN).prod

theorem wordProd_cons (s : ℕ) (w : List ℕ) : wordProd (s :: w) = genN s * wordProd w := by
  simp [wordProd]

theorem hasCode_wordProd (w : List ℕ) : HasCode (wordProd w) (wordCode w) := by
  induction w with
  | nil => exact hasCode_one
  | cons s w ih =>
    rw [wordProd_cons]
    exact (hasCode_genN s).mul ih

@[expose] def uDecM (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : ℕ :=
  (A 0 1).val + 2 * (A 0 2).val + 4 * (A 0 3).val + 8 * (A 1 2).val + 16 * (A 1 3).val +
    32 * (A 2 3).val

theorem uDecM_rowsMatrix (R : Array ℕ) : uDecM (rowsMatrix 4 R) = uDecC R := by
  have key : ∀ r c : Fin 4, (rowsMatrix 4 R r c).val = bitAt R r.val c.val := by
    intro r c
    rw [rowsMatrix_apply, toVecD_apply, bitAt]
    split_ifs <;> rfl
  rw [uDecM, uDecC, key 0 1, key 0 2, key 0 3, key 1 2, key 1 3, key 2 3]
  rfl

theorem uDecC_uCode : ∀ e < 64, uDecC (uCode e) = e := by decide +kernel

theorem uSL_injective {e e' : ℕ} (he : e < 64) (he' : e' < 64) (h : uSL e = uSL e') :
    e = e' := by
  have h1 : uDecM (uSL e).val = e := by
    rw [show (uSL e).val = rowsMatrix 4 (uCode e) from rfl, uDecM_rowsMatrix, uDecC_uCode e he]
  have h2 : uDecM (uSL e').val = e' := by
    rw [show (uSL e').val = rowsMatrix 4 (uCode e') from rfl, uDecM_rowsMatrix,
      uDecC_uCode e' he']
  rw [← h1, ← h2, h]

theorem natCard_U : Nat.card U = 64 := by
  rw [card_unitriangular, Nat.card_zmod]
  norm_num

theorem isPGroup_U : IsPGroup 2 U := IsPGroup.of_card (n := 6) (by rw [natCard_U]; norm_num)

theorem exists_uSL {u : SL4} (hu : u ∈ U) : ∃ e < 64, uSL e = u := by
  let f : Fin 64 → U := fun e => ⟨uSL e.val, uSL_mem _⟩
  have hinj : Function.Injective f := fun a b h =>
    Fin.ext (uSL_injective a.isLt b.isLt (congrArg Subtype.val h))
  have hbij := hinj.bijective_of_nat_card_le (by rw [natCard_U, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  obtain ⟨e, he⟩ := hbij.2 ⟨u, hu⟩
  exact ⟨e.val, e.isLt, congrArg Subtype.val he⟩

@[expose] def twW : Fin 4 → Fin 4 → List ℕ
  | 0, 1 => [0]
  | 0, 2 => [3, 1, 3]
  | 0, 3 => [3, 4, 2, 4, 3]
  | 1, 0 => [0, 3, 0]
  | 1, 2 => [1]
  | 1, 3 => [4, 2, 4]
  | 2, 0 => [3, 1, 4, 1, 3]
  | 2, 1 => [1, 4, 1]
  | 2, 3 => [2]
  | 3, 0 => [3, 4, 2, 5, 2, 4, 3]
  | 3, 1 => [4, 2, 5, 2, 4]
  | 3, 2 => [2, 5, 2]
  | _, _ => []

theorem twW_spec :
    ∀ i j : Fin 4, i ≠ j → rowsMatrix 4 (wordCode (twW i j)) = transvection i j 1 := by
  decide +kernel

theorem twW_lt : ∀ i j : Fin 4, ∀ s ∈ twW i j, s < 6 := by decide +kernel

abbrev genClosure : Subgroup SL4 := Subgroup.closure (Set.range fun s : Fin 6 => genN s.val)

theorem wordProd_mem_closure {w : List ℕ} (hw : ∀ s ∈ w, s < 6) : wordProd w ∈ genClosure := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons s w ih =>
    rw [wordProd_cons]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨s, hw s (by simp)⟩, rfl⟩)
      (ih fun t ht => hw t (List.mem_cons_of_mem s ht))

theorem closure_gen : genClosure = ⊤ := by
  have htr : ∀ t : TransvectionStruct (Fin 4) (ZMod 2), t.toSpecialLinearGroup ∈ genClosure := by
    intro t
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t.c with hc | hc
    · have : t.toSpecialLinearGroup = 1 := by
        apply Subtype.ext
        change t.toMatrix = 1
        rw [TransvectionStruct.toMatrix, hc, transvection_zero]
      rw [this]
      exact Subgroup.one_mem _
    · have : t.toSpecialLinearGroup = wordProd (twW t.i t.j) := by
        apply Subtype.ext
        change t.toMatrix = (wordProd (twW t.i t.j)).val
        rw [show (wordProd (twW t.i t.j)).val = _ from hasCode_wordProd _,
          twW_spec t.i t.j t.hij, TransvectionStruct.toMatrix, hc]
      rw [this]
      exact wordProd_mem_closure (twW_lt t.i t.j)
  refine eq_top_iff.mpr fun M _ => ?_
  obtain ⟨L, L', D, hD, hM⟩ :=
    SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hD1 : (⟨diagonal D, hD⟩ : SL4) = (1 : SL4) := by
    have hprod : ∏ i, D i = 1 := by rwa [det_diagonal] at hD
    have hDi : ∀ i, D i = 1 := fun i => by
      have hne : D i ≠ 0 := fun h0 => by
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hprod
        exact zero_ne_one hprod
      have : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact this _ hne
    ext i j
    change diagonal D i j = (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j
    rw [show D = fun _ => 1 from funext hDi, diagonal_one]
  rw [hM, hD1, mul_one]
  refine Subgroup.mul_mem _ (Subgroup.list_prod_mem _ fun x hx => ?_)
    (Subgroup.list_prod_mem _ fun x hx => ?_)
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact htr t
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact htr t

end CFSG.LargeExtraspecial.SL4Mod
