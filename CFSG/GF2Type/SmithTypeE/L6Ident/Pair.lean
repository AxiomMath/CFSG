module

public import CFSG.GF2Type.SmithTypeE.L6Ident.E261
public import Certificates.Certificate38670

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open Subgroup CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod CFSG.GF2Type.SmithTypeE.L6
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor eq_of_decode_eq)
open CFSG.LargeExtraspecial.S14

theorem dec6_one : dec6 1 = Pi.single 0 1 := by
  funext i
  fin_cases i <;> rfl

theorem dec6_two : dec6 2 = Pi.single 1 1 := by
  funext i
  fin_cases i <;> rfl

section Checks


theorem stdPairCheck_holds : prChkStd = true := Certificates.certificate38670.1

theorem ord4Check_holds : prChkOrd4 = true := Certificates.certificate38670.2.1

theorem f3Check_holds : prChkF3 = true := Certificates.certificate38670.2.2

theorem stdPair_parts :
    tvPair 0 = (1, 2) ∧ tvPair 31 = (2, 1) ∧ stabRep 6 = 31 ∧ prOrd3 = true := by
  have h := stdPairCheck_holds
  simp only [prChkStd, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem tv_std_parts : tvVec 0 = Pi.single 0 1 ∧ tvForm 0 = Pi.single 1 1 ∧
    tvVec 31 = Pi.single 1 1 ∧ tvForm 31 = Pi.single 0 1 := by
  obtain ⟨h0, h31, -, -⟩ := stdPair_parts
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tvVec, h0]
    exact dec6_one
  · rw [tvForm, h0]
    exact dec6_two
  · rw [tvVec, h31]
    exact dec6_two
  · rw [tvForm, h31]
    exact dec6_one

end Checks

theorem fin_val_zero : ((0 : Fin 1953) : ℕ) = 0 := rfl

theorem fin_val_31 : ((31 : Fin 1953) : ℕ) = 31 := rfl

theorem pow_three_eq_one_of_apply {α : Type*} (p q : Equiv.Perm α)
    (h : ∀ x, p (q (p (q (p (q x))))) = x) : (p * q) ^ 3 = 1 := by
  refine Equiv.ext fun x => ?_
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id]
  exact h x

theorem pow_four_eq_one_of_apply {α : Type*} (p q : Equiv.Perm α)
    (h : ∀ x, p (q (p (q (p (q (p (q x))))))) = x) : (p * q) ^ 4 = 1 := by
  refine Equiv.ext fun x => ?_
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one, id]
  exact h x

section Commuting


theorem tvImg_eq_self_of_commute {k j : Fin 1953} (h : Commute (tvP k) (tvP j)) :
    tvImg k j = j := by
  have h1 := mul_tvP_mul_inv (tvP_mem k) j
  rw [h.eq, mul_inv_cancel_right] at h1
  have h2 := tvP_injective h1
  rw [← tvP_apply, ← h2]

theorem commute_tvP_of_conj {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) {a b : Fin 1953}
    (h : Commute (tvP (g a)) (tvP (g b))) : Commute (tvP a) (tvP b) := by
  rw [← mul_tvP_mul_inv hg a, ← mul_tvP_mul_inv hg b] at h
  have h2 := commute_conj_inv g h
  have e : ∀ x : Equiv.Perm (Fin 1953), g⁻¹ * (g * x * g⁻¹) * g = x := fun x => by group
  rwa [e, e] at h2

theorem commute_tvP_conj {g : Equiv.Perm (Fin 1953)} (hg : g ∈ T6) {a b : Fin 1953}
    (h : Commute (tvP a) (tvP b)) : Commute (tvP (g a)) (tvP (g b)) := by
  rw [← mul_tvP_mul_inv hg a, ← mul_tvP_mul_inv hg b]
  have h2 := commute_conj_inv g⁻¹ h
  simpa only [inv_inv] using h2

end Commuting

section Ord4


theorem orderOf_ne_three_of_stabCls_ne {a : Fin 1953} (ha : stabCls a ≠ 6) :
    orderOf (tvP 0 * tvP a) ≠ 3 := by
  have h := ord4Check_holds
  simp only [prChkOrd4, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have hx := h a a.2
  simp only [ha, false_or, prOrd4, List.all_eq_true, List.mem_range, beq_iff_eq] at hx
  have h4 : (tvP 0 * tvP a) ^ 4 = 1 := by
    refine pow_four_eq_one_of_apply _ _ fun x => Fin.ext ?_
    simp only [tvP_apply, Fin.val_zero]
    exact hx x x.2
  intro h3
  have := orderOf_dvd_of_pow_eq_one h4
  rw [h3] at this
  omega

theorem orderOf_std : orderOf (tvP 0 * tvP 31) = 3 := by
  obtain ⟨-, -, -, h⟩ := stdPair_parts
  simp only [prOrd3, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h3 : (tvP 0 * tvP 31) ^ 3 = 1 := by
    refine pow_three_eq_one_of_apply _ _ fun x => Fin.ext ?_
    simp only [tvP_apply, fin_val_zero, fin_val_31]
    exact h x x.2
  have hne : tvP 0 * tvP 31 ≠ 1 := fun h1 => by
    have h2 : tvP 31 = tvP 0 := by
      rw [eq_inv_of_mul_eq_one_right h1, tvP_inv]
    exact absurd (tvP_injective h2) (by decide)
  exact orderOf_eq_prime h3 hne

end Ord4

section Pairs


theorem exists_mem_T6_of_stabCls_six (a : Fin 1953) (ha : stabCls a = 6) :
    ∃ g ∈ T6, g 0 = 0 ∧ g 31 = a := by
  refine stab_reach (fun j => ∀ hj : j < 1953, stabCls j = 6 →
    ∃ g ∈ T6, g 0 = 0 ∧ g 31 = ⟨j, hj⟩) ?_ ?_ a.val a.2 a.2 ha
  · intro v _ hr hv hv6
    refine ⟨1, T6.one_mem, rfl, ?_⟩
    apply Fin.ext
    have : v = 31 := by rw [beq_iff_eq.mp hr, hv6, stdPair_parts.2.2.1]
    subst this
    rfl
  · intro g hg u hu v _ he hQ hv hv6
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hg0, hgu⟩, hcls⟩ := he
    obtain ⟨c, hc, hc0, hc31⟩ := hQ hu (hcls ▸ hv6)
    refine ⟨tvP ⟨g, hg⟩ * c, T6.mul_mem (tvP_mem _) hc, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hc0]
      exact Fin.ext (by rw [tvP_apply]; exact hg0)
    · rw [Equiv.Perm.mul_apply, hc31]
      exact Fin.ext (by rw [tvP_apply]; exact hgu)

theorem exists_mem_T6_pair {kt ku : Fin 1953} (h : orderOf (tvP kt * tvP ku) = 3) :
    ∃ g ∈ T6, g 0 = kt ∧ g 31 = ku := by
  obtain ⟨g₁, hg₁, hg₁0⟩ := exists_mem_T6_apply_zero_eq kt
  have hg₁a : g₁ (g₁⁻¹ ku) = ku := by simp
  have hord : orderOf (tvP 0 * tvP (g₁⁻¹ ku)) = 3 := by
    have e : g₁ * (tvP 0 * tvP (g₁⁻¹ ku)) * g₁⁻¹ = tvP kt * tvP ku := by
      have h0 := mul_tvP_mul_inv hg₁ 0
      have h1 := mul_tvP_mul_inv hg₁ (g₁⁻¹ ku)
      rw [hg₁0] at h0
      rw [hg₁a] at h1
      calc g₁ * (tvP 0 * tvP (g₁⁻¹ ku)) * g₁⁻¹
          = (g₁ * tvP 0 * g₁⁻¹) * (g₁ * tvP (g₁⁻¹ ku) * g₁⁻¹) := by group
        _ = tvP kt * tvP ku := by rw [h0, h1]
    have e' : orderOf (MulAut.conj g₁ (tvP 0 * tvP (g₁⁻¹ ku))) = orderOf (tvP kt * tvP ku) := by
      rw [MulAut.conj_apply, e]
    rw [MulEquiv.orderOf_eq] at e'
    rw [e', h]
  have hcls : stabCls (g₁⁻¹ ku) = 6 := by
    by_contra hne
    exact orderOf_ne_three_of_stabCls_ne hne hord
  obtain ⟨g₂, hg₂, hg₂0, hg₂31⟩ := exists_mem_T6_of_stabCls_six _ hcls
  refine ⟨g₁ * g₂, T6.mul_mem hg₁ hg₂, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hg₂0, hg₁0]
  · rw [Equiv.Perm.mul_apply, hg₂31, hg₁a]

end Pairs

theorem foldl_range_lt (F : ℕ → ℕ → ℕ) (hF : ∀ acc t, acc < 2 ^ t → F acc t < 2 ^ (t + 1)) :
    ∀ n, (List.range n).foldl F 0 < 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact hF _ n ih

theorem wedge3_lt (a b c : ℕ) : wedge3 a b c < 2 ^ 20 := by
  unfold wedge3
  refine foldl_range_lt _ ?_ 20
  intro acc t hacc
  have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
  split
  split_ifs
  · exact Nat.or_lt_two_pow (by omega) (by omega)
  · omega

theorem wt_lt_two_pow (i : ℕ) : wt i < 2 ^ 20 := by
  unfold wt
  generalize wB i = p
  obtain ⟨a, b, c⟩ := p
  exact wedge3_lt a b c

section Vec


theorem inE_of_vec {k : Fin 1953} {i : ℕ} {v : V} (h : tvEquiv k.val v + v = wtV i) :
    InE k.val i := by
  refine ⟨SMG.code v, SMG.code_lt v, ?_⟩
  rw [← code_tvEquiv k.2 v, ← SMG.code_add, h, wtV, code_decode' (wt_lt_two_pow i)]

theorem vec_of_inE {k : Fin 1953} {i : ℕ} (h : InE k.val i) :
    ∃ v : V, tvEquiv k.val v + v = wtV i := by
  obtain ⟨c, -, h⟩ := h
  refine ⟨decode c, ?_⟩
  rw [tvEquiv_decode k.2, ← decode_xor, h]
  rfl

theorem fix_of_vec {k : Fin 1953} {i : ℕ} (h : tvEquiv k.val (wtV i) = wtV i) :
    applyCols (tvCols k.val) (wt i) = wt i := by
  refine eq_of_decode_eq (applyCols_tvCols_lt' k.2 _) (wt_lt_two_pow i) ?_
  rw [← tvEquiv_decode k.2]
  exact h

theorem vec_of_fix {k : Fin 1953} {i : ℕ} (h : applyCols (tvCols k.val) (wt i) = wt i) :
    tvEquiv k.val (wtV i) = wtV i := by
  rw [wtV, tvEquiv_decode k.2, h]

end Vec

section Transport


theorem rhoMod_tvEquiv (g : T6) (k : Fin 1953) (v : V) :
    rhoMod g (tvEquiv k.val v) = tvEquiv ((g : Equiv.Perm (Fin 1953)) k).val (rhoMod g v) := by
  have h := rhoMod_conj_tvEquiv g k
  have h2 := congrArg (fun L : V ≃ₗ[ZMod 2] V => L (rhoMod g v)) h
  simpa using h2

theorem transport_inE (g : T6) {k : Fin 1953} {i : Fin 1395} (h : InE k.val i.val) :
    InE ((g : Equiv.Perm (Fin 1953)) k).val (g • i).val := by
  obtain ⟨v, hv⟩ := vec_of_inE h
  refine inE_of_vec (v := rhoMod g v) ?_
  rw [← rhoMod_tvEquiv, ← map_add, hv, rhoMod_wtV]

theorem transport_fix (g : T6) {k : Fin 1953} {i : Fin 1395}
    (h : applyCols (tvCols k.val) (wt i.val) = wt i.val) :
    applyCols (tvCols ((g : Equiv.Perm (Fin 1953)) k).val) (wt (g • i).val) = wt (g • i).val := by
  refine fix_of_vec ?_
  have h1 := vec_of_fix h
  have h2 := congrArg (rhoMod g) h1
  rw [rhoMod_tvEquiv, rhoMod_wtV] at h2
  exact h2

end Transport

section F3Std


theorem f3_std {k : Fin 1953} (h0 : Commute (tvP k) (tvP 0)) (h31 : Commute (tvP k) (tvP 31)) :
    ∃ i < 1395, InE k.val i ∧ applyCols (tvCols 0) (wt i) = wt i ∧
      applyCols (tvCols 31) (wt i) = wt i := by
  have h := f3Check_holds
  simp only [prChkF3, List.all_eq_true, List.mem_range] at h
  have hk := h k k.2
  have e0 := tvImg_eq_self_of_commute h0
  have e31 := tvImg_eq_self_of_commute h31
  rw [fin_val_zero] at e0
  rw [fin_val_31] at e31
  simp only [e0, e31, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨hi, hc⟩, hC⟩, hD⟩, hE⟩ := hk
  exact ⟨prIdx k.val, hi, ⟨prC k.val, hc, hC⟩, hD, hE⟩

end F3Std

section F3


theorem hF3_holds : ∀ kt ku k : Fin 1953, orderOf (tvP kt * tvP ku) = 3 →
    Commute (tvP k) (tvP kt) → Commute (tvP k) (tvP ku) → ∃ i < 1395, InE k i ∧
      applyCols (tvCols kt) (wt i) = wt i ∧ applyCols (tvCols ku) (wt i) = wt i := by
  intro kt ku k hord h1 h2
  obtain ⟨g, hg, hg0, hg31⟩ := exists_mem_T6_pair hord
  have hkk : g (g⁻¹ k) = k := by simp
  have hc0 : Commute (tvP (g⁻¹ k)) (tvP 0) :=
    commute_tvP_of_conj hg (by rw [hkk, hg0]; exact h1)
  have hc31 : Commute (tvP (g⁻¹ k)) (tvP 31) :=
    commute_tvP_of_conj hg (by rw [hkk, hg31]; exact h2)
  obtain ⟨i, hi, hE, hf0, hf31⟩ := f3_std hc0 hc31
  let gT : T6 := ⟨g, hg⟩
  refine ⟨(gT • (⟨i, hi⟩ : Fin 1395)).val, (gT • (⟨i, hi⟩ : Fin 1395)).2, ?_, ?_, ?_⟩
  · have := transport_inE gT (k := g⁻¹ k) (i := ⟨i, hi⟩) hE
    rwa [show (gT : Equiv.Perm (Fin 1953)) (g⁻¹ k) = k from hkk] at this
  · have := transport_fix gT (k := 0) (i := ⟨i, hi⟩) hf0
    rwa [show (gT : Equiv.Perm (Fin 1953)) 0 = kt from hg0] at this
  · have := transport_fix gT (k := 31) (i := ⟨i, hi⟩) hf31
    rwa [show (gT : Equiv.Perm (Fin 1953)) 31 = ku from hg31] at this

end F3

section Block

open Matrix
open scoped MatrixGroups

abbrev e24 : Fin 2 ⊕ Fin 4 ≃ Fin 6 := finSumFinEquiv

@[expose] def blkMat (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e24 (Matrix.fromBlocks 1 0 0 A)

theorem blkMat_one : blkMat 1 = 1 := by
  simp [blkMat, Matrix.fromBlocks_one]

theorem blkMat_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    blkMat (A * B) = blkMat A * blkMat B := by
  simp only [blkMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem det_blkMat (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : (blkMat A).det = A.det := by
  rw [blkMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

theorem blkMat_injective : Function.Injective blkMat := by
  intro A B h
  have := (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e24).injective h
  exact (Matrix.fromBlocks_inj.mp this).2.2.2

@[expose] def embSL : SL(4, ZMod 2) →* SL(6, ZMod 2) where
  toFun A := (⟨blkMat A, by rw [det_blkMat]; exact A.2⟩ : SL(6, ZMod 2))
  map_one' := Subtype.ext blkMat_one
  map_mul' A B := Subtype.ext (blkMat_mul A.1 B.1)

theorem embSL_injective : Function.Injective embSL := fun A B h =>
  Subtype.ext (blkMat_injective (congrArg Subtype.val h))

@[expose] def ext0 (v : Fin 4 → ZMod 2) : Fin 6 → ZMod 2 :=
  Sum.elim (0 : Fin 2 → ZMod 2) v ∘ e24.symm

theorem ext0_inr (v : Fin 4 → ZMod 2) (x : Fin 4) : ext0 v (e24 (Sum.inr x)) = v x := by
  simp [ext0]

theorem ext0_inl (v : Fin 4 → ZMod 2) (x : Fin 2) : ext0 v (e24 (Sum.inl x)) = 0 := by
  simp [ext0]

theorem blkMat_transvec (v φ : Fin 4 → ZMod 2) :
    blkMat (1 + vecMulVec v φ) = 1 + vecMulVec (ext0 v) (ext0 φ) := by
  ext a b
  obtain ⟨x, rfl⟩ := e24.surjective a
  obtain ⟨y, rfl⟩ := e24.surjective b
  rcases x with x | x <;> rcases y with y | y <;>
    simp [blkMat, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      ext0, Matrix.one_apply, vecMulVec_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

theorem ext0_ne_zero {v : Fin 4 → ZMod 2} (hv : v ≠ 0) : ext0 v ≠ 0 := fun h =>
  hv (funext fun x => by simpa [ext0_inr] using congrFun h (e24 (Sum.inr x)))

theorem dotProduct_ext0 (φ v : Fin 4 → ZMod 2) : ext0 φ ⬝ᵥ ext0 v = φ ⬝ᵥ v := by
  unfold dotProduct
  rw [← Equiv.sum_comp e24 (fun a => ext0 φ a * ext0 v a), Fintype.sum_sum_type]
  simp [ext0_inl, ext0_inr]

theorem eq_top_of_elementary_gen {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (S : Subgroup (SpecialLinearGroup ι (ZMod 2)))
    (h : ∀ i j : ι, ∀ hij : i ≠ j, SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ S) :
    S = ⊤ := by
  refine (Subgroup.eq_top_iff' S).mpr fun M => ?_
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun A => A ∈ S) M ?_ ?_ ?_
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) c hc
    subst hc1
    have hone : SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      ext k l
      by_cases hkl : k = l <;>
        simp [SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply, Matrix.one_apply, hkl]
    rw [hone]
    exact S.one_mem
  · intro i j hij a
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact S.one_mem
    · exact h i j hij
  · intro A B hA hB
    exact S.mul_mem hA hB

theorem card_SL_four : Nat.card SL(4, ZMod 2) = 20160 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

end Block

section Std

open Matrix
open scoped MatrixGroups

section Dot


theorem commute_tvP_of_dot {k j : Fin 1953} (h1 : tvForm k.val ⬝ᵥ tvVec j.val = 0)
    (h2 : tvForm j.val ⬝ᵥ tvVec k.val = 0) : Commute (tvP k) (tvP j) := by
  have hAB : Commute (vecMulVec (tvVec k.val) (tvForm k.val))
      (vecMulVec (tvVec j.val) (tvForm j.val)) := by
    show _ * _ = _ * _
    rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, h1, h2, zero_smul, zero_smul,
      vecMulVec_zero, vecMulVec_zero]
  have hM : Commute (tvMatrix k.val) (tvMatrix j.val) :=
    (Commute.one_left _).add_left ((Commute.one_right _).add_right hAB)
  have hSL : Commute (tvSL k) (tvSL j) := Subtype.ext hM.eq
  exact hSL.map actPerm

theorem dot_eq_zero_of_commute {k j : Fin 1953} (h : Commute (tvP k) (tvP j)) :
    tvForm k.val ⬝ᵥ tvVec j.val = 0 ∧ tvForm j.val ⬝ᵥ tvVec k.val = 0 := by
  have h1 := tvImg_eq_self_of_commute h
  have h2 := tvVec_tvImg (j := k) (a := j)
  have h3 := tvForm_tvImg (j := k) (a := j)
  rw [h1] at h2 h3
  refine ⟨?_, ?_⟩
  · have h4 : (tvForm k.val ⬝ᵥ tvVec j.val) • tvVec k.val = 0 := by
      have := congrArg (fun w => w - tvVec j.val) h2
      simpa using this.symm
    exact (smul_eq_zero.mp h4).resolve_right (tvVec_ne_zero k.2)
  · have h4 : (tvForm j.val ⬝ᵥ tvVec k.val) • tvForm k.val = 0 := by
      have := congrArg (fun w => w - tvForm j.val) h3
      simpa using this.symm
    exact (smul_eq_zero.mp h4).resolve_right (tvForm_ne_zero k.2)

theorem exists_tv_ext0 {v φ : Fin 4 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hd : φ ⬝ᵥ v = 0) :
    ∃ k : Fin 1953, tvVec k.val = ext0 v ∧ tvForm k.val = ext0 φ := by
  obtain ⟨k, hk⟩ := tvToSet_surjective
    (⟨(ext0 v, ext0 φ), ext0_ne_zero hv, ext0_ne_zero hφ, by rw [dotProduct_ext0]; exact hd⟩ :
      TvSet)
  exact ⟨k, congrArg (fun q => q.1.1) hk, congrArg (fun q => q.1.2) hk⟩

theorem injective_actPerm_embSL : Function.Injective (actPerm.comp embSL) :=
  fun _ _ h => embSL_injective (actPerm_injective h)

end Dot

section StdPair


theorem exists_tv_blk {v φ : Fin 4 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hd : φ ⬝ᵥ v = 0) :
    ∃ k : Fin 1953, tvMatrix k.val = blkMat (1 + vecMulVec v φ) ∧
      Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP 31) := by
  obtain ⟨k, hk1, hk2⟩ := exists_tv_ext0 hv hφ hd
  obtain ⟨h0v, h0f, h31v, h31f⟩ := tv_std_parts
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [blkMat_transvec, tvMatrix, hk1, hk2]
  · refine commute_tvP_of_dot ?_ ?_
    · rw [fin_val_zero, hk2, h0v, dotProduct_single, mul_one]
      exact ext0_inl φ 0
    · rw [fin_val_zero, hk1, h0f, single_dotProduct, one_mul]
      exact ext0_inl v 1
  · refine commute_tvP_of_dot ?_ ?_
    · rw [fin_val_31, hk2, h31v, dotProduct_single, mul_one]
      exact ext0_inl φ 1
    · rw [fin_val_31, hk1, h31f, single_dotProduct, one_mul]
      exact ext0_inl v 0

@[expose] def stdComm : Set (Fin 1953) :=
  {k | Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP 31)}

theorem actPerm_embSL_transvection {i j : Fin 4} (hij : i ≠ j) :
    ∃ k ∈ stdComm, actPerm (embSL (SpecialLinearGroup.transvection hij (1 : ZMod 2))) = tvP k := by
  have hne : ∀ a : Fin 4, (Pi.single a (1 : ZMod 2) : Fin 4 → ZMod 2) ≠ 0 := fun a h => by
    have := congrFun h a
    simp at this
  obtain ⟨k, hkm, hk0, hk31⟩ := exists_tv_blk (hne i) (hne j) (by
    rw [dotProduct_single, mul_one]
    simp [Pi.single_apply, hij])
  refine ⟨k, ⟨hk0, hk31⟩, ?_⟩
  have : embSL (SpecialLinearGroup.transvection hij (1 : ZMod 2)) = tvSL k := by
    apply Subtype.ext
    show blkMat (1 + Matrix.single i j (1 : ZMod 2)) = tvMatrix k.val
    rw [Matrix.single_eq_single_vecMulVec_single, hkm]
  rw [this]
  rfl

theorem actPerm_embSL_mem_closure (A : SL(4, ZMod 2)) :
    actPerm (embSL A) ∈ closure (tvP '' stdComm) := by
  have htop : (closure (tvP '' stdComm)).comap (actPerm.comp embSL) = ⊤ := by
    apply eq_top_of_elementary_gen
    intro i j hij
    obtain ⟨k, hk, hT⟩ := actPerm_embSL_transvection hij
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, hT]
    exact subset_closure ⟨k, hk, rfl⟩
  have : A ∈ (closure (tvP '' stdComm)).comap (actPerm.comp embSL) := htop ▸ mem_top A
  exact this

theorem exists_tv_ext0_of_mem_stdComm {k : Fin 1953} (hk : k ∈ stdComm) :
    ∃ v φ : Fin 4 → ZMod 2, tvVec k.val = ext0 v ∧ tvForm k.val = ext0 φ := by
  obtain ⟨hk0, hk31⟩ := hk
  obtain ⟨h0v, h0f, h31v, h31f⟩ := tv_std_parts
  obtain ⟨a1, a2⟩ := dot_eq_zero_of_commute hk0
  obtain ⟨b1, b2⟩ := dot_eq_zero_of_commute hk31
  rw [fin_val_zero, h0v, dotProduct_single, mul_one] at a1
  rw [fin_val_zero, h0f, single_dotProduct, one_mul] at a2
  rw [fin_val_31, h31v, dotProduct_single, mul_one] at b1
  rw [fin_val_31, h31f, single_dotProduct, one_mul] at b2
  refine ⟨fun x => tvVec k.val (e24 (Sum.inr x)), fun x => tvForm k.val (e24 (Sum.inr x)), ?_, ?_⟩
  · funext a
    obtain ⟨x, rfl⟩ := e24.surjective a
    rcases x with x | x
    · rw [ext0_inl]
      fin_cases x
      · exact b2
      · exact a2
    · rw [ext0_inr]
  · funext a
    obtain ⟨x, rfl⟩ := e24.surjective a
    rcases x with x | x
    · rw [ext0_inl]
      fin_cases x
      · exact a1
      · exact b1
    · rw [ext0_inr]

theorem actPerm_embSL_surj_of_mem_stdComm {k : Fin 1953} (hk : k ∈ stdComm) :
    ∃ A : SL(4, ZMod 2), actPerm (embSL A) = tvP k := by
  obtain ⟨v, φ, hv, hφ⟩ := exists_tv_ext0_of_mem_stdComm hk
  have hblk : tvMatrix k.val = blkMat (1 + vecMulVec v φ) := by
    rw [blkMat_transvec, tvMatrix, hv, hφ]
  have hdet : (1 + vecMulVec v φ).det = 1 := by
    rw [← det_blkMat, ← hblk]
    exact det_tvMatrix k.2
  refine ⟨⟨1 + vecMulVec v φ, hdet⟩, ?_⟩
  have : embSL ⟨1 + vecMulVec v φ, hdet⟩ = tvSL k := Subtype.ext hblk.symm
  rw [this]
  rfl

theorem closure_stdComm_eq_range :
    closure (tvP '' stdComm) = (actPerm.comp embSL).range := by
  refine le_antisymm ((closure_le _).mpr ?_) ?_
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨A, hA⟩ := actPerm_embSL_surj_of_mem_stdComm hk
    exact ⟨A, hA⟩
  · rintro _ ⟨A, rfl⟩
    exact actPerm_embSL_mem_closure A

theorem card_closure_stdComm : Nat.card (closure (tvP '' stdComm)) = 20160 := by
  rw [closure_stdComm_eq_range,
    Nat.card_congr (MonoidHom.ofInjective injective_actPerm_embSL).toEquiv.symm, card_SL_four]

theorem card_closure_std : Nat.card (closure (tvP '' {k : Fin 1953 |
    Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP 31)})) = 20160 :=
  card_closure_stdComm

theorem isSimpleGroup_closure_stdComm : IsSimpleGroup (closure (tvP '' stdComm)) := by
  haveI : IsSimpleGroup PSL(4, ZMod 2) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 4 (by norm_num) (.inl (by norm_num))
      (.inl (by norm_num))
  haveI : IsSimpleGroup SL(4, ZMod 2) := (CFSG.LargeExtraspecial.DW.slEquivPSL 4).isSimpleGroup
  haveI : IsSimpleGroup (actPerm.comp embSL).range :=
    (MonoidHom.ofInjective injective_actPerm_embSL).symm.isSimpleGroup
  have h : closure (tvP '' stdComm) = (actPerm.comp embSL).range := closure_stdComm_eq_range
  exact (MulEquiv.subgroupCongr h).isSimpleGroup

theorem isSimpleGroup_closure_std : IsSimpleGroup (closure (tvP '' {k : Fin 1953 |
    Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP 31)})) :=
  isSimpleGroup_closure_stdComm

end StdPair

section Gen


theorem exists_map_closure_stdComm {kt ku : Fin 1953} (hord : orderOf (tvP kt * tvP ku) = 3) :
    ∃ g : Equiv.Perm (Fin 1953), (closure (tvP '' stdComm)).map (MulAut.conj g).toMonoidHom =
      closure (tvP '' {k : Fin 1953 | Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)}) := by
  obtain ⟨g, hg, hg0, hg31⟩ := exists_mem_T6_pair hord
  refine ⟨g, ?_⟩
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨k', hk', rfl⟩, rfl⟩
    refine ⟨g k', ⟨?_, ?_⟩, ?_⟩
    · rw [← hg0]
      exact commute_tvP_conj hg hk'.1
    · rw [← hg31]
      exact commute_tvP_conj hg hk'.2
    · exact (mul_tvP_mul_inv hg k').symm
  · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
    have hkk : g (g⁻¹ k) = k := by simp
    refine ⟨tvP (g⁻¹ k), ⟨g⁻¹ k, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · exact commute_tvP_of_conj hg (by rw [hkk, hg0]; exact hk1)
    · exact commute_tvP_of_conj hg (by rw [hkk, hg31]; exact hk2)
    · show g * tvP (g⁻¹ k) * g⁻¹ = tvP k
      rw [mul_tvP_mul_inv hg, hkk]

theorem nonempty_mulEquiv_closure_pair {kt ku : Fin 1953}
    (hord : orderOf (tvP kt * tvP ku) = 3) :
    Nonempty (closure (tvP '' stdComm) ≃* closure (tvP '' {k : Fin 1953 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) := by
  obtain ⟨g, hmap⟩ := exists_map_closure_stdComm hord
  exact ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hmap)⟩

theorem isSimpleGroup_closure_pair {kt ku : Fin 1953} (hord : orderOf (tvP kt * tvP ku) = 3) :
    IsSimpleGroup (closure (tvP '' {k : Fin 1953 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_closure_pair hord
  haveI := isSimpleGroup_closure_stdComm
  exact e.symm.isSimpleGroup

end Gen

end Std

end CFSG.GF2Type.SmithTypeE.L6Ident
