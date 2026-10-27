module

public import CFSG.LocalAnalysis.RankThreeUC.GL33.CodeSound
public import Certificates.Data.GL33.Check
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GL33

open CFSG.GL33.Native

abbrev G := GL (Fin 3) (ZMod 3)

@[expose] def Good (c : ℕ) : Prop := (toM c).det ≠ 0

noncomputable def ofCode (c : ℕ) : G := by
  classical exact if h : Good c then Matrix.GeneralLinearGroup.mkOfDetNeZero (toM c) h else 1

private theorem digs_getElem (a : ℕ) {n : ℕ} (hn : n < 9) : (digs a)[n]! = dig a n := by
  simp [digs, dig, hn]

private theorem digs_ent (a : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    (digs a)[3 * i + j]! = ent a i j := digs_getElem a (by omega)

theorem mulF_eq_mulC (a b : ℕ) : mulF a b = mulC a b := by
  dsimp only [mulF, mulC]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk9 : k < 9 := List.mem_range.1 hk
  have hi : k / 3 < 3 := by omega
  have hj : k % 3 < 3 := by omega
  have x0 : (digs a)[3 * (k / 3)]! = ent a (k / 3) 0 :=
    digs_ent a (i := k / 3) (j := 0) hi (by omega)
  have x1 : (digs a)[3 * (k / 3) + 1]! = ent a (k / 3) 1 :=
    digs_ent a (i := k / 3) (j := 1) hi (by omega)
  have x2 : (digs a)[3 * (k / 3) + 2]! = ent a (k / 3) 2 :=
    digs_ent a (i := k / 3) (j := 2) hi (by omega)
  have y0 : (digs b)[k % 3]! = ent b 0 (k % 3) := by
    simpa using digs_ent b (i := 0) (j := k % 3) (by omega) hj
  have y1 : (digs b)[3 + k % 3]! = ent b 1 (k % 3) := by
    simpa using digs_ent b (i := 1) (j := k % 3) (by omega) hj
  have y2 : (digs b)[6 + k % 3]! = ent b 2 (k % 3) := by
    simpa using digs_ent b (i := 2) (j := k % 3) (by omega) hj
  rw [x0, x1, x2, y0, y1, y2]

theorem good_oneC : Good oneC := by
  unfold Good
  rw [toM_oneC, Matrix.det_one]
  exact one_ne_zero

theorem good_mulF {a b : ℕ} (ha : Good a) (hb : Good b) : Good (mulF a b) := by
  unfold Good at *
  rw [mulF_eq_mulC, toM_mulC, Matrix.det_mul]
  exact mul_ne_zero ha hb

theorem coe_ofCode {c : ℕ} (hc : Good c) :
    ((ofCode c : G) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = toM c := by
  unfold ofCode
  rw [dif_pos hc]
  rfl

theorem ofCode_oneC : ofCode oneC = 1 := by
  apply Units.ext
  rw [coe_ofCode good_oneC, toM_oneC]
  rfl

theorem ofCode_mulF {a b : ℕ} (ha : Good a) (hb : Good b) :
    ofCode (mulF a b) = ofCode a * ofCode b := by
  apply Units.ext
  rw [coe_ofCode (good_mulF ha hb), mulF_eq_mulC, toM_mulC]
  rw [Units.val_mul, coe_ofCode ha, coe_ofCode hb]

theorem good_powC {a : ℕ} (ha : Good a) (e : ℕ) : Good (powC a e) := by
  induction e with
  | zero => exact good_oneC
  | succ e ih =>
    rw [powC, ← mulF_eq_mulC]
    exact good_mulF ih ha

theorem ofCode_powC {a : ℕ} (ha : Good a) (e : ℕ) : ofCode (powC a e) = ofCode a ^ e := by
  induction e with
  | zero => rw [powC, ofCode_oneC, pow_zero]
  | succ e ih => rw [powC, ← mulF_eq_mulC, ofCode_mulF (good_powC ha e) ha, ih, pow_succ]

theorem good_of_mem_glCodes {c : ℕ} (h : c ∈ glCodes ()) : Good c :=
  ((mem_glCodes_iff c).1 h).2

theorem encode_mem_glCodes (g : G) :
    encode (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) ∈ glCodes () :=
  (mem_glCodes_iff _).2 ⟨encode_lt _, by
    rw [toM_encode]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero⟩

theorem ofCode_encode (g : G) :
    ofCode (encode (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) = g := by
  apply Units.ext
  rw [coe_ofCode (good_of_mem_glCodes (encode_mem_glCodes g)), toM_encode]

theorem ofCode_injOn {a b : ℕ} (ha : a ∈ glCodes ()) (hb : b ∈ glCodes ())
    (h : ofCode a = ofCode b) : a = b := by
  have ha' := (mem_glCodes_iff a).1 ha
  have hb' := (mem_glCodes_iff b).1 hb
  refine eq_of_toM_eq ha'.1 hb'.1 ?_
  rw [← coe_ofCode ha'.2, ← coe_ofCode hb'.2, h]

private theorem memS_go_spec (L : Array ℕ) (c : ℕ) :
    ∀ f lo hi : ℕ, hi ≤ L.size → memS.go L c lo hi f = true → ∃ i < L.size, L[i]! = c := by
  intro f
  induction f with
  | zero => intro lo hi _ h; simp [memS.go] at h
  | succ f ih =>
    intro lo hi hhi h
    simp only [memS.go] at h
    split_ifs at h with h1 h2 h3
    · exact ⟨(lo + hi) / 2, by omega, by simpa using h2⟩
    · exact ih _ _ hhi h
    · exact ih _ _ (by omega) h

theorem memS_spec {L : Array ℕ} {c : ℕ} (h : memS L c = true) : ∃ i < L.size, L[i]! = c :=
  memS_go_spec L c _ 0 L.size le_rfl h

theorem incOK_inj {L : Array ℕ} (h : incOK L = true) {i j : ℕ} (hi : i < L.size)
    (hj : j < L.size) (hij : L[i]! = L[j]!) : i = j := by
  have hstep : ∀ k, k + 1 < L.size → L[k]! < L[k + 1]! := by
    intro k hk
    simp only [incOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h k (by omega)
  have hlt : ∀ j, ∀ i, i < j → j < L.size → L[i]! < L[j]! := by
    intro j
    induction j with
    | zero => intro i hij; omega
    | succ j ih =>
      intro i hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
      · exact (ih i hlt (by omega)).trans (hstep j hj)
      · exact hstep i hj
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd hij (hlt j i h1 hj).ne
  · exact h1
  · exact absurd hij.symm (hlt i j h1 hi).ne

private theorem size_glArr : (glArr ()).size = (glCodes ()).length := by
  simp [glArr]

private theorem toArray_getElem! {l : List ℕ} {i : ℕ} (hi : i < l.length) :
    l.toArray[i]! = l[i] := by
  simp [hi]

private theorem glArr_getElem {i : ℕ} (hi : i < (glCodes ()).length) :
    (glArr ())[i]! = (glCodes ())[i] := by
  unfold glArr
  exact toArray_getElem! hi

theorem glArr_getElem_mem {i : ℕ} (hi : i < (glArr ()).size) :
    (glArr ())[i]! ∈ glCodes () := by
  rw [size_glArr] at hi
  rw [glArr_getElem hi]
  exact List.getElem_mem hi

theorem exists_glArr (g : G) : ∃ i < (glArr ()).size, ofCode (glArr ())[i]! = g := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 (encode_mem_glCodes g)
  refine ⟨i, by rw [size_glArr]; exact hi, ?_⟩
  rw [glArr_getElem hi, hix, ofCode_encode]

theorem good_glArr {i : ℕ} (hi : i < (glArr ()).size) : Good (glArr ())[i]! :=
  good_of_mem_glCodes (glArr_getElem_mem hi)

theorem card_G : Nat.card G = 11232 := by
  rw [Matrix.card_GL_field 3, ZMod.card, Fin.prod_univ_three]
  norm_num

@[expose] noncomputable def sub2 (a b : ℕ) : Subgroup G := Subgroup.closure {ofCode a, ofCode b}

private theorem gen_spec {a b : ℕ} (ha : Good a) (hb : Good b) {k : ℕ} (hk : k < 2) :
    Good #[a, b][k]! ∧ ofCode #[a, b][k]! ∈ sub2 a b := by
  interval_cases k
  · exact ⟨ha, Subgroup.subset_closure (by simp)⟩
  · exact ⟨hb, Subgroup.subset_closure (by simp)⟩

theorem treeOK_spec {L par lab dep : Array ℕ} {a b : ℕ} (ha : Good a) (hb : Good b)
    (h : treeOK L #[a, b] par lab dep = true) :
    ∀ i < L.size, Good L[i]! ∧ ofCode L[i]! ∈ sub2 a b := by
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, hall⟩ := h
  suffices H : ∀ n i, i < L.size → dep[i]! = n → Good L[i]! ∧ ofCode L[i]! ∈ sub2 a b from
    fun i hi => H _ i hi rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hdep
    rcases hall i hi with ⟨_, h1⟩ | ⟨⟨⟨hpar, hlab⟩, hlt⟩, heq⟩
    · rw [h1]
      exact ⟨good_oneC, by rw [ofCode_oneC]; exact Subgroup.one_mem _⟩
    · obtain ⟨hs, hm⟩ := ih _ (by omega) par[i]! hpar rfl
      obtain ⟨hgs, hgm⟩ := gen_spec ha hb (by simpa using hlab)
      rw [heq]
      exact ⟨good_mulF hs hgs, by rw [ofCode_mulF hs hgs]; exact Subgroup.mul_mem _ hm hgm⟩

private theorem pow_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) (k : ℕ) :
    ∀ y ∈ S, y * x ^ k ∈ S := by
  induction k with
  | zero => intro y hy; simpa using hy
  | succ k ih => intro y hy; rw [pow_succ, ← mul_assoc]; exact hx _ (ih y hy)

private theorem inv_mem_of_mul_mem (S : Set G) (x : G) (hx : ∀ y ∈ S, y * x ∈ S) :
    ∀ y ∈ S, y * x⁻¹ ∈ S := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have h1 : x * x ^ (Nat.card G - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_card_eq_one']
  rw [inv_eq_of_mul_eq_one_right h1]
  exact pow_mem_of_mul_mem S x hx _

theorem closedOK_spec {L : Array ℕ} {a b : ℕ} (ha : Good a) (hb : Good b)
    (hL : ∀ i < L.size, Good L[i]!) (h : closedOK L #[a, b] = true) :
    ∀ x ∈ sub2 a b, ∃ i < L.size, ofCode L[i]! = x := by
  simp only [closedOK, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  set S : Set G := {x | ∃ i < L.size, ofCode L[i]! = x}
  have hone : (1 : G) ∈ S := by
    obtain ⟨i, hi, hic⟩ := memS_spec h1
    exact ⟨i, hi, by rw [hic, ofCode_oneC]⟩
  have hgen : ∀ k < 2, ∀ y ∈ S, y * ofCode #[a, b][k]! ∈ S := by
    rintro k hk _ ⟨i, hi, rfl⟩
    have hk' : k < #[a, b].size := by simpa using hk
    have h3 := h2 i hi k hk'
    rw [← getElem!_pos L i hi, ← getElem!_pos #[a, b] k hk'] at h3
    obtain ⟨j, hj, hjc⟩ := memS_spec h3
    exact ⟨j, hj, by rw [hjc, ofCode_mulF (hL i hi) (gen_spec ha hb hk).1]⟩
  have key : ∀ x ∈ sub2 a b, ∀ y ∈ S, y * x ∈ S := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {ofCode a, ofCode b} := hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hgen 0 (by norm_num)
      · exact hgen 1 (by norm_num)
    | one => intro y hy; simpa using hy
    | mul x y _ _ hx hy => intro z hz; rw [← mul_assoc]; exact hy _ (hx z hz)
    | inv x _ hx => exact inv_mem_of_mul_mem S x hx
  intro x hx
  obtain ⟨i, hi, hix⟩ := key x hx 1 hone
  exact ⟨i, hi, by rw [hix, one_mul]⟩

private theorem treeOK_lt {L gens par lab dep : Array ℕ}
    (h : treeOK L gens par lab dep = true) : ∀ i < L.size, L[i]! < 3 ^ 9 := by
  simp only [treeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  intro i hi
  rcases h.2 i hi with ⟨_, h1⟩ | ⟨_, heq⟩
  · rw [h1]
    decide
  · rw [heq, mulF_eq_mulC]
    exact mulC_lt _ _

theorem subOK_spec {a b n : ℕ} {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (ha : Good a)
    (hb : Good b) (h : subOK #[a, b] n r = true) :
    r.1.size = n ∧ (∀ i < n, Good r.1[i]!) ∧ (∀ x, x ∈ sub2 a b ↔ ∃ i < n, ofCode r.1[i]! = x) ∧
      Nat.card (sub2 a b) = n := by
  simp only [subOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hsize, hinc⟩, htree⟩, hclosed⟩ := h
  have hsym := treeOK_spec ha hb htree
  have hlt := treeOK_lt htree
  have hmem := closedOK_spec ha hb (fun i hi => (hsym i hi).1) hclosed
  have hiff : ∀ x, x ∈ sub2 a b ↔ ∃ i < n, ofCode r.1[i]! = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := hmem x hx
      exact ⟨i, by omega, hix⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hsym i (by omega)).2
  have hglc : ∀ i < n, r.1[i]! ∈ glCodes () := fun i hi =>
    (mem_glCodes_iff _).2 ⟨hlt i (by omega), (hsym i (by omega)).1⟩
  refine ⟨hsize, fun i hi => (hsym i (by omega)).1, hiff, ?_⟩
  have hbij : Function.Bijective (fun i : Fin n =>
      (⟨ofCode r.1[(i : ℕ)]!, (hsym i (by omega)).2⟩ : sub2 a b)) := by
    constructor
    · intro i j hij
      exact Fin.ext (incOK_inj hinc (by omega) (by omega)
        (ofCode_injOn (hglc i i.2) (hglc j j.2) (congrArg Subtype.val hij)))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, hix⟩ := (hiff x).1 hx
      exact ⟨⟨i, hi⟩, Subtype.ext hix⟩
  exact (Nat.card_eq_of_bijective _ hbij).symm.trans (Nat.card_fin n)

theorem subOK_mem_glCodes {a b n : ℕ} {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (ha : Good a)
    (hb : Good b) (h : subOK #[a, b] n r = true) {i : ℕ} (hi : i < n) : r.1[i]! ∈ glCodes () := by
  have h' := h
  simp only [subOK, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨hsize, -⟩, htree⟩, -⟩ := h'
  exact (mem_glCodes_iff _).2 ⟨treeOK_lt htree i (by omega),
    (subOK_spec ha hb h).2.1 i hi⟩

theorem mem_sub2_of_memS {a b n : ℕ} {r : Array ℕ × Array ℕ × Array ℕ × Array ℕ} (ha : Good a)
    (hb : Good b) (hr : subOK #[a, b] n r = true) {c : ℕ} (h : memS r.1 c = true) :
    Good c ∧ ofCode c ∈ sub2 a b := by
  obtain ⟨i, hi, hic⟩ := memS_spec h
  obtain ⟨hsize, hsym, hiff, -⟩ := subOK_spec ha hb hr
  subst hic
  exact ⟨hsym i (by omega), (hiff _).2 ⟨i, by omega, rfl⟩⟩

theorem toM_minusOneC : toM minusOneC = -1 := by
  ext x y
  fin_cases x <;> fin_cases y <;> decide

theorem good_minusOneC : Good minusOneC := by
  unfold Good
  rw [toM_minusOneC, Matrix.det_neg, Matrix.det_one]
  decide

end CFSG.GL33

end
