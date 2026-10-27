module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatJ3E9
public import CFSG.Quasithin.Background.E2TwoProofSporGen
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.J3K

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.Schreier
open CFSG.KC.SLDc CFSG.KC.E64F
open CFSG.KD.J3Dc (Lm)

@[expose] def n3w : List ℕ := [3, 2, 0, 3, 0, 1, 3]

@[expose] def n3iw : List ℕ := [2, 3, 3, 0, 1]

@[expose] noncomputable def n3 : ↥j3P := evalElt (gensY 4).toArray n3w

@[expose] noncomputable def n3inv : ↥j3P := evalElt (gensY 4).toArray n3iw

@[expose] noncomputable def n3F (w : List ℕ) : ℕ → ℕ := wordF (Lm 4) w

@[expose] noncomputable def n3aF : ℕ → ℕ := n3F n3w

@[expose] noncomputable def n3gF : ℕ → ℕ := n3F n3iw

@[expose] noncomputable def n3mJ (j : ℕ) : ↥j3P := evalElt (gensY j).toArray [3]

@[expose] noncomputable def n3OK : Bool :=
  e9B.all (fun p => n3aF (n3aF (n3aF p)) == p) &&
  e9B.any (fun p => n3aF p != p) &&
  e9B.all (fun p => n3gF (n3aF p) == n3aF (n3aF (n3gF p))) &&
  (List.range 3).all (fun i =>
    labF (wordF (Lm 4) (n3w ++ [i] ++ n3w ++ n3w)) CFSG.KD.J3Dc.C.Δ == CFSG.KD.J3Dc.C.Δ) &&
  (labF (wordF (Lm 2) [0, 3]) CFSG.KD.J3Dc.C.Δ != labF (wordF (Lm 2) [3]) CFSG.KD.J3Dc.C.Δ) &&
  (labF (wordF (Lm 3) [0, 3]) CFSG.KD.J3Dc.C.Δ != labF (wordF (Lm 3) [3]) CFSG.KD.J3Dc.C.Δ) &&
  (labF (wordF (Lm 4) [1, 3]) CFSG.KD.J3Dc.C.Δ != labF (wordF (Lm 4) [3]) CFSG.KD.J3Dc.C.Δ)

private theorem n3OK_eq : n3OK = true := by quickRfl

private theorem n3_parts :
    (∀ p ∈ e9B, n3aF (n3aF (n3aF p)) = p) ∧
    (∃ p ∈ e9B, n3aF p ≠ p) ∧
    (∀ p ∈ e9B, n3gF (n3aF p) = n3aF (n3aF (n3gF p))) ∧
    (∀ i ∈ List.range 3,
      labF (wordF (Lm 4) (n3w ++ [i] ++ n3w ++ n3w)) CFSG.KD.J3Dc.C.Δ = CFSG.KD.J3Dc.C.Δ) ∧
    (labF (wordF (Lm 2) [0, 3]) CFSG.KD.J3Dc.C.Δ ≠ labF (wordF (Lm 2) [3]) CFSG.KD.J3Dc.C.Δ) ∧
    (labF (wordF (Lm 3) [0, 3]) CFSG.KD.J3Dc.C.Δ ≠ labF (wordF (Lm 3) [3]) CFSG.KD.J3Dc.C.Δ) ∧
    (labF (wordF (Lm 4) [1, 3]) CFSG.KD.J3Dc.C.Δ ≠ labF (wordF (Lm 4) [3]) CFSG.KD.J3Dc.C.Δ) := by
  have h := n3OK_eq
  unfold n3OK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

private theorem gensY4_size : (gensY 4).toArray.size = 4 := by
  simp only [List.size_toArray, gensY, List.length_append, List.length_cons, List.length_nil,
    List.length_map]
  decide

private theorem gensY_size (j : ℕ) :
    (gensY j).toArray.size = 3 + (CFSG.KD.J3Dc.J.mw.getD j []).length := by
  simp [gensY]
  omega

private theorem mw_getD_length {j : ℕ} (hj : j = 2 ∨ j = 3 ∨ j = 4) :
    (CFSG.KD.J3Dc.J.mw.getD j []).length = 1 := by
  rcases hj with rfl | rfl | rfl <;> decide

private theorem gensY_getD_of_lt {j i : ℕ} (hi : i < 3) :
    (gensY j).toArray.getD i 1 = sg i := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD]
  unfold gensY
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  interval_cases i <;> rfl

private theorem n3w_lt : ∀ l ∈ n3w, l < (gensY 4).toArray.size := by
  rw [gensY4_size]
  intro l hl
  simp only [n3w, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private theorem n3iw_lt : ∀ l ∈ n3iw, l < (gensY 4).toArray.size := by
  rw [gensY4_size]
  intro l hl
  simp only [n3iw, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl <;> norm_num

section Checks


private theorem n3_act {w : List ℕ} (hw : ∀ l ∈ w, l < (gensY 4).toArray.size) {p : ℕ}
    (hp : p < 6156) : act 6156 (evalElt (gensY 4).toArray w) p = wordF (Lm 4) w p := by
  rw [act_evalElt (gensY 4).toArray (tabs (gensY 4).toArray)
    (fun l hl => tabs_getD _ (by rw [tabs_size]; exact hl)) _ hw p hp]
  exact (wordImg_eq (good_Y 4) w (by rw [tabs_size]; exact hw) p hp).1

private theorem insN_map_insN (f : ℕ → ℕ) (l : List ℕ) :
    insN ((insN l).map f) = insN (l.map f) := by
  rw [insN_eq, insN_eq, insN_eq]
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ ?_ ?_
  · exact List.pairwise_insertionSort (· ≤ ·) ((l.insertionSort (· ≤ ·)).map f)
  · exact List.pairwise_insertionSort (· ≤ ·) (l.map f)
  · have h0 : (((l.insertionSort (· ≤ ·)).map f).insertionSort (· ≤ ·)).Perm
        ((l.insertionSort (· ≤ ·)).map f) :=
      List.perm_insertionSort (· ≤ ·) ((l.insertionSort (· ≤ ·)).map f)
    have h1 : ((l.insertionSort (· ≤ ·)).map f).Perm (l.map f) :=
      (List.perm_insertionSort (· ≤ ·) l).map f
    have h2 : (l.map f).Perm ((l.map f).insertionSort (· ≤ ·)) :=
      (List.perm_insertionSort (· ≤ ·) (l.map f)).symm
    exact h0.trans (h1.trans h2)

private theorem ptAct_eq_labF (t : Array ℕ) (x : List ℕ) :
    ptAct t x = labF (fun p => t.getD p 0) x := by
  unfold ptAct labF
  rw [sortN_eq]

private theorem labWord_eq_labF (letters : Array (Array ℕ)) (w : List ℕ) :
    labWord ptAct letters CFSG.KD.J3Dc.C.Δ w =
      labF (wordImg letters w) CFSG.KD.J3Dc.C.Δ := by
  induction w with
  | nil =>
      change CFSG.KD.J3Dc.C.Δ = labF id CFSG.KD.J3Dc.C.Δ
      rw [labF, List.map_id, ← sortN_eq, sortN_of_pairwise delta_valid.1]
  | cons l w ih =>
      change ptAct (letters.getD l #[]) (labWord ptAct letters CFSG.KD.J3Dc.C.Δ w) =
        labF (wordImg letters (l :: w)) CFSG.KD.J3Dc.C.Δ
      rw [ih, ptAct_eq_labF]
      unfold labF wordImg
      rw [insN_map_insN, List.map_map]
      rfl

private theorem lab_evalElt_labF {j : ℕ} (w : List ℕ)
    (hw : ∀ l ∈ w, l < (gensY j).toArray.size) :
    lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (evalElt (gensY j).toArray w) =
      labF (wordF (Lm j) w) CFSG.KD.J3Dc.C.Δ := by
  rw [lab_evalElt (ptLab_lawful (Γ := ↥j3P) (n := 6156)) delta_valid
    (gensY j).toArray (tabs (gensY j).toArray)
    (fun l hl => tabs_getD _ (by rw [tabs_size]; exact hl)) w hw]
  change labWord ptAct (tabs (gensY j).toArray) CFSG.KD.J3Dc.C.Δ w = _
  rw [labWord_eq_labF]
  unfold labF
  congr 1
  refine List.map_congr_left fun p hp => ?_
  exact (wordImg_eq (good_Y j) w (by rw [tabs_size]; exact hw) p (delta_valid.2 p hp)).1

private theorem n3sg_mem_S {i : ℕ} (hi : i < 3) : sg i ∈ S := by
  show sg i ∈ Subgroup.closure {x | x ∈ [sg 0, sg 1, sg 2]}
  apply Subgroup.subset_closure
  interval_cases i <;> simp

private theorem n3mJ_mem_Y {j : ℕ} (hj : j = 2 ∨ j = 3 ∨ j = 4) : n3mJ j ∈ Y j := by
  have hlt : 3 < (gensY j).toArray.size := by
    rw [gensY_size, mw_getD_length hj]
    norm_num
  have hmem : evalElt (gensY j).toArray [3] ∈ Y j := by
    refine evalElt_mem _ (fun l hl => ?_) [3] (fun l hl => ?_)
    · have h := evalElt_getD_mem_closure (gensY j).toArray hl
      rwa [List.toList_toArray] at h
    · simp only [List.mem_singleton] at hl
      rwa [hl]
  simpa [n3mJ] using hmem

private theorem n3stab_eq_S :
    stab (ptLab_lawful (Γ := ↥j3P) (n := 6156)) delta_valid = S := by
  ext g
  exact dc_facts.1 g

private theorem n3a_act {p : ℕ} (hp : p < 6156) : act 6156 n3 p = n3aF p := by
  rw [n3, n3aF, n3F]
  exact n3_act n3w_lt hp

private theorem n3g_act {p : ℕ} (hp : p < 6156) : act 6156 n3inv p = n3gF p := by
  rw [n3inv, n3gF, n3F]
  exact n3_act n3iw_lt hp

private theorem n3aF_lt {p : ℕ} (hp : p < 6156) : n3aF p < 6156 := by
  rw [← n3a_act hp]
  exact act_lt _ hp

private theorem n3gF_lt {p : ℕ} (hp : p < 6156) : n3gF p < 6156 := by
  rw [← n3g_act hp]
  exact act_lt _ hp

theorem n3_pow_three : n3 ^ 3 = 1 := by
  refine eq_of_e9B fun p hp => ?_
  have hp' := e9B_lt p hp
  rw [act_one hp', j3P_act_pow_three _ hp', n3a_act hp', n3a_act (n3aF_lt hp'),
    n3a_act (n3aF_lt (n3aF_lt hp'))]
  exact n3_parts.1 p hp

theorem n3_ne_one : n3 ≠ 1 := by
  intro h
  obtain ⟨p, hp, hne⟩ := n3_parts.2.1
  have hp' := e9B_lt p hp
  rw [← n3a_act hp', h, act_one hp'] at hne
  exact hne rfl

private theorem n3_mul_self_eq_inv : n3 * n3 = n3⁻¹ := by
  have h3 : (n3 * n3) * n3 = 1 := by
    rw [mul_assoc, ← pow_three]
    exact n3_pow_three
  have h4 : (n3 * n3) * n3 = n3⁻¹ * n3 := by
    rw [h3, inv_mul_cancel]
  exact mul_right_cancel h4

theorem n3inv_conj : n3inv * n3 * n3inv⁻¹ = n3⁻¹ := by
  have hga : n3inv * n3 = n3 * n3 * n3inv := by
    refine eq_of_e9B fun p hp => ?_
    have hp' := e9B_lt p hp
    calc
      act 6156 (n3inv * n3) p = act 6156 n3inv (act 6156 n3 p) := act_mul _ _ hp'
      _ = act 6156 n3inv (n3aF p) := by rw [n3a_act hp']
      _ = n3gF (n3aF p) := n3g_act (n3aF_lt hp')
      _ = act 6156 (n3 * n3 * n3inv) p := by
        rw [act_mul _ _ hp', act_mul _ _ (act_lt n3inv hp'), n3g_act hp',
          n3a_act (n3gF_lt hp'), n3a_act (n3aF_lt (n3gF_lt hp'))]
        exact n3_parts.2.2.1 p hp
  calc
    n3inv * n3 * n3inv⁻¹ = n3 * n3 * n3inv * n3inv⁻¹ := by rw [hga]
    _ = n3 * n3 := by group
    _ = n3⁻¹ := n3_mul_self_eq_inv

private theorem n3_not_mem_S : n3 ∉ S := by
  intro hmem
  have hord : orderOf n3 ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hmem
  rw [card_S] at hord
  have ho : orderOf n3 = 3 := orderOf_eq_prime n3_pow_three n3_ne_one
  rw [ho] at hord
  norm_num at hord

theorem n3_mem_normalizer : n3 ∈ Subgroup.normalizer (S : Set ↥j3P) := by
  have hgen : ∀ i < 3, n3 * sg i * n3 * n3 ∈ S := by
    intro i hi
    refine (dc_facts.1 _).mp ?_
    have hw4 : ∀ l ∈ n3w, l < 4 := by
      intro l hl
      have h := n3w_lt l hl
      rwa [gensY4_size] at h
    have hw : ∀ l ∈ (n3w ++ [i] ++ n3w ++ n3w), l < (gensY 4).toArray.size := by
      intro l hl
      rw [gensY4_size]
      rcases List.mem_append.mp hl with hl | hl
      · rcases List.mem_append.mp hl with hl | hl
        · rcases List.mem_append.mp hl with hl | hl
          · exact hw4 l hl
          · rw [List.mem_singleton] at hl; omega
        · exact hw4 l hl
      · exact hw4 l hl
    have e : evalElt (gensY 4).toArray (n3w ++ [i] ++ n3w ++ n3w) =
        n3 * sg i * n3 * n3 := by
      simp only [evalElt, List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one, n3, gensY_getD_of_lt (j := 4) hi]
    rw [← e, lab_evalElt_labF (j := 4) (n3w ++ [i] ++ n3w ++ n3w) hw]
    exact n3_parts.2.2.2.1 i (List.mem_range.mpr hi)
  have hconj : ∀ s ∈ S, n3 * s * n3⁻¹ ∈ S := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · have h := hgen 0 (by norm_num)
          have e : n3 * sg 0 * n3 * n3 = n3 * sg 0 * n3⁻¹ := by
            rw [← n3_mul_self_eq_inv]
            group
          rwa [e] at h
        · have h := hgen 1 (by norm_num)
          have e : n3 * sg 1 * n3 * n3 = n3 * sg 1 * n3⁻¹ := by
            rw [← n3_mul_self_eq_inv]
            group
          rwa [e] at h
        · have h := hgen 2 (by norm_num)
          have e : n3 * sg 2 * n3 * n3 = n3 * sg 2 * n3⁻¹ := by
            rw [← n3_mul_self_eq_inv]
            group
          rwa [e] at h
    | one =>
        have e : n3 * (1 : ↥j3P) * n3⁻¹ = 1 := by group
        rw [e]
        exact S.one_mem
    | mul x y hx hy ihx ihy =>
        have e : n3 * (x * y) * n3⁻¹ = (n3 * x * n3⁻¹) * (n3 * y * n3⁻¹) := by group
        rw [e]
        exact S.mul_mem ihx ihy
    | inv x hx ih =>
        have e : n3 * x⁻¹ * n3⁻¹ = (n3 * x * n3⁻¹)⁻¹ := by group
        rw [e]
        exact S.inv_mem ih
  have hmap_le : S.map (MulAut.conj n3).toMonoidHom ≤ S := by
    rintro _ ⟨s, hs, rfl⟩
    change (MulAut.conj n3) s ∈ S
    rw [MulAut.conj_apply]
    exact hconj s hs
  have hmap : S.map (MulAut.conj n3).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq (Subgroup.card_map_of_injective
      (K := S) (f := (MulAut.conj n3).toMonoidHom) (MulAut.conj n3).injective).symm)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

private theorem n3mJ_label_ne {j i : ℕ} (hi : i < 3) (hj : j = 2 ∨ j = 3 ∨ j = 4)
    (h : labF (wordF (Lm j) [i, 3]) CFSG.KD.J3Dc.C.Δ ≠ labF (wordF (Lm j) [3]) CFSG.KD.J3Dc.C.Δ) :
    lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (sg i * n3mJ j) ≠ lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (n3mJ j) := by
  intro heq
  apply h
  have h1 : lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (sg i * n3mJ j) =
      labF (wordF (Lm j) [i, 3]) CFSG.KD.J3Dc.C.Δ := by
    have e : evalElt (gensY j).toArray [i, 3] = sg i * n3mJ j := by
      rw [evalElt_cons, evalElt_cons, evalElt_nil]
      simp only [mul_one]
      rw [gensY_getD_of_lt (j := j) hi]
      simp [n3mJ, evalElt]
    rw [← e]
    refine lab_evalElt_labF [i, 3] ?_
    intro l hl
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [gensY_size, mw_getD_length hj]; omega
    · rw [gensY_size, mw_getD_length hj]; omega
  have h2 : lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (n3mJ j) =
      labF (wordF (Lm j) [3]) CFSG.KD.J3Dc.C.Δ := by
    rw [n3mJ]
    refine lab_evalElt_labF [3] ?_
    intro l hl
    simp only [List.mem_singleton] at hl
    rw [hl, gensY_size, mw_getD_length hj]
    norm_num
  rw [h1, h2] at heq
  exact heq

private theorem n3mJ_not_mem_normalizer {j i : ℕ} (hi : i < 3)
    (hj : j = 2 ∨ j = 3 ∨ j = 4)
    (hne : lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (sg i * n3mJ j) ≠
      lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (n3mJ j)) :
    n3mJ j ∉ Subgroup.normalizer (S : Set ↥j3P) := by
  intro hN
  have hN' : (n3mJ j)⁻¹ ∈ Subgroup.normalizer (S : Set ↥j3P) :=
    (Subgroup.normalizer (S : Set ↥j3P)).inv_mem hN
  have hmem : (n3mJ j)⁻¹ * (sg i * n3mJ j) ∈ S := by
    have h := (Subgroup.mem_normalizer_iff.mp hN' (sg i)).mp (n3sg_mem_S hi)
    have e : (n3mJ j)⁻¹ * (sg i * n3mJ j) = (n3mJ j)⁻¹ * sg i * (n3mJ j)⁻¹⁻¹ := by
      group
    rwa [e]
  have heq : lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (n3mJ j) =
      lab 6156 ptLab CFSG.KD.J3Dc.C.Δ (sg i * n3mJ j) := by
    refine (lab_eq_iff (ptLab_lawful (Γ := ↥j3P) (n := 6156)) delta_valid _ _).mpr ?_
    rwa [n3stab_eq_S]
  exact hne heq.symm

theorem normalizer_S_eq : Subgroup.normalizer (S : Set ↥j3P) = Y 1 := by
  let N := Subgroup.normalizer (S : Set ↥j3P)
  have hS_le_N : S ≤ N := Subgroup.le_normalizer
  obtain ⟨j, hj, hNj⟩ := complete N hS_le_N
  have hY0 : Y 0 = S := by
    refine (Subgroup.eq_of_le_of_card_ge (S_le_Y 0) ?_).symm
    rw [member_card (j := 0) (by norm_num)]
    simp
  have hm2 : n3mJ 2 ∉ N :=
    n3mJ_not_mem_normalizer (j := 2) (i := 0) (by norm_num) (Or.inl rfl)
      (n3mJ_label_ne (j := 2) (i := 0) (by norm_num) (Or.inl rfl) n3_parts.2.2.2.2.1)
  have hm3 : n3mJ 3 ∉ N :=
    n3mJ_not_mem_normalizer (j := 3) (i := 0) (by norm_num) (Or.inr (Or.inl rfl))
      (n3mJ_label_ne (j := 3) (i := 0) (by norm_num) (Or.inr (Or.inl rfl))
        n3_parts.2.2.2.2.2.1)
  have hm4 : n3mJ 4 ∉ N :=
    n3mJ_not_mem_normalizer (j := 4) (i := 1) (by norm_num) (Or.inr (Or.inr rfl))
      (n3mJ_label_ne (j := 4) (i := 1) (by norm_num) (Or.inr (Or.inr rfl))
        n3_parts.2.2.2.2.2.2)
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl
  · have hN0 : N = S := by
      rw [hNj]
      simp [memberOrTop, hY0]
    exact absurd (hN0 ▸ n3_mem_normalizer) n3_not_mem_S
  · simpa [memberOrTop] using hNj
  · have hmem : n3mJ 2 ∈ N := by
      rw [hNj, show memberOrTop 5 Y 2 = Y 2 by simp [memberOrTop]]
      exact n3mJ_mem_Y (j := 2) (Or.inl rfl)
    exact absurd hmem hm2
  · have hmem : n3mJ 3 ∈ N := by
      rw [hNj, show memberOrTop 5 Y 3 = Y 3 by simp [memberOrTop]]
      exact n3mJ_mem_Y (j := 3) (Or.inr (Or.inl rfl))
    exact absurd hmem hm3
  · have hmem : n3mJ 4 ∈ N := by
      rw [hNj, show memberOrTop 5 Y 4 = Y 4 by simp [memberOrTop]]
      exact n3mJ_mem_Y (j := 4) (Or.inr (Or.inr rfl))
    exact absurd hmem hm4
  · have hmem : n3mJ 2 ∈ N := by
      rw [hNj, show memberOrTop 5 Y 5 = ⊤ by simp [memberOrTop]]
      exact Subgroup.mem_top _
    exact absurd hmem hm2

theorem card_normalizer_S : Nat.card (Subgroup.normalizer (S : Set ↥j3P)) = 3 * Nat.card S := by
  rw [normalizer_S_eq, member_card (j := 1) (by norm_num)]
  rfl

end Checks

end CFSG.QuasithinUnique.Ch1.SporLat.J3K

end
