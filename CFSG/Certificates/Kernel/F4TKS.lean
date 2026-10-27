module

public import CFSG.Certificates.Kernel.F4TSound
public import CFSG.Certificates.Kernel.F4TInv
import all CFSG.Fischer.F4
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KC.F4T

open CFSG.Fischer CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

@[expose] def vecT (v : List Nat) : Fin 3 → F4 :=
  ![f4 (v.getD 0 0), f4 (v.getD 1 0), f4 (v.getD 2 0)]

theorem ptsT_cover : ∀ v : Fin 3 → F4,
    (v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)) → ∃ p ∈ ptsT, vecT p = v := by
  decide +kernel

theorem vecsT_cover : ∀ w : Fin 3 → F4, w ≠ 0 → ∃ q ∈ vecsT, vecT q = w := by
  decide +kernel

theorem ptsT_lt : ∀ p ∈ ptsT, ∀ x ∈ p, x < 4 := by decide +kernel

theorem vecsT_lt : ∀ q ∈ vecsT, ∀ x ∈ q, x < 4 := by decide +kernel

theorem f4_eq_zero : ∀ x < 4, f4 x = 0 → x = 0 := by decide +kernel

theorem f4_one : f4 1 = 1 := rfl

theorem toMT_outer_num {a0 a1 a2 b0 b1 b2 : Nat} (ha0 : a0 < 4) (ha1 : a1 < 4) (ha2 : a2 < 4)
    (hb0 : b0 < 4) (hb1 : b1 < 4) (hb2 : b2 < 4) :
    toMT ⟨aT 1 (mT a0 b0), mT a0 b1, mT a0 b2, mT a1 b0, aT 1 (mT a1 b1), mT a1 b2, mT a2 b0,
      mT a2 b1, aT 1 (mT a2 b2)⟩ =
      1 + Matrix.vecMulVec ![f4 a0, f4 a1, f4 a2] ![f4 b0, f4 b1, f4 b2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMT, toMat, toLT, Matrix.vecMulVec_apply, Matrix.one_apply, f4_aT, f4_mT, mT_lt, f4_one, *]

theorem toMT_outerT {v w : List Nat} (hv : ∀ x ∈ v, x < 4) (hw : ∀ x ∈ w, x < 4) :
    toMT (outerT v w) = 1 + Matrix.vecMulVec (vecT v) (vecT w) :=
  toMT_outer_num (getD_lt hv 0) (getD_lt hv 1) (getD_lt hv 2) (getD_lt hw 0) (getD_lt hw 1)
    (getD_lt hw 2)

theorem invsT_complete (t : Matrix (Fin 3) (Fin 3) F4) (h1 : t * t = 1) (h2 : t ≠ 1) :
    ∃ A ∈ invsT, toMT A = t := by
  obtain ⟨v, w, hn, hw0, hd, rfl⟩ := inv_eq_one_add_outer t h1 h2
  obtain ⟨p, hp, rfl⟩ := ptsT_cover v hn
  obtain ⟨q, hq, rfl⟩ := vecsT_cover w hw0
  have hpl := ptsT_lt p hp
  have hql := vecsT_lt q hq
  refine ⟨outerT p q, ?_, toMT_outerT hpl hql⟩
  refine List.mem_flatMap.2 ⟨p, hp, List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, ?_⟩, rfl⟩⟩
  have hdot : f4 (dotT (p.getD 0 0) (p.getD 1 0) (p.getD 2 0) (q.getD 0 0) (q.getD 1 0)
      (q.getD 2 0)) = 0 := by
    rw [f4_dotT (getD_lt hpl 0) (getD_lt hpl 1) (getD_lt hpl 2) (getD_lt hql 0) (getD_lt hql 1)
      (getD_lt hql 2)]
    rw [dotProduct_comm] at hd
    simpa [dotProduct, Fin.sum_univ_three, vecT] using hd
  rw [f4_eq_zero _ (dotT_lt _ _ _ _ _ _) hdot]
  rfl

theorem good3_inv {t : Matrix (Fin 3) (Fin 3) F4} (h : Good3 t) : t * t = 1 ∧ t ≠ 1 := by
  simp only [Good3, good3, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

theorem zip_fst_mem {α β : Type} {l₁ : List α} {l₂ : List β} (hlen : l₁.length = l₂.length)
    {a : α} (ha : a ∈ l₁) : ∃ b, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < l₂.length := by rw [← hlen]; exact hi
  exact ⟨l₂[i], List.mem_iff_getElem.2 ⟨i, by simp [List.length_zip, hi, hi'], by simp⟩⟩

theorem f4_inj_all : ∀ a < 4, ∀ b < 4, f4 a = f4 b → a = b := by decide +kernel

theorem toMT_inj {A B : M3 Nat} (hA : OK A) (hB : OK B) (h : toMT A = toMT B) : A = B := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hA
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := hB
  have e : ∀ i j : Fin 3, toMT A i j = toMT B i j := fun i j => by rw [h]
  exact M3.ext (f4_inj_all _ a0 _ b0 (e 0 0)) (f4_inj_all _ a1 _ b1 (e 0 1))
    (f4_inj_all _ a2 _ b2 (e 0 2)) (f4_inj_all _ a3 _ b3 (e 1 0)) (f4_inj_all _ a4 _ b4 (e 1 1))
    (f4_inj_all _ a5 _ b5 (e 1 2)) (f4_inj_all _ a6 _ b6 (e 2 0)) (f4_inj_all _ a7 _ b7 (e 2 1))
    (f4_inj_all _ a8 _ b8 (e 2 2))

theorem lettersT_sound {A : M3 Nat} (hA : OK A) :
    ∀ a ∈ lettersT A, OK a ∧ toMT a ∈ letters (toMT A) := by
  have o1 : OK xdT := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have o2 : OK xd2T := by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  have toMT_xdT : toMT xdT = Xd := by
    rw [← toMat_XdL]
    rfl
  have toMT_xd2T : toMT xd2T = Xd2 := by
    have h : toLT xd2T = mulL XdL XdL := rfl
    rw [toMT, h, toMat_mulL, toMat_XdL]
    rfl
  intro a ha
  simp only [lettersT, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨hA, by simp [letters]⟩
  · refine ⟨mMulT_OK _ _, ?_⟩
    rw [toMT_mMulT (mMulT_OK _ _) o2, toMT_mMulT o1 hA, toMT_xdT, toMT_xd2T]
    simp [letters]
  · refine ⟨mMulT_OK _ _, ?_⟩
    rw [toMT_mMulT (mMulT_OK _ _) o1, toMT_mMulT o2 hA, toMT_xdT, toMT_xd2T]
    simp [letters]

theorem words3T_sound {A : M3 Nat} (hA : OK A) :
    ∀ W ∈ words3T A, OK W ∧ toMT W ∈ words3 (toMT A) := by
  have hL := lettersT_sound hA
  intro W hW
  dsimp only [words3T] at hW
  unfold words3
  rcases List.mem_append.1 hW with hW | hW
  · rcases List.mem_append.1 hW with hW | hW
    · exact ⟨(hL W hW).1, List.mem_append_left _ (List.mem_append_left _ (hL W hW).2)⟩
    · obtain ⟨a, ha, hW⟩ := List.mem_flatMap.1 hW
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hW
      refine ⟨mMulT_OK _ _, List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨_, (hL a ha).2, List.mem_map.2 ⟨_, (hL b hb).2, ?_⟩⟩))⟩
      rw [toMT_mMulT (hL a ha).1 (hL b hb).1]
  · obtain ⟨a, ha, hW⟩ := List.mem_flatMap.1 hW
    obtain ⟨b, hb, hW⟩ := List.mem_flatMap.1 hW
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hW
    refine ⟨mMulT_OK _ _, List.mem_append_right _ (List.mem_flatMap.2 ⟨_, (hL a ha).2,
      List.mem_flatMap.2 ⟨_, (hL b hb).2, List.mem_map.2 ⟨_, (hL c hc).2, ?_⟩⟩⟩)⟩
    rw [toMT_mMulT (mMulT_OK _ _) (hL c hc).1, toMT_mMulT (hL a ha).1 (hL b hb).1]

theorem mEq_self (A : M3 Nat) : mEq A A = true := by
  simp [mEq]

theorem witOK_sound {rows : List (List Nat)} {invs : List (M3 Nat)} {wits : List (Nat × Nat)}
    (h : witOK rows invs wits = true) (hok : ∀ A ∈ invs, OK A) :
    ∀ A ∈ invs, Good3 (toMT A) → ∃ code ∈ rows, matN code = A := by
  simp only [witOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨hlen, hall⟩ := h
  intro A hA hgood
  obtain ⟨x, hx⟩ := zip_fst_mem hlen hA
  have hw := hall _ hx
  have hOK := hok A hA
  unfold wit1OK at hw
  dsimp only at hw
  cases hx0 : Nat.beq x.1 0
  · rw [hx0] at hw
    exfalso
    simp only [Good3, good3, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hgood
    have hW : ∃ W, (words3T A).getD x.2 mOne = W ∧ OK W ∧ toMT W ^ 4 = 1 := by
      rw [List.getD_eq_getElem?_getD]
      cases hg : (words3T A)[x.2]? with
      | none =>
        refine ⟨mOne, rfl, mOne_OK, ?_⟩
        rw [toMT_mOne, one_pow]
      | some W =>
        obtain ⟨hWOK, hWw⟩ := words3T_sound hOK W (List.mem_of_getElem? hg)
        exact ⟨W, rfl, hWOK, hgood.2 _ hWw⟩
    obtain ⟨W, hWe, hWOK, hW4⟩ := hW
    have hp : pow4T W = mOne := by
      refine toMT_inj (mMulT_OK _ _) mOne_OK ?_
      rw [pow4T, toMT_mMulT (mMulT_OK _ _) (mMulT_OK _ _), toMT_mMulT hWOK hWOK, toMT_mOne,
        ← hW4, show (4 : Nat) = 2 + 2 from rfl, pow_add, sq]
    simp only [cond_false, hWe, hp, mEq_self, Bool.not_true] at hw
    exact Bool.false_ne_true hw
  · rw [hx0] at hw
    simp only [cond_true, Bool.and_eq_true, Nat.blt_eq] at hw
    exact ⟨rows.getD x.2 [], by rw [List.getD_eq_getElem _ _ hw.1]; exact List.getElem_mem _,
      (mEq_eq hw.2).symm⟩

theorem witOK_append {rows : List (List Nat)} {L₁ L₂ : List (M3 Nat)} {W₁ W₂ : List (Nat × Nat)}
    (h₁ : witOK rows L₁ W₁ = true) (h₂ : witOK rows L₂ W₂ = true) :
    witOK rows (L₁ ++ L₂) (W₁ ++ W₂) = true := by
  simp only [witOK, Bool.and_eq_true, Nat.beq_eq] at h₁ h₂ ⊢
  refine ⟨by rw [List.length_append, List.length_append, h₁.1, h₂.1], ?_⟩
  rw [List.zip_append h₁.1, List.all_append, h₁.2, h₂.2]
  rfl

theorem witOK_of_chunks (rows : List (List Nat)) (c : Nat) :
    ∀ (n : Nat) (L : List (M3 Nat)) (W : List (Nat × Nat)), L.length = W.length →
      L.length ≤ c * n → (∀ k < n, witOK rows (chunkT c k L) (chunkT c k W) = true) →
      witOK rows L W = true := by
  intro n
  induction n with
  | zero =>
    intro L W hlen hle _
    have hL : L = [] := List.length_eq_zero_iff.1 (by omega)
    have hW : W = [] := List.length_eq_zero_iff.1 (by omega)
    subst hL hW
    rfl
  | succ n ih =>
    intro L W hlen hle h
    have h0 := h 0 (Nat.zero_lt_succ n)
    simp only [chunkT, Nat.mul_zero, List.drop_zero] at h0
    have hrest : witOK rows (L.drop c) (W.drop c) = true := by
      refine ih _ _ (by simp [hlen]) (by simp only [List.length_drop]; rw [Nat.mul_succ] at hle; omega)
        fun k hk => ?_
      have := h (k + 1) (by omega)
      simp only [chunkT, List.drop_drop] at this ⊢
      rwa [Nat.mul_succ, Nat.add_comm] at this
    rw [← List.take_append_drop c L, ← List.take_append_drop c W]
    exact witOK_append h0 hrest

theorem toMT_xdT : toMT xdT = Xd := by
  rw [← toMat_XdL]
  rfl

theorem toMT_xd2T : toMT xd2T = Xd2 := by
  have h : toLT xd2T = mulL XdL XdL := rfl
  rw [toMT, h, toMat_mulL, toMat_XdL]
  rfl

theorem toMT_zsT : toMT zsT = Zs := by
  rw [← toMat_ZsL]
  rfl

theorem toMT_zs2T : toMT zs2T = Zs * Zs := by
  have h : toLT zs2T = mulL ZsL ZsL := rfl
  rw [toMT, h, toMat_mulL, toMat_ZsL]

theorem toMT_wmT (c : Nat) : toMT (wmT c) = Wm (f4 c) := by
  rw [← toMat_WmL]
  rfl

theorem toLT_wm2T_all : ∀ c < 4, toLT (wm2T c) = mulL (WmL (f4 c)) (WmL (f4 c)) := by
  decide +kernel

theorem toMT_wm2T {c : Nat} (hc : c < 4) : toMT (wm2T c) = Wm (f4 c) * Wm (f4 c) := by
  rw [toMT, toLT_wm2T_all c hc, toMat_mulL, toMat_WmL]

theorem OK_of_lt {A : M3 Nat} (h : ∀ x ∈ [A.a00, A.a01, A.a02, A.a10, A.a11, A.a12, A.a20, A.a21,
    A.a22], x < 4) : OK A := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact h

theorem wmT_OK {c : Nat} (hc : c < 4) : OK (wmT c) := by
  refine OK_of_lt ?_
  simp only [wmT, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> first | exact hc | decide

theorem wm2T_OK {c : Nat} (hc : c < 4) : OK (wm2T c) := by
  refine OK_of_lt ?_
  simp only [wm2T, List.mem_cons, List.not_mem_nil, or_false]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> first | exact hc | decide

theorem consts_OK : OK xdT ∧ OK xd2T ∧ OK zsT ∧ OK zs2T := by
  refine ⟨OK_of_lt ?_, OK_of_lt ?_, OK_of_lt ?_, OK_of_lt ?_⟩ <;> decide

theorem gensT3_in {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)}
    {x w z t : Matrix.GeneralLinearGroup (Fin 3) F4} {c : Nat} (hc : c < 4) {A : M3 Nat}
    (hA : OK A) (hx : x ∈ H) (hxM : (x : Matrix (Fin 3) (Fin 3) F4) = Xd)
    (hw : w ∈ H) (hwM : (w : Matrix (Fin 3) (Fin 3) F4) = Wm (f4 c))
    (hz : z ∈ H) (hzM : (z : Matrix (Fin 3) (Fin 3) F4) = Zs)
    (ht : t ∈ H) (htM : toMT A = (t : Matrix (Fin 3) (Fin 3) F4)) : GensIn H (gensT3 c A) := by
  have hX : InM H Xd := ⟨x, hx, hxM⟩
  have hW : InM H (Wm (f4 c)) := ⟨w, hw, hwM⟩
  have hZ : InM H Zs := ⟨z, hz, hzM⟩
  obtain ⟨o1, o2, o3, o4⟩ := consts_OK
  intro g hg
  simp only [gensT3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨o1, by rw [toMT_xdT]; exact hX⟩
  · exact ⟨o2, by rw [toMT_xd2T]; exact InM_mul hX hX⟩
  · exact ⟨wmT_OK hc, by rw [toMT_wmT]; exact hW⟩
  · exact ⟨wm2T_OK hc, by rw [toMT_wm2T hc]; exact InM_mul hW hW⟩
  · exact ⟨o3, by rw [toMT_zsT]; exact hZ⟩
  · exact ⟨o4, by rw [toMT_zs2T]; exact InM_mul hZ hZ⟩
  · exact ⟨hA, ⟨t, ht, htM.symm⟩⟩

theorem SL_of_w6OK {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)} {gens : List (M3 Nat)}
    (hg : GensIn H gens) (hX : InM H Xd) {ws : List (List Nat)} (h : w6OK gens ws = true) :
    SLsub ≤ H := by
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ := w6OK_sound hg h
  exact SLsub_le_of_words hX (InM_mul hX hX) h01 h02 h10 h12 h20 h21

theorem t3RowOK_spec {code : List Nat} {w1 wo wo2 : List (List Nat)}
    (h : t3RowOK code w1 wo wo2 = true) :
    codeOK code = true ∧ w6OK (gensT3 2 (matN code)) wo = true ∧
      w6OK (gensT3 3 (matN code)) wo2 = true ∧
      (isRootT (matN code) = true → w6OK (gensT3 1 (matN code)) w1 = true) := by
  simp only [t3RowOK, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun hr => ?_⟩
  rcases h4 with h4 | h4
  · rw [hr] at h4
    exact absurd h4 (by decide)
  · exact h4

theorem t3Rows_of_chunks {codes : List (List Nat)} {w1 wo wo2 : List (List (List Nat))}
    (hlen : codes.length = 72 ∧ w1.length = 72 ∧ wo.length = 72 ∧ wo2.length = 72)
    (h : ∀ k < 3, t3RowsOK (chunkT 24 k codes) (chunkT 24 k w1) (chunkT 24 k wo)
      (chunkT 24 k wo2) = true) :
    ∀ i < 72, t3RowOK (codes.getD i []) (w1.getD i []) (wo.getD i []) (wo2.getD i []) = true := by
  intro i hi
  obtain ⟨h1, h2, h3, h4⟩ := hlen
  have hk := h (i / 24) (by omega)
  simp only [t3RowsOK, Bool.and_eq_true, List.all_eq_true] at hk
  have hlt : i % 24 < ((chunkT 24 (i / 24) codes).zip ((chunkT 24 (i / 24) w1).zip
      ((chunkT 24 (i / 24) wo).zip (chunkT 24 (i / 24) wo2)))).length := by
    simp only [chunkT, List.length_zip, List.length_take, List.length_drop, h1, h2, h3, h4]
    omega
  have hz := hk.2 _ (List.getElem_mem hlt)
  simp only [List.getElem_zip, chunkT, List.getElem_take, List.getElem_drop, Nat.div_add_mod]
    at hz
  rw [List.getD_eq_getElem codes [] (by omega : i < codes.length),
    List.getD_eq_getElem w1 [] (by omega : i < w1.length),
    List.getD_eq_getElem wo [] (by omega : i < wo.length),
    List.getD_eq_getElem wo2 [] (by omega : i < wo2.length)]
  exact hz

end CFSG.KC.F4T

end
