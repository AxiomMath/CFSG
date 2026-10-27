module

public import Certificates.Certificate22231
public import CFSG.Sporadic.Schreier.ONSchreierData

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.F3.Native CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier

theorem n0_check :
    (okRows n0Rows && okRows n0InvRows && eqM 154 (mul 154 n0Rows n0InvRows) (idM 154)) = true :=
  Certificates.certificate22231.1

theorem strong_check :
    ((List.range 7).all fun j =>
      okRows sIRows[j]! && eqM 154 (mul 154 sRows[j]! sIRows[j]!) (idM 154)) = true :=
  Certificates.certificate22231.2.1

theorem conjA_check :
    eqM 154 (mul 154 (mul 154 n0Rows rowsA) n0InvRows) (wordRows sRows sIRows wA) = true :=
  Certificates.certificate22231.2.2.1

theorem conjB_check :
    eqM 154 (mul 154 (mul 154 n0Rows rowsB) n0InvRows) (wordRows sRows sIRows wB) = true :=
  Certificates.certificate22231.2.2.2.1

theorem z_check :
    eqM 154 (mul 154 n0Rows zRows) (mul 154 zRows n0Rows) = true :=
  Certificates.certificate22231.2.2.2.2.1

theorem sq_check :
    (eqM 154 (mul 154 n0SqRows rowsA) (mul 154 rowsA n0SqRows) &&
      eqM 154 (mul 154 n0SqRows rowsB) (mul 154 rowsB n0SqRows)) = true :=
  Certificates.certificate22231.2.2.2.2.2

theorem size_of_okRows {X : Array V} (h : okRows X = true) : X.size = 154 := by
  unfold okRows at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem rowsWF_of_okRows {X : Array V} (h : okRows X = true) : RowsWF X := by
  unfold okRows at h
  simp only [Bool.and_eq_true] at h
  exact rowsWF_of_wfM h.2

theorem size_mul {X Y : Array V} : (mul 154 X Y).size = X.size := by
  simp [CFSG.F3.Native.mul]

theorem size_idM : (idM 154).size = 154 := by simp [idM]

theorem toMat_mul' {X Y : Array V} (hX : X.size = 154) (hXw : RowsWF X) (hYw : RowsWF Y) :
    toMat 154 (mul 154 X Y) = toMat 154 X * toMat 154 Y :=
  toMat_mul hX hXw hYw

@[expose] def RowsFor (S Si : Array (Array V)) (g : ℕ → J) (k : ℕ) : Prop :=
  ∀ h < k, S[h]!.size = 154 ∧ RowsWF S[h]! ∧ toMat 154 S[h]! = mat (g h) ∧
    Si[h]!.size = 154 ∧ RowsWF Si[h]! ∧ toMat 154 Si[h]! = mat (g h)⁻¹

@[expose] def ValidW (k : ℕ) (w : List ℤ) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k

@[expose] def validB (k : ℕ) (w : List ℤ) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ k)

theorem validW_of_validB {k : ℕ} {w : List ℤ} (h : validB k w = true) : ValidW k w := by
  intro l hl
  unfold validB at h
  rw [List.all_eq_true] at h
  have := h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem ptoLetters_cons {k : ℕ} {l : ℤ} (hl : l ≠ 0 ∧ l.natAbs ≤ k) (w : List ℤ) :
    ptoLetters k (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) :: ptoLetters k w := by
  simp only [ptoLetters, List.filterMap_cons, dite_eq_left hl]

theorem wordRows_spec {S Si : Array (Array V)} {g : ℕ → J} {k : ℕ} (hS : RowsFor S Si g k) :
    ∀ w : List ℤ, ValidW k w →
      (wordRows S Si w).size = 154 ∧ RowsWF (wordRows S Si w) ∧
        toMat 154 (wordRows S Si w) =
          mat (Quiver.SchreierGraph.evalWord (fun h : Fin k => g h.val) (ptoLetters k w))
  | [], _ => by
    refine ⟨size_idM, RowsWF.idM 154, ?_⟩
    rw [wordRows, toMat_idM]
    simp [ptoLetters, Quiver.SchreierGraph.evalWord_nil, mat_one]
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have hw' : ValidW k w := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    obtain ⟨h1, h2, h3⟩ := wordRows_spec hS w hw'
    have hidx : l.natAbs - 1 < k := by omega
    obtain ⟨s1, s2, s3, i1, i2, i3⟩ := hS (l.natAbs - 1) hidx
    rw [wordRows, ptoLetters_cons hl]
    by_cases hpos : 0 < l
    · have he : l.toNat - 1 = l.natAbs - 1 := by omega
      have hlet : letterRows S Si l = S[l.natAbs - 1]! := by
        rw [letterRows, ite_eq_left hpos, he]
      rw [hlet]
      refine ⟨by rw [size_mul, s1], RowsWF.mul _ 154 s2 h2, ?_⟩
      rw [toMat_mul' s1 s2 h2, s3, h3, decide_eq_true hpos,
        Quiver.SchreierGraph.evalWord_cons_true, mat_mul]
    · have he : (-l).toNat - 1 = l.natAbs - 1 := by omega
      have hlet : letterRows S Si l = Si[l.natAbs - 1]! := by
        rw [letterRows, ite_eq_right hpos, he]
      rw [hlet]
      refine ⟨by rw [size_mul, i1], RowsWF.mul _ 154 i2 h2, ?_⟩
      rw [toMat_mul' i1 i2 h2, i3, h3, decide_eq_false hpos,
        Quiver.SchreierGraph.evalWord_cons_false, mat_mul]

theorem map_evalWord {G H : Type*} [Group G] [Group H] (f : G →* H) {k : ℕ} (ι : Fin k → G) :
    ∀ w : List (Fin k × Bool),
      f (Quiver.SchreierGraph.evalWord ι w) = Quiver.SchreierGraph.evalWord (fun h => f (ι h)) w
  | [] => by rw [Quiver.SchreierGraph.evalWord_nil, Quiver.SchreierGraph.evalWord_nil, map_one]
  | (s, true) :: w => by
    rw [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_true, map_mul,
      map_evalWord f ι w]
  | (s, false) :: w => by
    rw [Quiver.SchreierGraph.evalWord_cons_false, Quiver.SchreierGraph.evalWord_cons_false,
      map_mul, map_inv, map_evalWord f ι w]

@[expose] def gJ (j : ℕ) : J := jEquivPv.symm ⟨sgen j, sgen_mem j⟩

theorem phiV_gJ (j : ℕ) : phiV (gJ j) = sgen j := by
  rw [← jEquivPv_apply, gJ, MulEquiv.apply_symm_apply]

theorem gJ_eq_of_phiV {j : ℕ} {g : J} (h : phiV g = sgen j) : gJ j = g :=
  phiV_injective (by rw [phiV_gJ, h])

structure Link (j : ℕ) : Prop where
  size : sRows[j]!.size = 154
  wf : RowsWF sRows[j]!
  mat_eq : toMat 154 sRows[j]! = mat (gJ j)
  isize : sIRows[j]!.size = 154
  iwf : RowsWF sIRows[j]!
  imat_eq : toMat 154 sIRows[j]! = mat (gJ j)⁻¹

theorem link_of {j : ℕ} (hj : j < 7) (h1 : sRows[j]!.size = 154)
    (h2 : RowsWF sRows[j]!) (h3 : toMat 154 sRows[j]! = mat (gJ j)) : Link j := by
  have hc := strong_check
  rw [List.all_eq_true] at hc
  have hj' := hc j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true] at hj'
  obtain ⟨hok, heq⟩ := hj'
  have hi1 := size_of_okRows hok
  have hi2 := rowsWF_of_okRows hok
  refine ⟨h1, h2, h3, hi1, hi2, ?_⟩
  have e := toMat_eq_of_eqM heq
  rw [toMat_mul' h1 h2 hi2, toMat_idM, h3] at e
  calc toMat 154 sIRows[j]! = mat (gJ j)⁻¹ * (mat (gJ j) * toMat 154 sIRows[j]!) := by
        rw [← mul_assoc, ← mat_mul, inv_mul_cancel, mat_one, one_mul]
    _ = mat (gJ j)⁻¹ := by rw [e, mul_one]

theorem rowsA_size' : rowsA.size = 154 := by simp [rowsA, rowsOf]

theorem rowsB_size' : rowsB.size = 154 := by simp [rowsB, rowsOf]

theorem gJ_zero : gJ 0 = ga := gJ_eq_of_phiV (by
  rw [phiV_ga, sgen, wordStrong_of_lt _ _ (by simp)]
  rfl)

theorem gJ_one : gJ 1 = gb := gJ_eq_of_phiV (by
  rw [phiV_gb, sgen, wordStrong_of_lt _ _ (by simp)]
  rfl)

theorem sRows_zero : sRows[0]! = rowsA := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_zero]
  rfl

theorem sRows_one : sRows[1]! = rowsB := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]
  rfl

theorem link0 : Link 0 :=
  link_of (by norm_num) (by rw [sRows_zero]; exact rowsA_size')
    (by rw [sRows_zero]; exact rowsWF_rowsA) (by rw [sRows_zero, gJ_zero, mat_ga, toMat_rowsA])

theorem link1 : Link 1 :=
  link_of (by norm_num) (by rw [sRows_one]; exact rowsB_size')
    (by rw [sRows_one]; exact rowsWF_rowsB) (by rw [sRows_one, gJ_one, mat_gb, toMat_rowsB])

theorem link_step {j : ℕ} (hj2 : 2 ≤ j) (hj : j < 7)
    {S Si : Array (Array V)} (hS : ∀ h < j, S[h]! = sRows[h]! ∧ Si[h]! = sIRows[h]!)
    (hlinks : ∀ h < j, Link h)
    (hdef : sRows[j]! = wordRows S Si CFSG.ONSchreier.Data.strongWords[j]!)
    (hvalid : ValidW j CFSG.ONSchreier.Data.strongWords[j]!) : Link j := by
  have hR : RowsFor S Si gJ j := fun h hh => by
    obtain ⟨e1, e2⟩ := hS h hh
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlinks h hh
    rw [e1, e2]
    exact ⟨l1, l2, l3, l4, l5, l6⟩
  obtain ⟨w1, w2, w3⟩ := wordRows_spec hR _ hvalid
  refine link_of hj (by rw [hdef]; exact w1) (by rw [hdef]; exact w2) ?_
  rw [hdef, w3]
  congr 1
  refine (gJ_eq_of_phiV ?_).symm
  rw [map_evalWord, sgen, wordStrong_of_ge _ _ (by simp; omega)]
  congr 1
  funext h
  rw [phiV_gJ]
  rfl

theorem lit_eq (j : ℕ) {S Si : Array (Array V)} (hS : S = sRows.extract 0 j)
    (hSi : Si = sIRows.extract 0 j) : ∀ h < j, S[h]! = sRows[h]! ∧ Si[h]! = sIRows[h]! := by
  intro h hh
  subst hS hSi
  have h7 : sRows.size = 7 := rfl
  have h7' : sIRows.size = 7 := rfl
  by_cases hh7 : h < 7
  · constructor
    · rw [getElem!_pos _ h (by simp [h7]; omega), getElem!_pos sRows h (by rw [h7]; exact hh7),
        Array.getElem_extract]
      simp
    · rw [getElem!_pos _ h (by simp [h7']; omega), getElem!_pos sIRows h (by rw [h7']; exact hh7),
        Array.getElem_extract]
      simp
  · constructor
    · rw [getElem!_neg _ h (by simp [h7]; omega), getElem!_neg sRows h (by rw [h7]; exact hh7)]
    · rw [getElem!_neg _ h (by simp [h7']; omega), getElem!_neg sIRows h (by rw [h7']; exact hh7)]

theorem sRows_2 : sRows[2]! = sR2 := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem link2 : Link 2 :=
  link_step (S := #[sR0, sR1]) (Si := #[sI0, sI1]) le_rfl
    (by norm_num) (lit_eq 2 (by simp [sRows]) (by simp [sIRows]))
    (fun h hh => by interval_cases h; exacts [link0, link1])
    (by rw [sRows_2]; rfl) (validW_of_validB (by decide +kernel))

theorem sRows_3 : sRows[3]! = sR3 := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem link3 : Link 3 :=
  link_step (S := #[sR0, sR1, sR2]) (Si := #[sI0, sI1, sI2]) (by norm_num)
    (by norm_num) (lit_eq 3 (by simp [sRows]) (by simp [sIRows]))
    (fun h hh => by interval_cases h; exacts [link0, link1, link2])
    (by rw [sRows_3]; rfl) (validW_of_validB (by decide +kernel))

theorem sRows_4 : sRows[4]! = sR4 := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem link4 : Link 4 :=
  link_step (S := #[sR0, sR1, sR2, sR3]) (Si := #[sI0, sI1, sI2, sI3]) (by norm_num)
    (by norm_num) (lit_eq 4 (by simp [sRows]) (by simp [sIRows]))
    (fun h hh => by interval_cases h; exacts [link0, link1, link2, link3])
    (by rw [sRows_4]; rfl) (validW_of_validB (by decide +kernel))

theorem sRows_5 : sRows[5]! = sR5 := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem link5 : Link 5 :=
  link_step (S := #[sR0, sR1, sR2, sR3, sR4]) (Si := #[sI0, sI1, sI2, sI3, sI4]) (by norm_num)
    (by norm_num) (lit_eq 5 (by simp [sRows]) (by simp [sIRows]))
    (fun h hh => by interval_cases h; exacts [link0, link1, link2, link3, link4])
    (by rw [sRows_5]; rfl) (validW_of_validB (by decide +kernel))

theorem sRows_6 : sRows[6]! = sR6 := by
  simp only [sRows, List.getElem!_toArray, List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem link6 : Link 6 :=
  link_step (S := #[sR0, sR1, sR2, sR3, sR4, sR5]) (Si := #[sI0, sI1, sI2, sI3, sI4, sI5])
    (by norm_num) (by norm_num) (lit_eq 6 (by simp [sRows]) (by simp [sIRows]))
    (fun h hh => by interval_cases h; exacts [link0, link1, link2, link3, link4, link5])
    (by rw [sRows_6]; rfl) (validW_of_validB (by decide +kernel))

theorem links : ∀ h < 7, Link h := by
  intro h hh
  interval_cases h
  exacts [link0, link1, link2, link3, link4, link5, link6]

theorem rowsFor_strong : RowsFor sRows sIRows gJ 7 :=
  fun h hh => let L := links h hh; ⟨L.size, L.wf, L.mat_eq, L.isize, L.iwf, L.imat_eq⟩

end CFSG.ComponentClassification.SolMax.ONOut
