module

public import Certificates.Certificate22233
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK1Sigma
public import CFSG.Sporadic.ONOddCore.OuterLocal

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.ONOut

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem sig_strong_check :
    strongOK nPts (wordArr wA) (wordArr wB) sigStrong Data.strongWords = true :=
  Certificates.certificate22233.1

theorem m_tree_check :
    treeOK 161280 3 (arrStep hArrs) base3 mPar mLab mIm = true :=
  Certificates.certificate22233.2.1

theorem m_sim_check :
    treeOK 161280 3 (arrStep vArrs) base3 mPar mLab mSim = true :=
  Certificates.certificate22233.2.2.1

theorem m_distinct_check : distinctOK 161280 mIm = true :=
  Certificates.certificate22233.2.2.2.1

theorem t_count_check : tList.length ≤ 1344 :=
  Certificates.certificate22233.2.2.2.2.1

theorem cover_check : allBelowN 161280 cTest = true :=
  Certificates.certificate22233.2.2.2.2.2.1

theorem f_check :
    (treeOK 60 2 fStep base3 fPar fLab fIm && fIm.size == 60 && distinctOK 60 fIm &&
      fClosedOK && fNoZOK && fFixOK && fCommOK) = true :=
  Certificates.certificate22233.2.2.2.2.2.2

section Act


@[expose] def pAct (x : Pv) (p : ℕ) : ℕ :=
  if h : p < N then ((x : Equiv.Perm (Fin N)) ⟨p, h⟩ : ℕ) else p

theorem pAct_of_lt (x : Pv) {p : ℕ} (hp : p < N) :
    pAct x p = ((x : Equiv.Perm (Fin N)) ⟨p, hp⟩ : ℕ) := by
  rw [pAct, dite_eq_left hp]

theorem pAct_of_not_lt (x : Pv) {p : ℕ} (hp : ¬ p < N) : pAct x p = p := by
  rw [pAct, dite_eq_right hp]

theorem pAct_lt (x : Pv) {p : ℕ} (hp : p < N) : pAct x p < N := by
  rw [pAct_of_lt x hp]
  exact Fin.isLt _

theorem pAct_fin (x : Pv) (a : Fin N) : pAct x a = ((x : Equiv.Perm (Fin N)) a : ℕ) :=
  pAct_of_lt x a.isLt

theorem pAct_mul (x y : Pv) (p : ℕ) : pAct (x * y) p = pAct x (pAct y p) := by
  by_cases hp : p < N
  · rw [pAct_of_lt (x * y) hp, pAct_of_lt y hp, pAct_fin]
    rfl
  · rw [pAct_of_not_lt _ hp, pAct_of_not_lt _ hp, pAct_of_not_lt _ hp]

theorem pAct_one (p : ℕ) : pAct 1 p = p := by
  by_cases hp : p < N
  · rw [pAct_of_lt _ hp]
    rfl
  · rw [pAct_of_not_lt _ hp]

theorem getElem_eq_pAct {A : Array ℕ} {x : Pv} (h : PRep N A (x : Equiv.Perm (Fin N))) {p : ℕ}
    (hp : p < N) : A[p]! = pAct x p := by
  rw [pAct_of_lt x hp]
  exact h ⟨p, hp⟩

@[expose] def pAct3 (x : Pv) (t : Pt3) : Pt3 := map3 (pAct x) t

@[expose] def Valid3 (t : Pt3) : Prop := t.1 < N ∧ t.2.1 < N ∧ t.2.2 < N

theorem valid3_pAct3 (x : Pv) {t : Pt3} (ht : Valid3 t) : Valid3 (pAct3 x t) :=
  ⟨pAct_lt x ht.1, pAct_lt x ht.2.1, pAct_lt x ht.2.2⟩

theorem pAct3_mul (x y : Pv) (t : Pt3) : pAct3 (x * y) t = pAct3 x (pAct3 y t) := by
  simp only [pAct3, map3, pAct_mul]

theorem pAct3_one (t : Pt3) : pAct3 1 t = t := by
  simp only [pAct3, map3, pAct_one]

theorem valid3_base3 : Valid3 base3 :=
  ⟨by norm_num [base3], by norm_num [base3], by norm_num [base3]⟩

theorem arrStep_eq {A : Array (Array ℕ)} {l : ℕ} {x : Pv}
    (h : PRep N A[l]! (x : Equiv.Perm (Fin N))) {t : Pt3} (ht : Valid3 t) :
    arrStep A l t = pAct3 x t := by
  simp only [arrStep, pAct3, map3, getElem_eq_pAct h ht.1, getElem_eq_pAct h ht.2.1,
    getElem_eq_pAct h ht.2.2]

theorem eq_of_pAct3 {x y : Pv}
    (h : pAct3 x base3 = pAct3 y base3) : x = y := by
  simp only [pAct3, map3, base3, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [pAct_of_lt x (p := 0) (by norm_num), pAct_of_lt y (p := 0) (by norm_num)] at h0
  rw [pAct_of_lt x (p := 227759) (by norm_num), pAct_of_lt y (p := 227759) (by norm_num)] at h1
  rw [pAct_of_lt x (p := 100817) (by norm_num), pAct_of_lt y (p := 100817) (by norm_num)] at h2
  exact Subtype.ext (eq_of_three x.2 y.2 (Fin.ext h0) (Fin.ext h1) (Fin.ext h2))

@[expose] def treeElt (g : ℕ → Pv) (par lab : Array ℕ) (k : ℕ) : Pv :=
  if _h : 0 < k ∧ par[k]! < k then g lab[k]! * treeElt g par lab par[k]! else 1
termination_by k
decreasing_by exact _h.2

theorem treeElt_zero (g : ℕ → Pv) (par lab : Array ℕ) : treeElt g par lab 0 = 1 := by
  rw [treeElt, dite_eq_right (by omega)]

theorem treeElt_of_lt (g : ℕ → Pv) (par lab : Array ℕ) {k : ℕ} (hk : 0 < k) (hp : par[k]! < k) :
    treeElt g par lab k = g lab[k]! * treeElt g par lab par[k]! := by
  rw [treeElt, dite_eq_left ⟨hk, hp⟩]

theorem treeOK_parts {n ng : ℕ} {step : ℕ → Pt3 → Pt3} {start : Pt3} {par lab : Array ℕ}
    {im : Array Pt3} (h : treeOK n ng step start par lab im = true) :
    im[0]! = start ∧ ∀ k, 0 < k → k < n →
      par[k]! < k ∧ lab[k]! < ng ∧ im[k]! = step lab[k]! im[par[k]!]! := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h0, hall⟩ := h
  refine ⟨h0, fun k hk hkn => ?_⟩
  have := allBelowN_spec hall hkn
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h | ⟨⟨h1, h2⟩, h3⟩
  · omega
  · exact ⟨h1, h2, h3⟩

theorem tree_spec {n ng : ℕ} {step : ℕ → Pt3 → Pt3} {start : Pt3} {par lab : Array ℕ}
    {im : Array Pt3} (h : treeOK n ng step start par lab im = true) (g : ℕ → Pv)
    (hstart : Valid3 start) (hstep : ∀ l < ng, ∀ t, Valid3 t → step l t = pAct3 (g l) t) :
    ∀ k < n, im[k]! = pAct3 (treeElt g par lab k) start := by
  obtain ⟨h0, hk⟩ := treeOK_parts h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [h0, treeElt_zero, pAct3_one]
    · obtain ⟨hp, hl, he⟩ := hk k hpos hkn
      rw [he, ih _ hp (by omega), hstep _ hl _ (valid3_pAct3 _ hstart), ← pAct3_mul,
        treeElt_of_lt g par lab hpos hp]

theorem treeElt_mem {n ng : ℕ} {step : ℕ → Pt3 → Pt3} {start : Pt3} {par lab : Array ℕ}
    {im : Array Pt3} (h : treeOK n ng step start par lab im = true) (g : ℕ → Pv)
    (H : Subgroup Pv) (hg : ∀ l < ng, g l ∈ H) : ∀ k < n, treeElt g par lab k ∈ H := by
  obtain ⟨-, hk⟩ := treeOK_parts h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [treeElt_zero]
      exact H.one_mem
    · obtain ⟨hpk, hl, -⟩ := hk k hpos hkn
      rw [treeElt_of_lt g par lab hpos hpk]
      exact H.mul_mem (hg _ hl) (ih _ hpk (by omega))

theorem map_treeElt (φ : MulAut Pv) (g : ℕ → Pv) (par lab : Array ℕ) (k : ℕ) :
    φ (treeElt g par lab k) = treeElt (fun l => φ (g l)) par lab k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : 0 < k ∧ par[k]! < k
    · rw [treeElt_of_lt g par lab hk.1 hk.2, treeElt_of_lt _ par lab hk.1 hk.2, map_mul,
        ih _ hk.2]
    · rw [treeElt, dite_eq_right hk, treeElt, dite_eq_right hk, map_one]

theorem pathEval_spec {n ng : ℕ} {step : ℕ → Pt3 → Pt3} {start : Pt3} {par lab : Array ℕ}
    {im : Array Pt3} (h : treeOK n ng step start par lab im = true) {A : Array (Array ℕ)}
    (g : ℕ → Pv) (hA : ∀ l < ng, PRep N A[l]! (g l : Equiv.Perm (Fin N))) :
    ∀ k < n, ∀ p < N, pathEval A par lab k p = pAct (treeElt g par lab k) p := by
  obtain ⟨-, hk⟩ := treeOK_parts h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkn p hp
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pathEval, dite_eq_right (by omega), treeElt_zero, pAct_one]
    · obtain ⟨hpk, hl, -⟩ := hk k hpos hkn
      rw [pathEval, dite_eq_left ⟨hpos, hpk⟩, ih _ hpk (by omega) p hp,
        getElem_eq_pAct (hA _ hl) (pAct_lt _ hp), ← pAct_mul, treeElt_of_lt g par lab hpos hpk]

theorem evalW_spec {A : Array (Array ℕ)} {g : ℕ → Pv} {ng : ℕ}
    (hA : ∀ l < ng, PRep N A[l]! (g l : Equiv.Perm (Fin N))) :
    ∀ w : List ℕ, (∀ a ∈ w, a < ng) → ∀ p < N, evalW A w p = pAct (w.map g).prod p
  | [], _, p, _ => by
    rw [List.map_nil, List.prod_nil, pAct_one]
    rfl
  | a :: w, hw, p, hp => by
    have ih := evalW_spec hA w (fun b hb => hw b (List.mem_cons_of_mem a hb)) p hp
    have e : evalW A (a :: w) p = (A[a]!)[evalW A w p]! := rfl
    rw [e, ih, getElem_eq_pAct (hA a (hw a (by simp))) (pAct_lt _ hp), ← pAct_mul,
      List.map_cons, List.prod_cons]

theorem distinct_spec {n : ℕ} {im : Array Pt3} (h : distinctOK n im = true) {k k' : ℕ}
    (hk : k < n) (hk' : k' < n) (he : im[k]! = im[k']!) : k = k' := by
  dsimp only [distinctOK] at h
  have h1 := allBelowN_spec h hk
  have h2 := allBelowN_spec h hk'
  simp only [beq_iff_eq] at h1 h2
  rw [he] at h1
  exact h1.symm.trans h2

end Act

section Sigma


@[expose] def sgenP (j : ℕ) : Pv := ⟨sgen j, sgen_mem j⟩

theorem coe_evalWord_P {k : ℕ} (ι : Fin k → Pv) (w : List (Fin k × Bool)) :
    ((Quiver.SchreierGraph.evalWord ι w : Pv) : Equiv.Perm (Fin N)) =
      Quiver.SchreierGraph.evalWord (fun h => (ι h : Equiv.Perm (Fin N))) w :=
  map_evalWord Pv.subtype ι w

theorem sgenP_word {j : ℕ} (hj : 2 ≤ j) :
    sgenP j = Quiver.SchreierGraph.evalWord (fun h : Fin j => sgenP h)
      (ptoLetters j Data.strongWords[j]!) := by
  apply Subtype.ext
  rw [coe_evalWord_P]
  show sgen j = _
  rw [sgen, wordStrong_of_ge _ _ (by simpa using hj)]
  rfl

theorem map_evalWord_hom {G H : Type*} [Group G] [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (f : F) {k : ℕ} (ι : Fin k → G) :
    ∀ w : List (Fin k × Bool),
      f (Quiver.SchreierGraph.evalWord ι w) = Quiver.SchreierGraph.evalWord (fun h => f (ι h)) w
  | [] => by rw [Quiver.SchreierGraph.evalWord_nil, Quiver.SchreierGraph.evalWord_nil, map_one]
  | (s, true) :: w => by
    rw [Quiver.SchreierGraph.evalWord_cons_true, Quiver.SchreierGraph.evalWord_cons_true, map_mul,
      map_evalWord_hom f ι w]
  | (s, false) :: w => by
    rw [Quiver.SchreierGraph.evalWord_cons_false, Quiver.SchreierGraph.evalWord_cons_false,
      map_mul, map_inv, map_evalWord_hom f ι w]

theorem sigma_evalWord {k : ℕ} (ι : Fin k → Pv)
    (w : List (Fin k × Bool)) :
    ((sigmaPv (Quiver.SchreierGraph.evalWord ι w) : Pv) : Equiv.Perm (Fin N)) =
      Quiver.SchreierGraph.evalWord (fun h => ((sigmaPv (ι h) : Pv) : Equiv.Perm (Fin N))) w := by
  rw [map_evalWord_hom sigmaPv ι w, coe_evalWord_P]

theorem sigStrong_parts :
    sigStrong.size = 7 ∧ peq nPts sigStrong[0]! (wordArr wA) = true ∧
      peq nPts sigStrong[1]! (wordArr wB) = true ∧
      (∀ j < 7, pisInv nPts sigStrong[j]! sigStrongInv[j]! = true) ∧
      ∀ j < 7, 2 ≤ j → plettersOK j Data.strongWords[j]! = true ∧
        peq nPts sigStrong[j]! (pword nPts sigStrong sigStrongInv Data.strongWords[j]!) =
          true := by
  have h := sig_strong_check
  unfold strongOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hsz⟩, h0⟩, h1⟩, hinv⟩, hw⟩ := h
  have hs : sigStrong.size = 7 := hsz.trans words_facts.1
  refine ⟨hs, h0, h1, fun j hj => allBelowN_spec hinv (by rw [hs]; exact hj), fun j hj hj2 => ?_⟩
  have := allBelowN_spec hw (by rw [hs]; exact hj)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at this
  rcases this with h | h
  · omega
  · exact h

theorem prep_sigStrong :
    ∀ j < 7, PRep N sigStrong[j]! (sigmaPv (sgenP j) : Equiv.Perm (Fin N)) ∧
      PRep N sigStrongInv[j]! (sigmaPv (sgenP j) : Equiv.Perm (Fin N))⁻¹ := by
  obtain ⟨-, h0, h1, hinv, hw⟩ := sigStrong_parts
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have key : PRep N sigStrong[j]! (sigmaPv (sgenP j) : Equiv.Perm (Fin N)) := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | hj2
      · have e : sgenP 0 = ⟨a0, a0_mem⟩ := Subtype.ext (by
          show sgen 0 = a0
          rw [sgen, wordStrong_of_lt _ _ (by simp)]
          rfl)
        rw [e, sigmaPv_a0]
        exact prep_of_peq h0 (prep_wordArr (by decide))
      · have e : sgenP 1 = ⟨a1, a1_mem⟩ := Subtype.ext (by
          show sgen 1 = a1
          rw [sgen, wordStrong_of_lt _ _ (by simp)]
          rfl)
        rw [e, sigmaPv_a1]
        exact prep_of_peq h1 (prep_wordArr (by decide))
      · obtain ⟨hl, hpe⟩ := hw j hj hj2
        refine prep_of_peq hpe ?_
        have hp := prep_pword (gs := fun h => (sigmaPv (sgenP h) : Equiv.Perm (Fin N)))
          (fun h hh => (ih h hh (by omega)).1) (fun h hh => (ih h hh (by omega)).2) _ hl
        rw [sgenP_word hj2, sigma_evalWord]
        exact hp
    exact ⟨key, prep_inv_of_pisInv key (hinv j hj)⟩

@[expose] def hP (l : ℕ) : Pv := ⟨evalS Data.MWords[l]!, evalS_mem _⟩

theorem evalS_word (w : List ℤ) :
    (⟨evalS w, evalS_mem w⟩ : Pv) =
      Quiver.SchreierGraph.evalWord (fun h : Fin 7 => sgenP h) (ptoLetters 7 w) := by
  apply Subtype.ext
  rw [coe_evalWord_P]
  rfl

theorem mwords_size : Data.MWords.size = 3 := by decide

theorem mwords_ok : ∀ l < 3, plettersOK 7 Data.MWords[l]! = true := by
  intro l hl
  apply words_ok.2.1
  rw [getElem!_pos Data.MWords l (by rw [mwords_size]; exact hl)]
  exact Array.getElem_mem_toList _

theorem prep_hArrs : ∀ l < 3, PRep N hArrs[l]! (hP l : Equiv.Perm (Fin N)) := by
  intro l hl
  rw [hArrs, wordArrs, pwords_eq, getElem!_map' _ _ (by rw [mwords_size]; exact hl)]
  exact prep_wordArr (mwords_ok l hl)

theorem prep_vArrs :
    ∀ l < 3, PRep N vArrs[l]! (sigmaPv (hP l) : Equiv.Perm (Fin N)) := by
  intro l hl
  rw [vArrs, pwords_eq, getElem!_map' _ _ (by rw [mwords_size]; exact hl), hP, evalS_word,
    sigma_evalWord]
  exact prep_pword (gs := fun h => (sigmaPv (sgenP h) : Equiv.Perm (Fin N)))
    (fun h hh => (prep_sigStrong h hh).1) (fun h hh => (prep_sigStrong h hh).2) _ (mwords_ok l hl)

theorem prep_zArr : PRep N zArr (zP : Equiv.Perm (Fin N)) :=
  prep_wordArr words_ok.2.2.2.2.1

theorem hP_mem :
    ∀ l < 3, hP l ∈ Subgroup.centralizer ({zP} : Set Pv) := by
  intro l hl
  rw [CFSG.Sporadic.ONOddCore.mem_centralizer_zP_iff]
  apply Subgroup.subset_closure
  show evalS Data.MWords[l]! ∈ evalList Data.MWords
  refine List.mem_map.2 ⟨Data.MWords[l]!, ?_, rfl⟩
  rw [getElem!_pos Data.MWords l (by rw [mwords_size]; exact hl)]
  exact Array.getElem_mem_toList _

end Sigma

end CFSG.ComponentClassification.SolMax.ONOut
