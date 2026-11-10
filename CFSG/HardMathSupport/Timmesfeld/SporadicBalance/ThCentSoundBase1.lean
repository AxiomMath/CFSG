
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase

public import CFSG.Sporadic.Th.SimpleBase1

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open scoped Matrix Pointwise

theorem matTableOK_spec {st : BFSState} {t : Array V4} {T : Table} {n c : ℕ}
    (h : matTableOK st t T n c = true) :
    ∀ i < n, ap T i < n ∧ readKey st.keys (ap T i) = imageKey t (readKey st.keys i) := by
  intro i hi
  unfold matTableOK at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set b := n / (c + 1) + 1 with hb
  have hbpos : 0 < b := Nat.succ_pos _
  have hlt : i < b * (c + 1) := by
    rw [mul_comm]
    exact lt_trans hi (Nat.lt_mul_div_succ n (Nat.succ_pos c))
  have hj : i / b < c + 1 := (Nat.div_lt_iff_lt_mul hbpos).2 (by rw [mul_comm]; exact hlt)
  have hblk := h (i / b) hj
  change allIn (min n (i / b * b)) (min n ((i / b + 1) * b)) (fun i =>
    decide (ap T i < n) && (readKey st.keys (ap T i)).beq
      (imageKey (freshTable t) (readKey st.keys i))) = true at hblk
  have hlo : min n (i / b * b) ≤ i := (min_le_right _ _).trans (Nat.div_mul_le_self i b)
  have hhi : i < min n ((i / b + 1) * b) := by
    refine lt_min hi ?_
    have := Nat.lt_div_mul_add (a := i) hbpos
    rw [Nat.add_mul, one_mul]
    exact this
  have hp := allIn_eq_true.1 hblk i hlo hhi
  simp only [Bool.and_eq_true, decide_eq_true_eq, Key.beq_iff, freshTable_eq] at hp
  exact hp

abbrev matJ (g : J) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem matJ_mul (g h : J) : matJ (g * h) = matJ g * matJ h := by
  simp only [matJ, Subgroup.coe_mul, Units.val_mul]

theorem matJ_one : matJ 1 = 1 := by
  simp only [matJ, OneMemClass.coe_one, Units.val_one]

theorem matJ_pow (g : J) (e : ℕ) : matJ (g ^ e) = matJ g ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, matJ_one]
  | succ e ih => rw [pow_succ, pow_succ, matJ_mul, ih]

theorem rowsMatrix_foldl_mulRows (f : ℤ → Array V4) (gens : ℤ → J)
    (hf : ∀ l, rowsMatrix (f l) = matJ (gens l)) :
    ∀ (w : List ℤ) (acc : Array V4), rowsMatrix (w.foldl (fun acc l => mulRows acc (f l)) acc) =
      rowsMatrix acc * matJ (wordG gens w) := by
  intro w
  induction w with
  | nil => intro acc; simp [wordG, matJ_one]
  | cons l w ih =>
    intro acc
    rw [List.foldl_cons, ih, rowsMatrix_mulRows, hf, wordG_cons, matJ_mul, mul_assoc]

theorem rowsMatrix_wordRows {P Q : Array V4} {g h : J} (hP : rowsMatrix P = matJ g)
    (hQ : rowsMatrix Q = matJ h) (hg : g ^ 2 = 1) (hh : h ^ 3 = 1) (w : List ℤ) :
    rowsMatrix (wordRows P Q w) = matJ (wordG (pairLetters g h) w) := by
  have hg' : g⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hg]
  have hh' : h⁻¹ = h * h := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', hh]
  have hL : ∀ l : ℤ, rowsMatrix (if l = 1 ∨ l = -1 then P else if l = 2 then Q else
      mulRows Q Q) = matJ (pairLetters g h l) := by
    intro l
    unfold pairLetters
    by_cases h1 : l = 1
    · simp only [h1, true_or, ite_true, hP]
    · by_cases h2 : l = -1
      · simp only [h2, or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false, hP, hg']
      · by_cases h3 : l = 2
        · simp only [h3, show (2 : ℤ) ≠ 1 by decide, show (2 : ℤ) ≠ -1 by decide, or_self,
            ite_false, ite_true, hQ]
        · simp only [h1, h2, h3, or_self, ite_false, rowsMatrix_mulRows, hQ, hh', matJ_mul]
  have := rowsMatrix_foldl_mulRows (fun l => if l = 1 ∨ l = -1 then P else if l = 2 then Q else
    mulRows Q Q) (pairLetters g h) hL w idRows
  rw [rowsMatrix_idRows, one_mul] at this
  exact this

noncomputable def x1J : J := wordG (pairLetters a b) (abWord x1Str)

noncomputable def x2J : J := wordG (pairLetters a b) (abWord x2Str)

noncomputable def zJ : J := (x1J * x2J) ^ 9

theorem smul_val (g : J) (p : Fin nX) : (g • p).val = idx nX g p.val := (idx_val g p).symm

theorem rowsMatrix_seedB : rowsMatrix (rowsOf seedB) = matJ b := by
  rw [rowsMatrix_rowsOf_seedB, matJ, b_val]

section Facts

variable {c' : ℕ} (hC : CertFacts c')
include hC

theorem rep_of_matTableOK {M : Array V4} {g : J} (hM : rowsMatrix M = matJ g) {T : Table}
    {c : ℕ} (h : matTableOK thSt (frTable (transposeRows M)) T nX c = true) : Rep nX T g := by
  intro i hi
  obtain ⟨hlt, hkey⟩ := matTableOK_spec h i hi
  symm
  refine (idx_eq_iff hC.orbit hi hlt).2 ?_
  calc g • planeAt i = (fun v => matJ g *ᵥ v) '' planeAt i := smul_set_eq_image g _
    _ = (fun v => rowsMatrix M *ᵥ v) '' planeAt i := by rw [hM]
    _ = planeAt (ap T i) := by rw [planeAt, planeAt, hkey, keyPlane_imageKey]

theorem stripZ_spec {z : J} {zT xT yiT pl0 pos0 : Table} (hz : Rep nX zT z)
    (hxi : Rep nX xT xJ⁻¹) (hyi : Rep nX yiT yJ⁻¹) {p : ℕ} (hp : p < nX) :
    (stripZ zT gplT alphaT betaInvT pl0 pos0 xT yiT p).1 =
        ap pos0 (idx nX (treeElt gplT (lettersG a b) p)⁻¹ (idx nX z p)) ∧
      ∀ j < 3, (stripZ zT gplT alphaT betaInvT pl0 pos0 xT yiT p).2[j]! =
        idx nX ((treeElt pl0 (lettersG xJ yJ)
          (stripZ zT gplT alphaT betaInvT pl0 pos0 xT yiT p).1)⁻¹ *
          (treeElt gplT (lettersG a b) p)⁻¹) (idx nX (z ^ j) p) := by
  have hst : stripZ zT gplT alphaT betaInvT pl0 pos0 xT yiT p =
      (ap pos0 (applyTreeInv gplT (letters alphaT betaInvT) p
          #[p, ap zT p, ap zT (ap zT p)])[1]!,
        applyTreeInv pl0 (letters xT yiT)
          (ap pos0 (applyTreeInv gplT (letters alphaT betaInvT) p
            #[p, ap zT p, ap zT (ap zT p)])[1]!)
          (applyTreeInv gplT (letters alphaT betaInvT) p #[p, ap zT p, ap zT (ap zT p)])) := by
    simp only [stripZ, applyTreeInv2_eq]
  rw [hst]
  have hzp : ap zT p = idx nX z p := hz p hp
  have hzzp : ap zT (ap zT p) = idx nX (z ^ 2) p := by
    rw [hzp, hz _ (idx_lt z hp), pow_two, idx_mul]
  set q₀ : Array ℕ := #[p, ap zT p, ap zT (ap zT p)] with hq₀
  have hq₀s : q₀.size = 3 := rfl
  have hq₀j : ∀ j < 3, q₀[j]! = idx nX (z ^ j) p := by
    intro j hj
    obtain ⟨e0, e1, e2⟩ := triple_get p (ap zT p) (ap zT (ap zT p))
    interval_cases j
    · rw [e0, pow_zero, idx_one]
    · rw [e1, pow_one, hzp]
    · rw [e2, hzzp]
  have hq₀lt : ∀ j < q₀.size, q₀[j]! < nX := by
    intro j hj
    rw [hq₀s] at hj
    rw [hq₀j j hj]
    exact idx_lt _ hp
  obtain ⟨hs1, he1⟩ := applyTreeInv_spec (rep_ab_letters_inv hC) gplT p q₀ hq₀lt
  set q₁ := applyTreeInv gplT (letters alphaT betaInvT) p q₀ with hq₁
  have hq₁lt : ∀ j < q₁.size, q₁[j]! < nX := by
    intro j hj
    rw [hs1] at hj
    rw [he1 j hj]
    exact idx_lt _ (hq₀lt j hj)
  have hHinv : ∀ s, Rep nX (letters xT yiT s) (lettersG xJ yJ s)⁻¹ := rep_letters_inv hxi hyi
  have e1 : q₁[1]! = idx nX (treeElt gplT (lettersG a b) p)⁻¹ (idx nX z p) := by
    rw [he1 1 (by rw [hq₀s]; norm_num), hq₀j 1 (by norm_num), pow_one]
  refine ⟨?_, fun j hj => ?_⟩
  · show ap pos0 q₁[1]! = _
    rw [e1]
  · obtain ⟨hs2, he2⟩ := applyTreeInv_spec hHinv pl0 (ap pos0 q₁[1]!) q₁ hq₁lt
    show (applyTreeInv pl0 (letters xT yiT) (ap pos0 q₁[1]!) q₁)[j]! = _
    have hj' : j < q₁.size := by rw [hs1, hq₀s]; exact hj
    rw [he2 j hj', he1 j (by rw [hq₀s]; exact hj), hq₀j j hj, idx_mul]

end Facts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
