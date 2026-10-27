module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSpinCheck
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound.Spin

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

variable {d : ℕ}

theorem rowsMatrix_addRows (X Y : Array ℕ) :
    rowsMatrix d (addRows d X Y) = rowsMatrix d X + rowsMatrix d Y := by
  ext i j
  rw [Matrix.add_apply, rowsMatrix_apply, rowsMatrix_apply, rowsMatrix_apply]
  unfold addRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply]

theorem rowsMatrix_zeroRows : rowsMatrix d (zeroRows d) = 0 := by
  ext i j
  rw [rowsMatrix_apply]
  unfold zeroRows
  simp [toVecD_zero]

theorem cact_spec (X : Array ℕ) (v : ℕ) :
    rowsMatrix d X *ᵥ toVecD d v = toVecD d (cact d X v) :=
  rowsMatrix_mulVec d X v

section Comm

variable {g : Matrix (Fin d) (Fin d) (ZMod 2)}

theorem commute_id : g * rowsMatrix d (idRows d) = rowsMatrix d (idRows d) * g := by
  rw [rowsMatrix_idRows, Matrix.mul_one, Matrix.one_mul]

theorem commute_mulRows {X Y : Array ℕ} (hX : g * rowsMatrix d X = rowsMatrix d X * g)
    (hY : g * rowsMatrix d Y = rowsMatrix d Y * g) :
    g * rowsMatrix d (mulRows d X Y) = rowsMatrix d (mulRows d X Y) * g := by
  rw [rowsMatrix_mulRows]
  calc g * (rowsMatrix d X * rowsMatrix d Y) = (g * rowsMatrix d X) * rowsMatrix d Y := by
        rw [Matrix.mul_assoc]
    _ = rowsMatrix d X * (g * rowsMatrix d Y) := by rw [hX, Matrix.mul_assoc]
    _ = rowsMatrix d X * (rowsMatrix d Y * g) := by rw [hY]
    _ = rowsMatrix d X * rowsMatrix d Y * g := by rw [Matrix.mul_assoc]

theorem commute_addRows {X Y : Array ℕ} (hX : g * rowsMatrix d X = rowsMatrix d X * g)
    (hY : g * rowsMatrix d Y = rowsMatrix d Y * g) :
    g * rowsMatrix d (addRows d X Y) = rowsMatrix d (addRows d X Y) * g := by
  rw [rowsMatrix_addRows, Matrix.mul_add, Matrix.add_mul, hX, hY]

theorem commute_zeroRows : g * rowsMatrix d (zeroRows d) = rowsMatrix d (zeroRows d) * g := by
  rw [rowsMatrix_zeroRows, Matrix.mul_zero, Matrix.zero_mul]

variable {rs is : List (Array ℕ)}

theorem commute_letterRows
    (hr : ∀ k, g * rowsMatrix d (rs.getD k (idRows d)) = rowsMatrix d (rs.getD k (idRows d)) * g)
    (hi : ∀ k, g * rowsMatrix d (is.getD k (idRows d)) = rowsMatrix d (is.getD k (idRows d)) * g)
    (j : ℤ) :
    g * rowsMatrix d (letterRows d rs is j) = rowsMatrix d (letterRows d rs is j) * g := by
  unfold letterRows
  split_ifs
  · exact hr _
  · exact hi _

theorem commute_wordRows
    (hr : ∀ k, g * rowsMatrix d (rs.getD k (idRows d)) = rowsMatrix d (rs.getD k (idRows d)) * g)
    (hi : ∀ k, g * rowsMatrix d (is.getD k (idRows d)) = rowsMatrix d (is.getD k (idRows d)) * g)
    (w : List ℤ) :
    g * rowsMatrix d (wordRows d rs is w) = rowsMatrix d (wordRows d rs is w) * g := by
  unfold wordRows
  suffices ∀ acc, g * rowsMatrix d acc = rowsMatrix d acc * g →
      g * rowsMatrix d (w.foldl (fun acc j => mulRows d acc (letterRows d rs is j)) acc) =
        rowsMatrix d (w.foldl (fun acc j => mulRows d acc (letterRows d rs is j)) acc) * g from
    this _ commute_id
  induction w with
  | nil => intro acc h; exact h
  | cons j w ih =>
    intro acc h
    exact ih _ (commute_mulRows h (commute_letterRows hr hi j))

theorem commute_foldl_add (c : ℕ) (A : List (Array ℕ))
    (hA : ∀ k, g * rowsMatrix d (A.getD k (zeroRows d)) = rowsMatrix d (A.getD k (zeroRows d)) * g)
    (L : List ℕ) :
    ∀ acc, g * rowsMatrix d acc = rowsMatrix d acc * g →
      g * rowsMatrix d (L.foldl (fun acc k =>
        if c.testBit k then addRows d acc (A.getD k (zeroRows d)) else acc) acc) =
      rowsMatrix d (L.foldl (fun acc k =>
        if c.testBit k then addRows d acc (A.getD k (zeroRows d)) else acc) acc) * g := by
  induction L with
  | nil => intro acc h; exact h
  | cons k L ih =>
    intro acc h
    rw [List.foldl_cons]
    refine ih _ ?_
    split_ifs
    · exact commute_addRows h (hA k)
    · exact h

theorem commute_annW {C : Array ℕ} {A : List (Array ℕ)} {b : List ℕ} {j i : ℕ}
    (hs : g * rowsMatrix d (rs.getD j (idRows d)) = rowsMatrix d (rs.getD j (idRows d)) * g)
    (hA : ∀ k, g * rowsMatrix d (A.getD k (zeroRows d)) =
      rowsMatrix d (A.getD k (zeroRows d)) * g) :
    g * rowsMatrix d (annW d rs C A b j i) = rowsMatrix d (annW d rs C A b j i) * g := by
  unfold annW
  dsimp only
  exact commute_addRows (commute_foldl_add _ A hA _ _ commute_zeroRows)
    (commute_mulRows hs (hA i))

end Comm

theorem eq_of_mulVec_rows {C B g G : Matrix (Fin d) (Fin d) (ZMod 2)} (hCB : C * B = 1)
    (h : ∀ i, g *ᵥ (B i) = G *ᵥ (B i)) : g = G := by
  have h1 : g * Bᵀ = G * Bᵀ := by
    ext i j
    have := congrFun (h j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using this
  have h2 : Bᵀ * Cᵀ = 1 := by
    rw [← Matrix.transpose_mul, hCB, Matrix.transpose_one]
  calc g = g * (Bᵀ * Cᵀ) := by rw [h2, Matrix.mul_one]
    _ = (g * Bᵀ) * Cᵀ := by rw [Matrix.mul_assoc]
    _ = (G * Bᵀ) * Cᵀ := by rw [h1]
    _ = G * (Bᵀ * Cᵀ) := by rw [Matrix.mul_assoc]
    _ = G := by rw [h2, Matrix.mul_one]

theorem spin_unpack (D : SpinData) (h : spinOK D = true) :
    D.rs.length = D.is.length ∧
    (∀ j < D.rs.length, mulRows D.d (D.rs.getD j #[]) (D.is.getD j #[]) = idRows D.d) ∧
    D.bw.length = D.d ∧ D.b.length = D.d ∧ D.C.size = D.d ∧
    mulRows D.d D.C D.b.toArray = idRows D.d ∧
    D.sel.length = D.d ∧
    (∀ t ∈ D.sel, cact D.d (annW D.d D.rs D.C D.A D.b t.1 t.2.1) D.v0 = 0) ∧
    D.wcols.length ≤ D.d ∧
    addRows D.d (idRows D.d) (mulRows D.d D.Wp D.Pp) = mulRows D.d D.lam D.esel ∧
    (∀ x < 2 ^ D.wcols.length, ∀ i < D.d,
      vecMulN D.d (transposeRows D.d (D.mx x)) (D.b.getD i 0) =
        vecMulN D.d ((D.A.map (transposeRows D.d)).getD i #[]) (D.wx x)) := by
  unfold spinOK at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩ := h
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩


theorem size_addRows (X Y : Array ℕ) : (addRows d X Y).size = d := by
  unfold addRows; simp


theorem mulVec_rowsMatrix_apply (X : Array ℕ) (v : Fin d → ZMod 2) (k : Fin d) :
    (rowsMatrix d X *ᵥ v) k = dotProduct (toVecD d (X[k.val]?.getD 0)) v := rfl

theorem annW_size (rs : List (Array ℕ)) (C : Array ℕ) (A : List (Array ℕ)) (b : List ℕ)
    (j i : ℕ) : (annW d rs C A b j i).size = d := by
  unfold annW
  dsimp only
  exact size_addRows _ _

theorem getD_eq_of_lt {α : Type*} (l : List α) {k : ℕ} (hk : k < l.length) (a b : α) :
    l.getD k a = l.getD k b := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_eq_default {α : Type*} (l : List α) {k : ℕ} (hk : ¬ k < l.length) (a : α) :
    l.getD k a = a := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hk)]

theorem spin_sound (D : SpinData) (h : spinOK D = true) {g : Matrix (Fin D.d) (Fin D.d) (ZMod 2)}
    (hg : ∀ k < D.rs.length,
      g * rowsMatrix D.d (D.rs.getD k #[]) = rowsMatrix D.d (D.rs.getD k #[]) * g) :
    ∃ x < 2 ^ D.wcols.length, g = rowsMatrix D.d (D.mx x) := by
  classical
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := spin_unpack D h
  have hr : ∀ k, g * rowsMatrix D.d (D.rs.getD k (idRows D.d)) =
      rowsMatrix D.d (D.rs.getD k (idRows D.d)) * g := by
    intro k
    by_cases hk : k < D.rs.length
    · rw [getD_eq_of_lt D.rs hk _ #[]]
      exact hg k hk
    · rw [getD_eq_default D.rs hk]
      exact commute_id
  have hi : ∀ k, g * rowsMatrix D.d (D.is.getD k (idRows D.d)) =
      rowsMatrix D.d (D.is.getD k (idRows D.d)) * g := by
    intro k
    by_cases hk : k < D.rs.length
    · have hk' : k < D.is.length := c1 ▸ hk
      rw [getD_eq_of_lt D.is hk' _ #[]]
      have hRI : rowsMatrix D.d (D.rs.getD k #[]) * rowsMatrix D.d (D.is.getD k #[]) = 1 := by
        rw [← rowsMatrix_mulRows, c2 k hk, rowsMatrix_idRows]
      have hIR := mul_eq_one_comm.1 hRI
      have h1 := hg k hk
      calc g * rowsMatrix D.d (D.is.getD k #[])
          = (rowsMatrix D.d (D.is.getD k #[]) * rowsMatrix D.d (D.rs.getD k #[])) *
              (g * rowsMatrix D.d (D.is.getD k #[])) := by rw [hIR, Matrix.one_mul]
        _ = rowsMatrix D.d (D.is.getD k #[]) * ((rowsMatrix D.d (D.rs.getD k #[]) * g) *
              rowsMatrix D.d (D.is.getD k #[])) := by simp only [Matrix.mul_assoc]
        _ = rowsMatrix D.d (D.is.getD k #[]) * ((g * rowsMatrix D.d (D.rs.getD k #[])) *
              rowsMatrix D.d (D.is.getD k #[])) := by rw [← h1]
        _ = rowsMatrix D.d (D.is.getD k #[]) * g *
              (rowsMatrix D.d (D.rs.getD k #[]) * rowsMatrix D.d (D.is.getD k #[])) := by
          simp only [Matrix.mul_assoc]
        _ = rowsMatrix D.d (D.is.getD k #[]) * g := by rw [hRI, Matrix.mul_one]
    · have hk' : ¬ k < D.is.length := fun h' => hk (c1 ▸ h')
      rw [getD_eq_default D.is hk']
      exact commute_id
  have hA : ∀ k, g * rowsMatrix D.d (D.A.getD k (zeroRows D.d)) =
      rowsMatrix D.d (D.A.getD k (zeroRows D.d)) * g := by
    intro k
    unfold SpinData.A
    by_cases hk : k < D.bw.length
    · have : (D.bw.map (wordRows D.d D.rs D.is)).getD k (zeroRows D.d) =
          wordRows D.d D.rs D.is D.bw[k] := by
        simp [List.getD_eq_getElem?_getD, hk]
      rw [this]
      exact commute_wordRows hr hi _
    · have : (D.bw.map (wordRows D.d D.rs D.is)).getD k (zeroRows D.d) = zeroRows D.d := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.1 hk)]
      rw [this]
      exact commute_zeroRows
  have hann : ∀ j i, g * rowsMatrix D.d (annW D.d D.rs D.C D.A D.b j i) =
      rowsMatrix D.d (annW D.d D.rs D.C D.A D.b j i) * g := fun j i =>
    commute_annW (hr j) hA
  set v0v : Fin D.d → ZMod 2 := toVecD D.d D.v0 with hv0
  set wv : Fin D.d → ZMod 2 := g *ᵥ v0v with hwv
  have hN : ∀ t ∈ D.sel, rowsMatrix D.d (annW D.d D.rs D.C D.A D.b t.1 t.2.1) *ᵥ wv = 0 := by
    intro t ht
    have hz : rowsMatrix D.d (annW D.d D.rs D.C D.A D.b t.1 t.2.1) *ᵥ v0v = 0 := by
      rw [hv0, cact_spec, c8 t ht, toVecD_zero]
    rw [hwv, Matrix.mulVec_mulVec, ← hann, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  have hE : rowsMatrix D.d D.esel *ᵥ wv = 0 := by
    funext k
    have hk : k.val < D.sel.length := by rw [c7]; exact k.2
    have htmem : D.sel[k.val] ∈ D.sel := List.getElem_mem hk
    have hesel : D.esel[k.val]?.getD 0 =
        ((annW D.d D.rs D.C D.A D.b (D.sel[k.val]).1 (D.sel[k.val]).2.1)[(D.sel[k.val]).2.2]?.getD
          0) := by
      unfold SpinData.esel eselW
      simp [hk]
    rw [Pi.zero_apply, mulVec_rowsMatrix_apply, hesel]
    set t := D.sel[k.val] with ht
    by_cases hρ : t.2.2 < D.d
    · have := congrFun (hN t htmem) ⟨t.2.2, hρ⟩
      rw [mulVec_rowsMatrix_apply] at this
      simpa using this
    · have hnone : (annW D.d D.rs D.C D.A D.b t.1 t.2.1)[t.2.2]? = none := by
        apply Array.getElem?_eq_none
        rw [annW_size]
        omega
      rw [hnone]
      simp [toVecD_zero]
  have hM10 : (1 : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) +
      rowsMatrix D.d D.Wp * rowsMatrix D.d D.Pp =
      rowsMatrix D.d D.lam * rowsMatrix D.d D.esel := by
    have := congrArg (rowsMatrix D.d) c10
    rwa [rowsMatrix_addRows, rowsMatrix_idRows, rowsMatrix_mulRows, rowsMatrix_mulRows] at this
  have hQ : wv = (rowsMatrix D.d D.Wp * rowsMatrix D.d D.Pp) *ᵥ wv := by
    have h0 : ((1 : Matrix (Fin D.d) (Fin D.d) (ZMod 2)) +
        rowsMatrix D.d D.Wp * rowsMatrix D.d D.Pp) *ᵥ wv = 0 := by
      rw [hM10, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_zero]
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at h0
    funext i
    have := congrFun h0 i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    exact CharTwo.add_eq_zero.1 this
  set xv : Fin D.d → ZMod 2 := rowsMatrix D.d D.Pp *ᵥ wv with hxv
  have hwx : wv = rowsMatrix D.d D.Wp *ᵥ xv := by
    rw [hxv, Matrix.mulVec_mulVec]
    exact hQ
  have hxz : ∀ j : Fin D.d, ¬ j.val < D.wcols.length → xv j = 0 := by
    intro j hj
    rw [hxv, mulVec_rowsMatrix_apply]
    have : D.Pp[j.val]?.getD 0 = 0 := by
      unfold SpinData.Pp
      simp [j.isLt, hj]
    rw [this, toVecD_zero]
    simp
  let f : ℕ → Bool := fun k => if hk : k < D.d then decide (xv ⟨k, hk⟩ = 1) else false
  let x := ofBits D.wcols.length f
  have hxlt : x < 2 ^ D.wcols.length := ofBits_lt _ _
  have hxvec : toVecD D.d x = xv := by
    funext j
    rw [toVecD_apply, ofBits_testBit]
    by_cases hjm : j.val < D.wcols.length
    · simp only [hjm, decide_true, Bool.true_and, f, j.isLt, dite_true]
      generalize xv j = a
      fin_cases a <;> rfl
    · rw [hxz j hjm]
      simp [hjm]
  have hwvec : wv = toVecD D.d (D.wx x) := by
    rw [hwx, ← hxvec]
    unfold SpinData.Wp SpinData.wx
    rw [rowsMatrix_transposeRows, Matrix.mulVec_transpose, ← toVecD_vecMulN]
  refine ⟨x, hxlt, ?_⟩
  have hCB : rowsMatrix D.d D.C * rowsMatrix D.d D.b.toArray = 1 := by
    rw [← rowsMatrix_mulRows, c6, rowsMatrix_idRows]
  refine eq_of_mulVec_rows hCB (fun i => ?_)
  have hAlen : D.A.length = D.d := by
    unfold SpinData.A
    rw [List.length_map, c3]
  have hbi : rowsMatrix D.d D.b.toArray i = toVecD D.d (D.b.getD i.val 0) := by
    funext j
    rw [rowsMatrix_apply]
    simp [List.getD_eq_getElem?_getD]
  have hbA : D.b.getD i.val 0 = cact D.d (D.A.getD i.val #[]) D.v0 := by
    unfold SpinData.b
    have hi' : i.val < D.A.length := by rw [hAlen]; exact i.2
    simp [List.getD_eq_getElem?_getD, hi']
  rw [hbi, hbA]
  have hleft : g *ᵥ toVecD D.d (cact D.d (D.A.getD i.val #[]) D.v0) =
      toVecD D.d (cact D.d (D.A.getD i.val #[]) (D.wx x)) := by
    rw [← cact_spec, ← hv0, Matrix.mulVec_mulVec]
    have := hA i.val
    rw [getD_eq_of_lt D.A (by rw [hAlen]; exact i.2) (zeroRows D.d) #[]] at this
    rw [this, ← Matrix.mulVec_mulVec, ← hwv, hwvec, cact_spec]
  have hright : rowsMatrix D.d (D.mx x) *ᵥ toVecD D.d (cact D.d (D.A.getD i.val #[]) D.v0) =
      toVecD D.d (cact D.d (D.A.getD i.val #[]) (D.wx x)) := by
    rw [← hbA, cact_spec]
    have h11 := c11 x hxlt i.val i.2
    have hi' : i.val < D.A.length := by rw [hAlen]; exact i.2
    have hmap : (D.A.map (transposeRows D.d)).getD i.val #[] =
        transposeRows D.d (D.A.getD i.val #[]) := by
      simp [List.getD_eq_getElem?_getD, hi']
    rw [hmap] at h11
    exact congrArg (toVecD D.d) h11
  rw [hleft, hright]

theorem spin_sound' (D : SpinData) (h : spinOK D = true) {n : ℕ} (hn : D.d = n)
    {g : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hg : ∀ k < D.rs.length,
      g * rowsMatrix n (D.rs.getD k #[]) = rowsMatrix n (D.rs.getD k #[]) * g) :
    ∃ x < 2 ^ D.wcols.length, g = rowsMatrix n (D.mx x) := by
  subst hn
  exact spin_sound D h hg

theorem vecMulN_lt (R : Array ℕ) (hR : ∀ x ∈ R, x < 2 ^ d) (v : ℕ) :
    vecMulN d R v < 2 ^ d := by
  unfold vecMulN
  suffices ∀ (L : List ℕ) (acc : ℕ), acc < 2 ^ d →
      L.foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc) acc < 2 ^ d from
    this _ 0 (by positivity)
  intro L
  induction L with
  | nil => intro acc h; exact h
  | cons j L ih =>
    intro acc h
    rw [List.foldl_cons]
    refine ih _ ?_
    split_ifs
    · refine Nat.xor_lt_two_pow h ?_
      cases hj : R[j]? with
      | none => simp
      | some r => exact hR r (Array.mem_of_getElem? hj)
    · exact h


theorem validR_size {R : Array ℕ} (h : validR d R = true) : R.size = d := by
  unfold validR at h
  exact beq_iff_eq.1 (Eq.mp (Bool.and_eq_true _ _) h).1

theorem validR_lt {R : Array ℕ} (h : validR d R = true) : ∀ x ∈ R, x < 2 ^ d := by
  unfold validR at h
  intro x hx
  have := (Eq.mp (Bool.and_eq_true _ _) h).2
  exact of_decide_eq_true (Array.all_eq_true_iff_forall_mem.1 this x hx)

theorem validR_of {R : Array ℕ} (hs : R.size = d) (hl : ∀ x ∈ R, x < 2 ^ d) :
    validR d R = true := by
  unfold validR
  rw [Bool.and_eq_true]
  exact ⟨beq_iff_eq.2 hs, Array.all_eq_true_iff_forall_mem.2 fun x hx => decide_eq_true (hl x hx)⟩

theorem validR_idRows : validR d (idRows d) = true := by
  refine validR_of (by simp [idRows]) ?_
  intro x hx
  unfold idRows at hx
  obtain ⟨i, rfl⟩ := Array.mem_ofFn.1 hx
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) i.2

theorem validR_mulRows {X Y : Array ℕ} (hX : validR d X = true) (hY : validR d Y = true) :
    validR d (mulRows d X Y) = true := by
  refine validR_of (by simp [mulRows, validR_size hX]) ?_
  intro x hx
  unfold mulRows at hx
  obtain ⟨v, -, rfl⟩ := Array.mem_map.1 hx
  exact vecMulN_lt Y (validR_lt hY) v

theorem rowsMatrix_inj_of_valid {X Y : Array ℕ} (hX : validR d X = true) (hY : validR d Y = true)
    (h : rowsMatrix d X = rowsMatrix d Y) : X = Y := by
  have hxs := validR_size hX
  have hys := validR_size hY
  apply Array.ext (by rw [hxs, hys])
  intro i hix hiy
  have hi : i < d := hxs ▸ hix
  have hrow : toVecD d (X[i]?.getD 0) = toVecD d (Y[i]?.getD 0) := by
    funext j
    exact congrFun (congrFun h ⟨i, hi⟩) j
  have hxi : X[i]?.getD 0 = X[i] := by simp [hix]
  have hyi : Y[i]?.getD 0 = Y[i] := by simp [hiy]
  rw [hxi, hyi] at hrow
  exact toVecD_injective (validR_lt hX _ (Array.getElem_mem hix))
    (validR_lt hY _ (Array.getElem_mem hiy)) hrow

end CFSG.EvenSporadicStandard.Induction.AutBound.Spin
