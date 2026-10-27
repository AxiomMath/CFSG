
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CoreByList
public import CFSG.Sporadic.ThSchreier.AutAssembly

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent

theorem matJ_injective : Function.Injective matJ := fun g h hgh =>
  Subtype.ext (Units.ext hgh)

theorem card_centralizer_conj_eq (g s : J) :
    Nat.card (Subgroup.centralizer ({g * s * g⁻¹} : Set J)) =
      Nat.card (Subgroup.centralizer ({s} : Set J)) := by
  rw [← CFSG.Sporadic.ThSchreier.centralizer_map_conj g s]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem eq_of_rowsMatrix_eq {X Y : Array V4} {g h : J} (hX : rowsMatrix X = matJ g)
    (hY : rowsMatrix Y = matJ h) (e : eqRows X Y = true) : g = h :=
  matJ_injective (by rw [← hX, ← hY, eqRows_iff.1 e])

theorem ne_of_rowsDiffer {X Y : Array V4} {g h : J} (hX : rowsMatrix X = matJ g)
    (hY : rowsMatrix Y = matJ h) (e : rowsDiffer X Y = true) : g ≠ h := by
  rintro rfl
  exact rowsMatrix_ne_of_rowsDiffer e (hX.trans hY.symm)

@[expose] noncomputable def opJ (R : ℕ → J) : Op → ℕ → J
  | .mul i j k => Function.update R k (R i * R j)
  | .pow e i k => Function.update R k (R i ^ e)

@[expose] noncomputable def initJ (g h : J) : ℕ → J := fun r =>
  if r = 0 then g else if r = 1 then h else 1

@[expose] noncomputable def slpJ (g h : J) (prog : List Op) : ℕ → J :=
  prog.foldl opJ (initJ g h)

theorem rowsMatrix_slpRows {A B : Array V4} {g h : J} (hA : rowsMatrix A = matJ g)
    (hB : rowsMatrix B = matJ h) {n : ℕ} {prog : List Op} (hprog : prog.all (Op.lt n) = true) :
    (slpRows A B n prog).size = n ∧
      ∀ r < n, rowsMatrix (slpRows A B n prog)[r]! = matJ (slpJ g h prog r) := by
  suffices H : ∀ (prog : List Op), prog.all (Op.lt n) = true →
      ∀ (R : Array (Array V4)) (RJ : ℕ → J), R.size = n →
        (∀ r < n, rowsMatrix R[r]! = matJ (RJ r)) →
        (prog.foldl opRows R).size = n ∧
          ∀ r < n, rowsMatrix (prog.foldl opRows R)[r]! = matJ (prog.foldl opJ RJ r) by
    refine H prog hprog _ _ (by simp [initRows]) fun r hr => ?_
    rw [initRows, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    simp only [initJ]
    split_ifs
    · exact hA
    · exact hB
    · rw [matJ_one]; exact rowsMatrix_idRows
  intro prog
  induction prog with
  | nil => intro _ R RJ hs hR; exact ⟨hs, hR⟩
  | cons op prog ih =>
    intro hp R RJ hs hR
    simp only [List.all_cons, Bool.and_eq_true] at hp
    refine ih hp.2 _ _ (by rw [opRows_size, hs]) fun r hr => ?_
    have hr' : r < R.size := hs ▸ hr
    cases op with
    | mul i j k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨⟨hi, hj⟩, -⟩ := hp1
      simp only [opRows, opJ]
      rw [getElem!_setIfInBounds_of_lt hr']
      by_cases hkr : k = r
      · subst hkr
        rw [if_pos rfl, Function.update_self, rowsMatrix_mulRows, hR i hi, hR j hj, matJ_mul]
      · rw [if_neg hkr, Function.update_of_ne (Ne.symm hkr), hR r hr]
    | pow e i k =>
      have hp1 := hp.1
      simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp1
      obtain ⟨hi, -⟩ := hp1
      simp only [opRows, opJ]
      rw [getElem!_setIfInBounds_of_lt hr']
      by_cases hkr : k = r
      · subst hkr
        rw [if_pos rfl, Function.update_self, rowsMatrix_powRowsN, hR i hi, matJ_pow]
      · rw [if_neg hkr, Function.update_of_ne (Ne.symm hkr), hR r hr]

theorem rowsMatrix_wordRowsL {gs : Array (Array V4)} {R : ℕ → J} {w : List ℕ}
    (h : ∀ r ∈ w, rowsMatrix gs[r]! = matJ (R r)) :
    rowsMatrix (wordRowsL gs w) = matJ (w.map R).prod := by
  suffices H : ∀ (w : List ℕ), (∀ r ∈ w, rowsMatrix gs[r]! = matJ (R r)) →
      ∀ acc : Array V4, rowsMatrix (w.foldl (fun acc r => mulRows acc gs[r]!) acc) =
        rowsMatrix acc * matJ (w.map R).prod by
    rw [wordRowsL, H w h, rowsMatrix_idRows, one_mul]
  intro w
  induction w with
  | nil => intro _ acc; simp [matJ_one]
  | cons r w ih =>
    intro hw acc
    rw [List.foldl_cons, ih (fun y hy => hw y (List.mem_cons_of_mem _ hy)), rowsMatrix_mulRows,
      hw r List.mem_cons_self, mul_assoc, ← matJ_mul]
    simp

theorem pairOK_spec {X Y : Array V4} {x y : J} (hX : rowsMatrix X = matJ x)
    (hY : rowsMatrix Y = matJ y) {p : ℕ} (h : pairOK X Y p = true) :
    x ^ p = 1 ∧ y ^ p = 1 ∧ matJ x * matJ y = matJ y * matJ x ∧ x ≠ 1 ∧ ∀ k < p, y ≠ x ^ k := by
  unfold pairOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hone : rowsMatrix idRows = matJ 1 := by rw [rowsMatrix_idRows, matJ_one]
  refine ⟨eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hX, matJ_pow]) hone h1,
    eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hY, matJ_pow]) hone h2, ?_,
    ne_of_rowsDiffer hX hone h4, fun k hk => ?_⟩
  · rw [← hX, ← hY, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h3]
  · exact ne_of_rowsDiffer hY (by rw [rowsMatrix_powRowsN, hX, matJ_pow]) (h5 k hk)

theorem conjOK_spec {regs : Array (Array V4)} {R : ℕ → J}
    (hR : ∀ r < regs.size, rowsMatrix regs[r]! = matJ (R r)) {X Y Z : Array V4} {x y z : J}
    (hX : rowsMatrix X = matJ x) (hY : rowsMatrix Y = matJ y) (hZ : rowsMatrix Z = matJ z)
    {p : ℕ} {W : Array (List ℕ)} (h : conjOK regs X Y Z p W = true) {a b : ℕ} (ha : a < p)
    (hb : b < p) (hab : a + b ≠ 0) :
    ∃ m : J, matJ m * (matJ x ^ a * matJ y ^ b) = matJ z * matJ m := by
  unfold conjOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h a ha b hb with h0 | ⟨hw, hc⟩
  · exact absurd h0 hab
  have hm := rowsMatrix_wordRowsL (R := R) fun r hr => hR r (hw r hr)
  refine ⟨((W[p * a + b]!).map R).prod, ?_⟩
  have := rowsMatrix_eq_of_eqRows hc
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRowsN, rowsMatrix_powRowsN, hm, hX,
    hY, rowsMatrix_mulRows, hZ, hm] at this
  exact this

theorem cubeOK_spec {X Y C : Array V4} {x y c : J} (hX : rowsMatrix X = matJ x)
    (hY : rowsMatrix Y = matJ y) (hC : rowsMatrix C = matJ c) {p row : ℕ} (hrow : row < 248)
    (h : cubeOK X Y C p row = true) :
    x ^ p = 1 ∧ y ^ p = 1 ∧ matJ c * matJ x = matJ x * matJ c ∧
      matJ c * matJ y = matJ y * matJ c ∧
      ∀ i j k i' j' k' : ℕ, i < p → j < p → k < p → i' < p → j' < p → k' < p →
        matJ x ^ i * matJ y ^ j * matJ c ^ k = matJ x ^ i' * matJ y ^ j' * matJ c ^ k' →
          i = i' ∧ j = j' ∧ k = k' := by
  unfold cubeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hone : rowsMatrix idRows = matJ 1 := by rw [rowsMatrix_idRows, matJ_one]
  refine ⟨eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hX, matJ_pow]) hone h1,
    eq_of_rowsMatrix_eq (by rw [rowsMatrix_powRowsN, hY, matJ_pow]) hone h2, ?_, ?_, ?_⟩
  · rw [← hX, ← hC, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h3]
  · rw [← hY, ← hC, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h4]
  · intro i j k i' j' k' hi hj hk hi' hj' hk' heq
    have hM : ∀ a b d : ℕ, rowsMatrix (mulRows (mulRows (powRowsN X a) (powRowsN Y b))
        (powRowsN C d)) = matJ x ^ a * matJ y ^ b * matJ c ^ d := fun a b d => by
      rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRowsN, rowsMatrix_powRowsN,
        rowsMatrix_powRowsN, hX, hY, hC]
    obtain ⟨hwf, hne⟩ := h5 i hi j hj k hk
    rcases hne i' hi' j' hj' k' hk' with ⟨⟨h6, h7⟩, h8⟩ | h6
    · exact ⟨h6, h7, h8⟩
    · exfalso
      have hwf' := (h5 i' hi' j' hj' k' hk').1
      rw [cubeRows_get hi hj hk] at hwf h6
      rw [cubeRows_get hi' hj' hk'] at hwf' h6
      exact rowsMatrix_ne_of_row hrow hwf hwf' h6 (by rw [hM, hM, heq])

theorem conj3OK_spec {regs : Array (Array V4)} {R : ℕ → J}
    (hR : ∀ r < regs.size, rowsMatrix regs[r]! = matJ (R r)) {X Y C : Array V4} {x y c : J}
    (hX : rowsMatrix X = matJ x) (hY : rowsMatrix Y = matJ y) (hC : rowsMatrix C = matJ c)
    {p : ℕ} {W : Array (List ℕ)} (h : conj3OK regs X Y C p W = true) {i j k : ℕ} (hi : i < p)
    (hj : j < p) (hk : k < p) (hijk : i + j + k ≠ 0) :
    ∃ m : J, matJ m * (matJ x ^ i * matJ y ^ j * matJ c ^ k) = matJ c * matJ m := by
  unfold conj3OK at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h i hi j hj k hk with h0 | ⟨hw, hc⟩
  · exact absurd h0 hijk
  have hm := rowsMatrix_wordRowsL (R := R) fun r hr => hR r (hw r hr)
  refine ⟨((W[p * p * i + p * j + k]!).map R).prod, ?_⟩
  have := rowsMatrix_eq_of_eqRows hc
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRowsN,
    rowsMatrix_powRowsN, rowsMatrix_powRowsN, hm, hX, hY, hC, rowsMatrix_mulRows, hC, hm] at this
  exact this

theorem rowsMatrix_witProd {E : Array (Array V4)} {inv : Array ℕ} {f : ℕ → J} {i : ℕ}
    {l : List ℕ} (hE : ∀ j ∈ i :: l, rowsMatrix E[j]! = matJ (f j))
    (hinv : ∀ j ∈ l, rowsMatrix E[inv[j]!]! = matJ (f j)⁻¹) :
    rowsMatrix (witProd E inv i l) = matJ (f i * (l.map fun j => f j * f i * (f j)⁻¹).prod) := by
  have hi := hE i List.mem_cons_self
  suffices H : ∀ (l : List ℕ), (∀ j ∈ l, rowsMatrix E[j]! = matJ (f j)) →
      (∀ j ∈ l, rowsMatrix E[inv[j]!]! = matJ (f j)⁻¹) → ∀ (P : Array V4) (g : J),
      rowsMatrix P = matJ g →
      rowsMatrix (l.foldl (fun P j => mulRows P (mulRows (mulRows E[j]! E[i]!) E[inv[j]!]!)) P) =
        matJ (g * (l.map fun j => f j * f i * (f j)⁻¹).prod) by
    exact H l (fun j hj => hE j (List.mem_cons_of_mem _ hj)) hinv _ _ hi
  intro l
  induction l with
  | nil => intro _ _ P g hP; simpa using hP
  | cons j l ih =>
    intro hEl hinvl P g hP
    rw [List.foldl_cons]
    refine (ih (fun j' hj' => hEl j' (List.mem_cons_of_mem _ hj'))
      (fun j' hj' => hinvl j' (List.mem_cons_of_mem _ hj')) _ (g * (f j * f i * (f j)⁻¹))
      ?_).trans ?_
    · rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, hP,
        hEl j List.mem_cons_self, hi, hinvl j List.mem_cons_self, matJ_mul, matJ_mul, matJ_mul]
    · simp [mul_assoc]

theorem gLAPPrimeCoreOf_eq_bot_of_coreListOK {regs : Array (Array V4)} {R : ℕ → J}
    (hR : ∀ r < regs.size, rowsMatrix regs[r]! = matJ (R r)) {Z : Array V4} {z : J}
    (hZ : rowsMatrix Z = matJ z) {D : CoreList} (h : coreListOK regs Z D = true)
    (hrow : D.row < 248) {p k : ℕ} (hp : p.Prime) (hn : D.n = p ^ k * D.m)
    (hcard : Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ D.n) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({z} : Set J)) = ⊥ := by
  unfold coreListOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hws, his⟩, hwis⟩, hlet⟩, hwit⟩, hinvlt⟩, hcomm⟩, hwf⟩, hdist⟩, hinv⟩,
    hwit'⟩ := h
  set E := D.words.map (wordRowsL regs) with hEdef
  set f : ℕ → J := fun i => (D.words[i]!.map R).prod with hf
  have hEsize : E.size = D.n := by rw [hEdef, Array.size_map, hws]
  have hEi : ∀ i < D.n, rowsMatrix E[i]! = matJ (f i) := by
    intro i hi
    have hi' : i < D.words.size := hws ▸ hi
    rw [hEdef, getElem!_pos _ i (by simpa using hi'), Array.getElem_map, hf]
    simp only
    rw [← getElem!_pos D.words i hi']
    refine rowsMatrix_wordRowsL fun r hr => hR r ?_
    exact hlet i hi' r (by rwa [getElem!_pos D.words i hi'] at hr)
  have hinvl : ∀ i < D.n, D.inv[i]! < D.n := by
    intro i hi
    have hi' : i < D.inv.size := his ▸ hi
    rw [getElem!_pos D.inv i hi']
    exact hinvlt i hi'
  have hfinv : ∀ i < D.n, f D.inv[i]! = (f i)⁻¹ := by
    intro i hi
    rw [eq_comm, inv_eq_iff_mul_eq_one]
    exact eq_of_rowsMatrix_eq (by rw [rowsMatrix_mulRows, hEi i hi, hEi _ (hinvl i hi), matJ_mul])
      (by rw [rowsMatrix_idRows, matJ_one]) (hinv i hi)
  have hwl : ∀ i < D.n, ∀ j ∈ D.wit[i]!, j < D.n := by
    intro i hi j hj
    have hi' : i < D.wit.size := hwis ▸ hi
    rw [getElem!_pos D.wit i hi'] at hj
    exact hwit i hi' j hj
  have hwfi : ∀ i < D.n, (rowAt E[i]! D.row).wf = true := by
    intro i hi
    have hi' : i < E.size := hEsize ▸ hi
    rw [getElem!_pos E i hi']
    exact hwf i hi'
  refine gLAPPrimeCoreOf_eq_bot_of_list hp hn f (fun i hi => ?_) (fun i hi j hj => ?_) hcard
    (fun i => D.wit[i]!) hwl (fun i hi hne => ?_)
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hi' : i < E.size := hEsize ▸ hi
    have h1 := hcomm i hi'
    rw [← getElem!_pos E i hi'] at h1
    exact eq_of_rowsMatrix_eq (by rw [rowsMatrix_mulRows, hEi i hi, hZ, matJ_mul])
      (by rw [rowsMatrix_mulRows, hZ, hEi i hi, matJ_mul]) h1
  ·
    intro heq
    exact rowsMatrix_ne_of_row hrow (hwfi i hi) (hwfi j (hj.trans hi)) (hdist i hi j hj)
      (by rw [hEi i hi, hEi j (hj.trans hi), heq])
  ·
    rcases hwit' i hi with h1 | h1
    · exact absurd (eq_of_rowsMatrix_eq (hEi i hi) (by rw [rowsMatrix_idRows, matJ_one]) h1) hne
    · have hP := rowsMatrix_witProd (E := E) (inv := D.inv) (f := f) (i := i) (l := D.wit[i]!)
        (fun j hj => by
          rcases List.mem_cons.1 hj with rfl | hj
          · exact hEi _ hi
          · exact hEi j (hwl i hi j hj))
        (fun j hj => by rw [hEi _ (hinvl j (hwl i hi j hj)), hfinv j (hwl i hi j hj)])
      exact ne_of_rowsDiffer (by rw [rowsMatrix_powRowsN, hP, matJ_pow])
        (by rw [rowsMatrix_idRows, matJ_one]) h1

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
