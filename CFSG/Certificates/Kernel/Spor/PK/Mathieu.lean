module

public import CFSG.Certificates.Kernel.Spor.PK.NatLetters
public import CFSG.Certificates.Kernel.Spor.PK.SiftSim
public import CFSG.Certificates.Kernel.Spor.PK.Cls

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Sporadic.Th.Native CFSG.Perm.Native
  CFSG.Sporadic.Mathieu.Native CFSG.KS.TW

theorem lenU_eq (l : List UInt32) : lenU l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show Nat.succ (lenU l) = l.length + 1
    rw [ih]

theorem allLtU_iff (n : Nat) (l : List UInt32) : allLtU n l = true ↔ ∀ x ∈ l, x.toNat < n := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => rfl⟩
  | cons x l ih =>
    have h : allLtU n (x :: l) = (Nat.blt x.toNat n && allLtU n l) := by
      rw [← bAnd_eq]
      rfl
    rw [h, Bool.and_eq_true, Nat.blt_eq, ih]
    simp

theorem allLtN_iff (n : Nat) (l : List Nat) : allLtN n l = true ↔ ∀ x ∈ l, x < n := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => rfl⟩
  | cons x l ih =>
    have h : allLtN n (x :: l) = (Nat.blt x n && allLtN n l) := by
      rw [← bAnd_eq]
      rfl
    rw [h, Bool.and_eq_true, Nat.blt_eq, ih]
    simp

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ j => exact (ih j).trans List.getD_cons_succ.symm

private theorem mth_itr_lt {n : Nat} {f : Nat → Nat} (hf : ∀ x < n, f x < n) (k : Nat) {x : Nat}
    (hx : x < n) : itr f k x < n := by
  induction k with
  | zero => exact hx
  | succ k ih => exact hf _ ih

private theorem mth_itr_congr {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n)
    (h : ∀ x < n, f x = g x) (k : Nat) : ∀ x < n, itr f k x = itr g k x := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    show f (itr f k x) = g (itr g k x)
    rw [← ih x hx]
    exact h _ (mth_itr_lt hf k hx)

private theorem mth_itr_lt_pow {n w : Nat} (hw : n < 2 ^ w) (T k : Nat) {x : Nat} (hx : x < n) :
    itr (fd w T) k x < 2 ^ w := by
  cases k with
  | zero => exact Nat.lt_trans hx hw
  | succ k => exact fd_lt w T _

private theorem mth_enc_eq_id_iff {n w : Nat} {g : Nat → Nat} (hg : ∀ i < n, g i < 2 ^ w)
    (hw : n < 2 ^ w) : enc w g n = enc w (fun i => i) n ↔ ∀ x < n, g x = x := by
  constructor
  · intro h x hx
    have h1 : fd w (enc w g n) x = fd w (enc w (fun i => i) n) x := by rw [h]
    rw [fd_enc hg hx, fd_enc (fun i hi => Nat.lt_trans hi hw) hx] at h1
    exact h1
  · intro h
    exact enc_congr h

theorem orderOK_iff {n w T p e : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hT : T < 2 ^ (w * n)) :
    CFSG.KS.Mathieu.orderOK n w (mask w) (pidn n w) T p e = true ↔
      (∀ x < n, itr (fd w T) (p ^ (e + 1)) x = x) ∧ ¬ ∀ x < n, itr (fd w T) (p ^ e) x = x := by
  have hnw : n < 2 ^ w := by omega
  have h24 : n ≤ 2 ^ 24 := by
    have : 2 ^ 16 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have h32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have key : ∀ k, Nat.beq (ppow n w (mask w) (pidn n w) T k) (pidn n w) = true ↔
      ∀ x < n, itr (fd w T) k x = x := by
    intro k
    rw [Nat.beq_eq, ppow_eq h32 h24 (Nat.le_of_lt hnw) T k, pidn_eq h24 (Nat.le_of_lt hnw)]
    exact mth_enc_eq_id_iff (fun i hi => mth_itr_lt_pow hnw T k hi) hnw
  unfold CFSG.KS.Mathieu.orderOK
  rw [bAnd_eq, bIf_eq, Bool.and_eq_true, key]
  apply and_congr Iff.rfl
  rw [← key]
  cases Nat.beq (ppow n w (mask w) (pidn n w) T (p ^ e)) (pidn n w) <;> simp

private theorem mth_table {n w : Nat} {t : Table} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hlen : lenU t.toList = n) (hlt : allLtU n t.toList = true)
    (hperm : permOK n w (mask w) (n * w) (packU w t.toList)
      (pinvS n w (mask w) (packU w t.toList)) = true) :
    TR n t (ap t) ∧ IsPermN n (ap t) ∧ packU w t.toList = enc w (ap t) n ∧
      pinvS n w (mask w) (packU w t.toList) = enc w (finv n (ap t)) n := by
  have hnw : n < 2 ^ w := by omega
  have hlen' : t.toList.length = n := by rw [← lenU_eq]; exact hlen
  have hsz : t.size = n := by simpa using hlen'
  have hlt' := (allLtU_iff n t.toList).1 hlt
  have hap : ∀ i < n, ap t i < n := by
    intro i hi
    unfold ap
    rw [getElem!_pos t i (by omega)]
    exact hlt' _ (by simp)
  have hTR : TR n t (ap t) := ⟨hsz, fun i hi => ⟨rfl, hap i hi⟩⟩
  have hpk : packU w t.toList = enc w (ap t) n := by
    rw [packU_eq (fun x hx => Nat.lt_trans (hlt' x hx) hnw), hlen']
    apply enc_congr
    intro i hi
    have hi' : i < t.size := by omega
    simp [ap, List.getD_eq_getElem?_getD, hi', getElem!_pos t i hi']
  have hfd : ∀ i < n, fd w (enc w (ap t) n) i = ap t i := fun i hi =>
    fd_enc (fun j hj => Nat.lt_trans (hap j hj) hnw) hi
  rw [hpk] at hperm ⊢
  obtain ⟨-, -, hperm'⟩ := permOK_iff.1 hperm
  have hPerm : IsPermN n (ap t) := by
    refine ⟨hap, fun i hi j hj hij => ?_⟩
    have h1 := (hperm' i hi).2
    have h2 := (hperm' j hj).2
    rw [hfd i hi] at h1
    rw [hfd j hj] at h2
    rw [← h1, ← h2, hij]
  refine ⟨hTR, hPerm, rfl, ?_⟩
  refine pinvS_eq (Nat.le_of_lt hnw) (fun i hi => by rw [hfd i hi]; exact hap i hi)
    (fun j hj => ?_) (fun i hi => ?_)
  · obtain ⟨h1, h2⟩ := finv_spec hPerm hj
    exact ⟨h1, by rw [hfd _ h1]; exact h2⟩
  · rw [hfd i hi]
    exact finv_apply hPerm hi

private theorem mth_gens_perm {n : Nat} {tA tB : Table} (hA : IsPermN n (ap tA))
    (hB : IsPermN n (ap tB)) (z : Int) : IsPermN n (gensT n tA tB z) := by
  unfold gensT
  by_cases h1 : z = 1
  · simp only [h1, if_true]
    exact hA
  by_cases h2 : z = -1
  · simp only [h1, h2, if_true, if_false]
    exact hA.finv
  by_cases h3 : z = 2
  · simp only [h1, h2, h3, if_true, if_false]
    exact hB
  · simp only [h1, h2, h3, if_true, if_false]
    exact hB.finv

private theorem mth_lettersP {n w : Nat} {D : Data} {A Ai B Bi : Nat}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hPA : IsPermN n (ap D.tA)) (hPB : IsPermN n (ap D.tB))
    (hA : A = enc w (ap D.tA) n) (hAi : Ai = enc w (finv n (ap D.tA)) n)
    (hB : B = enc w (ap D.tB) n) (hBi : Bi = enc w (finv n (ap D.tB)) n)
    (hws : Mathieu.wordsOK D.words.toList 0 = true) :
    lettersP n w (mask w) (n * w) (mask (n * w)) (pidn n w) A Ai B Bi D.words.toList 0 0 =
      enc (n * w) (fun l => enc w ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) n)
        (2 * D.words.size) := by
  have hnw : n < 2 ^ w := by omega
  have hfdA : ∀ i < n, fd w (enc w (ap D.tA) n) i = ap D.tA i := fun i hi =>
    fd_enc (fun j hj => Nat.lt_trans (hPA.1 j hj) hnw) hi
  have hfdAi : ∀ i < n, fd w (enc w (finv n (ap D.tA)) n) i = finv n (ap D.tA) i := fun i hi =>
    fd_enc (fun j hj => Nat.lt_trans (hPA.finv.1 j hj) hnw) hi
  have hfdB : ∀ i < n, fd w (enc w (ap D.tB) n) i = ap D.tB i := fun i hi =>
    fd_enc (fun j hj => Nat.lt_trans (hPB.1 j hj) hnw) hi
  have hfdBi : ∀ i < n, fd w (enc w (finv n (ap D.tB)) n) i = finv n (ap D.tB) i := fun i hi =>
    fd_enc (fun j hj => Nat.lt_trans (hPB.finv.1 j hj) hnw) hi
  subst hA hAi hB hBi
  rw [← Array.length_toList (xs := D.words)]
  refine lettersP_eq hn16 hw ?_ ?_ ?_ ?_ (fun z _ _ => mth_gens_perm hPA hPB z) hws
  · intro x hx
    rw [hfdA x hx]
    simp [gensT]
  · intro x hx
    rw [hfdAi x hx]
    simp [gensT]
  · intro x hx
    rw [hfdB x hx]
    simp [gensT]
  · intro x hx
    rw [hfdBi x hx]
    simp [gensT]

private theorem mth_letF_enc {n w NL : Nat} {Fa : Nat → Nat → Nat} (hw : n < 2 ^ w)
    (hF : ∀ l < NL, IsPermN n (Fa l)) {l : Nat} (hl : l < NL) {x : Nat} (hx : x < n) :
    letF n w (enc (n * w) (fun l => enc w (Fa l) n) NL) l x = Fa l x := by
  unfold letF
  have h1 : fd (n * w) (enc (n * w) (fun l => enc w (Fa l) n) NL) l = enc w (Fa l) n := by
    refine fd_enc (fun i hi => ?_) hl
    show enc w (Fa i) n < 2 ^ (n * w)
    rw [Nat.mul_comm n w]
    exact enc_lt fun j hj => Nat.lt_trans ((hF i hi).1 j hj) hw
  rw [h1]
  exact fd_enc (fun j hj => Nat.lt_trans ((hF l hl).1 j hj) hw) hx

private theorem mth_getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private structure ChainCond (n : Nat) (F : Nat → Nat → Nat) (NL : Nat) (D : Data)
    (gA gB : Nat → Nat) : Prop where
  sch : ∀ i < D.base.toList.length,
    absSch n F (lvAt F NL D.base.toList i)
      (BS.run F (lvAt F NL D.base.toList i) n (D.base.toList.getD i 0))
      (((natLevels n F NL D.base.toList).drop (i + 1)).map fun e => e.2.2) = true
  term : ∀ l ∈ lvAt F NL D.base.toList D.base.toList.length, ∀ x < n, F l x = x
  sizes : (natLevels n F NL D.base.toList).map (fun e => e.2.2.pts.length) = D.sizes
  siftA : absSift n F ((natLevels n F NL D.base.toList).map fun e => e.2.2) gA = true
  siftB : absSift n F ((natLevels n F NL D.base.toList).map fun e => e.2.2) gB = true
  k_le : D.k ≤ D.base.toList.length
  cover : ∀ i < D.k, D.base.toList.getD i 0 = i ∧
    ∀ p < n, i ≤ p → p ∈ (BS.run F (lvAt F NL D.base.toList i) n (D.base.toList.getD i 0)).pts
  ordX : (∀ x < n, itr (F 0) (D.pX ^ (D.eX + 1)) x = x) ∧
    ¬ ∀ x < n, itr (F 0) (D.pX ^ D.eX) x = x
  ordY : (∀ x < n, itr (F 2) (D.pY ^ (D.eY + 1)) x = x) ∧
    ¬ ∀ x < n, itr (F 2) (D.pY ^ D.eY) x = x
  ordXY : (∀ x < n, itr (fun x => F 0 (F 2 x)) (D.pXY ^ (D.eXY + 1)) x = x) ∧
    ¬ ∀ x < n, itr (fun x => F 0 (F 2 x)) (D.pXY ^ D.eXY) x = x

private theorem mth_natLevels_mem {n NL : Nat} {F : Nat → Nat → Nat} {bs : List Nat}
    {e : List Nat × Nat × BS} (he : e ∈ natLevels n F NL bs) :
    ∃ i < bs.length,
      e = (lvAt F NL bs i, bs.getD i 0, BS.run F (lvAt F NL bs i) n (bs.getD i 0)) := by
  unfold natLevels at he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  exact ⟨i, List.mem_range.1 hi, rfl⟩

private theorem mth_levelOK {n NL : Nat} {F : Nat → Nat → Nat} {bs : List Nat}
    (hbs : ∀ b ∈ bs, b < n) (hF : ∀ l < NL, IsPermN n (F l)) {i : Nat} (hi : i < bs.length) :
    LevelOK n F (lvAt F NL bs i) (bs.getD i 0) (BS.run F (lvAt F NL bs i) n (bs.getD i 0)) :=
  ⟨run_ok (fun l hl => (hF l (lvAt_sub F NL bs i l hl)).1) (hbs _ (mth_getD_mem hi)),
    fun l hl => hF l (lvAt_sub F NL bs i l hl)⟩

private theorem mth_natLevels_levelOK {n NL : Nat} {F : Nat → Nat → Nat} {bs : List Nat}
    (hbs : ∀ b ∈ bs, b < n) (hF : ∀ l < NL, IsPermN n (F l)) :
    ∀ e ∈ natLevels n F NL bs, LevelOK n F e.1 e.2.1 e.2.2 := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mth_natLevels_mem he
  exact mth_levelOK hbs hF hi

private theorem mth_natLevels_congr {n NL : Nat} {F G : Nat → Nat → Nat} {bs : List Nat}
    (hn0 : 0 < n) (hbs : ∀ b ∈ bs, b < n) (hF : ∀ l < NL, IsPermN n (F l))
    (h : ∀ l < NL, ∀ x < n, F l x = G l x) : natLevels n F NL bs = natLevels n G NL bs := by
  unfold natLevels
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  show (lvAt F NL bs i, bs.getD i 0, BS.run F (lvAt F NL bs i) n (bs.getD i 0)) =
    (lvAt G NL bs i, bs.getD i 0, BS.run G (lvAt G NL bs i) n (bs.getD i 0))
  rw [← lvAt_congr hn0 hbs h i]
  rw [run_congr (hbs _ (mth_getD_mem hi'))
    (fun l hl => (hF l (lvAt_sub F NL bs i l hl)).1)
    (fun l hl => h l (lvAt_sub F NL bs i l hl))]

private theorem mth_ord_congr {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n)
    (h : ∀ x < n, f x = g x) {k1 k2 : Nat}
    (hc : (∀ x < n, itr f k1 x = x) ∧ ¬ ∀ x < n, itr f k2 x = x) :
    (∀ x < n, itr g k1 x = x) ∧ ¬ ∀ x < n, itr g k2 x = x := by
  refine ⟨fun x hx => ?_, fun H => hc.2 fun x hx => ?_⟩
  · rw [← mth_itr_congr hf h k1 x hx]
    exact hc.1 x hx
  · rw [mth_itr_congr hf h k2 x hx]
    exact H x hx

private theorem ChainCond.congr {n NL : Nat} {F G : Nat → Nat → Nat} {D : Data} {gA gB : Nat → Nat}
    (hn0 : 0 < n) (hbs : ∀ b ∈ D.base.toList, b < n) (hF : ∀ l < NL, IsPermN n (F l))
    (h : ∀ l < NL, ∀ x < n, F l x = G l x) (h2 : 2 < NL) (hgA : ∀ x < n, gA x < n)
    (hgB : ∀ x < n, gB x < n) (hc : ChainCond n F NL D gA gB) : ChainCond n G NL D gA gB := by
  have hNF : natLevels n F NL D.base.toList = natLevels n G NL D.base.toList :=
    mth_natLevels_congr hn0 hbs hF h
  have hlv : ∀ i, lvAt F NL D.base.toList i = lvAt G NL D.base.toList i :=
    lvAt_congr hn0 hbs h
  have hrun : ∀ i < D.base.toList.length,
      BS.run F (lvAt F NL D.base.toList i) n (D.base.toList.getD i 0) =
        BS.run G (lvAt F NL D.base.toList i) n (D.base.toList.getD i 0) := by
    intro i hi
    exact run_congr (hbs _ (mth_getD_mem hi)) (fun l hl => (hF l (lvAt_sub F NL _ i l hl)).1)
      (fun l hl => h l (lvAt_sub F NL _ i l hl))
  refine ⟨?_, ?_, ?_, ?_, ?_, hc.k_le, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := hc.sch i hi
    rw [← hNF, ← hlv i, ← hrun i hi]
    rw [← absSch_congr (mth_levelOK hbs hF hi) (fun l hl => h l (lvAt_sub F NL _ i l hl))
      (L := (natLevels n F NL D.base.toList).drop (i + 1))
      (fun e he => mth_natLevels_levelOK hbs hF e (List.mem_of_mem_drop he))
      (fun e he l hl => by
        obtain ⟨j, hj, rfl⟩ := mth_natLevels_mem (List.mem_of_mem_drop he)
        exact h l (lvAt_sub F NL _ j l hl))]
    exact h1
  · intro l hl x hx
    rw [← hlv] at hl
    have hlt := lvAt_sub F NL _ _ l hl
    rw [← h l hlt x hx]
    exact hc.term l hl x hx
  · rw [← hNF]
    exact hc.sizes
  · rw [← hNF, ← absSift_congr (mth_natLevels_levelOK hbs hF)
      (fun e he l hl x hx => by
        obtain ⟨j, hj, rfl⟩ := mth_natLevels_mem he
        exact h l (lvAt_sub F NL _ j l hl) x hx) hgA]
    exact hc.siftA
  · rw [← hNF, ← absSift_congr (mth_natLevels_levelOK hbs hF)
      (fun e he l hl x hx => by
        obtain ⟨j, hj, rfl⟩ := mth_natLevels_mem he
        exact h l (lvAt_sub F NL _ j l hl) x hx) hgB]
    exact hc.siftB
  · intro i hi
    obtain ⟨h1, h2⟩ := hc.cover i hi
    have hi' : i < D.base.toList.length := Nat.lt_of_lt_of_le hi hc.k_le
    refine ⟨h1, ?_⟩
    rw [← hlv i, ← hrun i hi']
    exact h2
  · exact mth_ord_congr (fun x hx => (hF 0 (by omega)).1 x hx) (fun x hx => h 0 (by omega) x hx)
      hc.ordX
  · exact mth_ord_congr (fun x hx => (hF 2 h2).1 x hx) (fun x hx => h 2 h2 x hx) hc.ordY
  · refine mth_ord_congr (fun x hx => (hF 0 (by omega)).1 _ ((hF 2 h2).1 x hx)) (fun x hx => ?_)
      hc.ordXY
    show F 0 (F 2 x) = G 0 (G 2 x)
    rw [h 0 (by omega) _ ((hF 2 h2).1 x hx), h 2 h2 x hx]

private theorem mth_allIn_iff {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hlo hhi
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [show lo + (i - lo) = i by omega] using this
  · intro h ⟨k, hk⟩ _
    simpa using h (lo + k) (by omega) (by omega)

private theorem mth_orderOK_nat {n : Nat} (hn32 : n < 2 ^ 32) {T : Table} {f : Nat → Nat}
    (hT : TR n T f) (p e : Nat) :
    Sporadic.Mathieu.Native.orderOK n T p e = true ↔
      (∀ x < n, itr f (p ^ (e + 1)) x = x) ∧ ¬ ∀ x < n, itr f (p ^ e) x = x := by
  have h1 := isIdT_iff (powT_TR hn32 hT (p ^ (e + 1)))
  have h2 := isIdT_iff (powT_TR hn32 hT (p ^ e))
  unfold Sporadic.Mathieu.Native.orderOK
  rw [Bool.and_eq_true, h1]
  apply and_congr Iff.rfl
  rw [← h2]
  cases isIdT n (powT n (p ^ e) T) <;> simp

private theorem mth_arr_get (a : Array Nat) {i : Nat} (h : i < a.size) :
    a[i]! = a.toList.getD i 0 := by
  simp [getElem!_pos a i h, List.getD_eq_getElem?_getD, h]

private theorem mth_native {n : Nat} {D : Data} (hn32 : n < 2 ^ 32) (hn0 : 0 < n)
    (hTA : TR n D.tA (ap D.tA)) (hPA : IsPermN n (ap D.tA))
    (hTB : TR n D.tB (ap D.tB)) (hPB : IsPermN n (ap D.tB))
    (hws : Mathieu.wordsOK D.words.toList 0 = true) (hD : D.words.size < 2 ^ 31)
    (h2 : 2 ≤ D.words.size) (hbs : ∀ b ∈ D.base.toList, b < n)
    (hc : ChainCond n (tabF (letters n D)) (letters n D).size D (ap D.tA) (ap D.tB)) :
    check n D = true := by
  have hLO : LettersOK n (letters n D) := lettersOK_letters hn32 hD hTA hPA hTB hPB hws
  have hF : ∀ l < (letters n D).size, ∀ x < n, tabF (letters n D) l x < n :=
    fun l hl x hx => (hLO.2.2 l hl).2.1.1 x hx
  have hlevTR : ∀ l < (letters n D).size, TR n (letters n D)[l]! (tabF (letters n D) l) :=
    fun l hl => ⟨(hLO.2.2 l hl).1, fun i hi => ⟨rfl, hF l hl i hi⟩⟩
  have hsize : (letters n D).size = 2 * D.words.size :=
    (letters_TR hn32 hTA hPA hTB hPB hws).1
  have hlenb : D.base.toList.length = D.base.size := Array.length_toList
  have hws' := (wordsOK_iff _ 0).1 hws
  have hwl : D.words.toList.length = D.words.size := Array.length_toList
  have hNLen : (natLevels n (tabF (letters n D)) (letters n D).size D.base.toList).length =
      D.base.toList.length := by simp [natLevels]
  have hNget : ∀ i (hi : i < D.base.toList.length),
      (natLevels n (tabF (letters n D)) (letters n D).size D.base.toList)[i]'(by rw [hNLen]; exact hi) =
        (lvAt (tabF (letters n D)) (letters n D).size D.base.toList i, D.base.toList.getD i 0,
          BS.run (tabF (letters n D)) (lvAt (tabF (letters n D)) (letters n D).size D.base.toList i) n
            (D.base.toList.getD i 0)) := by
    intro i hi
    simp [natLevels]
  unfold check
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact invOK_of hTA (invT_TR' hn32 hTA hPA) (fun i hi => finv_apply hPA hi)
  · exact invOK_of hTB (invT_TR' hn32 hTB hPB) (fun i hi => finv_apply hPB hi)
  ·
    unfold Sporadic.Fi23.Native.slpOK
    rw [mth_allIn_iff]
    intro j _ hj
    rw [List.all_eq_true]
    intro z hz
    have hj' : j < D.words.toList.length := by rw [hwl]; exact hj
    have hget : D.words[j]! = D.words.toList.getD j [] := by
      simp [getElem!_pos D.words j hj, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hz
    obtain ⟨h1, h2', -⟩ := hws' j hj' z hz
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨h1, by simpa using h2'⟩
  ·
    unfold Sporadic.Fi23.Native.slpPure
    rw [mth_allIn_iff]
    intro j hj2 hj
    rw [List.all_eq_true]
    intro z hz
    have hj' : j < D.words.toList.length := by rw [hwl]; exact hj
    have hget : D.words[j]! = D.words.toList.getD j [] := by
      simp [getElem!_pos D.words j hj, List.getD_eq_getElem?_getD, hj]
    rw [hget] at hz
    obtain ⟨-, -, h3⟩ := hws' j hj' z hz
    simpa using h3.resolve_left (by omega)
  ·
    refine chainOK_of hn32 hn0 hLO hbs (fun i hi => ?_) ?_
    · have hi' : i < D.base.toList.length := by rw [← hNLen]; exact hi
      rw [hNget i hi']
      exact hc.sch i hi'
    · intro l hl x hx
      rw [← hlenb] at hl
      exact hc.term l hl x hx
  ·
    show orbitSizes (chainTrees n (letters n D) D.base) = D.sizes
    rw [orbitSizes_eq hn32 hbs hF]
    exact hc.sizes
  ·
    show Perm.Native.sift (chainTrees n (letters n D) D.base) (letters n D) D.base (Array.range n) 0
      (apT D.tA (Array.range n)) = true
    rw [chainTrees_eq hn32 hbs hF, apT_map,
      sift_treeOf hn32 (natLevelsOK hn32 hLO hbs) ?_ hPA.1 0]
    · simpa using hc.siftA
    · intro i hi
      have hi' : i < D.base.toList.length := by rw [← hNLen]; exact hi
      rw [hNget i hi']
      exact mth_arr_get D.base (by rw [← hlenb]; exact hi')
  ·
    show Perm.Native.sift (chainTrees n (letters n D) D.base) (letters n D) D.base (Array.range n) 0
      (apT D.tB (Array.range n)) = true
    rw [chainTrees_eq hn32 hbs hF, apT_map,
      sift_treeOf hn32 (natLevelsOK hn32 hLO hbs) ?_ hPB.1 0]
    · simpa using hc.siftB
    · intro i hi
      have hi' : i < D.base.toList.length := by rw [← hNLen]; exact hi
      rw [hNget i hi']
      exact mth_arr_get D.base (by rw [← hlenb]; exact hi')
  · have := hc.k_le
    omega
  ·
    rw [mth_allIn_iff]
    intro i _ hik
    have hi' : i < D.base.toList.length := Nat.lt_of_lt_of_le hik hc.k_le
    have hi'' : i < D.base.size := by rw [← hlenb]; exact hi'
    obtain ⟨hb, hcov⟩ := hc.cover i hik
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [mth_arr_get D.base hi'', hb]
      exact beq_self_eq_true i
    · unfold Sporadic.Mathieu.Native.levelCover
      rw [mth_allIn_iff]
      intro p _ hp
      by_cases hpi : p < i
      · simp [hpi]
      · have hmem := hcov p hp (by omega)
        have hs := run_ok (n := n) (F := tabF (letters n D))
          (lv := lvAt (tabF (letters n D)) (letters n D).size D.base.toList i)
          (r := D.base.toList.getD i 0)
          (fun l hl => hF l (lvAt_sub _ _ _ _ l hl)) (hbs _ (mth_getD_mem hi'))
        have hT : (trees n D)[i]! = treeOf n (BS.run (tabF (letters n D))
            (lvAt (tabF (letters n D)) (letters n D).size D.base.toList i) n
            (D.base.toList.getD i 0)) := by
          show (chainTrees n (letters n D) D.base)[i]! = _
          rw [chainTrees_eq hn32 hbs hF]
          have hlt : i < (((natLevels n (tabF (letters n D)) (letters n D).size D.base.toList).map
              fun e => treeOf n e.2.2).toArray).size := by
            simpa [natLevels] using hi'
          rw [getElem!_pos _ i hlt]
          simp [natLevels]
        rw [hT, inTreeB_treeOf hn32 hs.lt hs.nodup hp]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hmem
  · rw [mth_orderOK_nat hn32 (hlevTR 0 (by omega))]
    exact hc.ordX
  · rw [mth_orderOK_nat hn32 (hlevTR 2 (by omega))]
    exact hc.ordY
  · rw [mth_orderOK_nat hn32 (compT_TR hn32 (hlevTR 0 (by omega)) (hlevTR 2 (by omega)))]
    exact hc.ordXY

private theorem mth_absChain_iff {n NL : Nat} {F : Nat → Nat → Nat} (ps : List (BS × Nat)) :
    absChain n F NL ps = true ↔ ∀ i (h : i < ps.length),
      absSch n F (maskL NL ps[i].2) ps[i].1 ((ps.drop (i + 1)).map Prod.fst) = true := by
  induction ps with
  | nil => simp [absChain]
  | cons p ps ih =>
    rw [absChain, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ j => exact h1 j (Nat.lt_of_succ_lt_succ hi)
    · intro h
      exact ⟨h 0 (Nat.succ_pos _), fun j hj => h (j + 1) (Nat.succ_lt_succ hj)⟩

private theorem mth_levLast (n w LT NL : Nat) (bs : List Nat) :
    levLast n w LT NL bs (mask NL) = levMaskAt n w LT NL bs bs.length := by
  unfold levMaskAt
  rw [List.take_length]

private theorem mth_packed_chain {n w LT NL : Nat} {D : Data} {gA gB : Nat → Nat}
    (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hn0 : 0 < n)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) (h2 : 2 < NL)
    (hbs : ∀ b ∈ D.base.toList, b < n)
    (hgA : ∀ x < n, gA x < n) (hgB : ∀ x < n, gB x < n)
    (h : chainPart n w (mask w) (n * w) (mask (n * w)) (pidn n w) (enc w gA n) (enc w gB n) LT NL D
      = true) :
    ChainCond n (letF n w LT) NL D gA gB := by
  have hn32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  unfold chainPart at h
  rw [strictB_eq, levels_eq hn16 hw hL hbs] at h
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true] at h
  rw [mth_levLast] at h
  generalize hps : levPairs n w LT NL D.base.toList (mask NL) = ps at h
  obtain ⟨hsch, hmid, hsz, hsA, hsB, hk, hcov, hox, hoy, hoxy⟩ := h
  have hps' : ps = (List.range D.base.toList.length).map fun i =>
      (BS.run (letF n w LT) (lvAt (letF n w LT) NL D.base.toList i) n (D.base.toList.getD i 0),
        levMaskAt n w LT NL D.base.toList i) := by
    rw [← hps]
    exact levPairs_eq _
  have hlen : ps.length = D.base.toList.length := by
    rw [hps']
    simp
  have hget : ∀ i (hi : i < ps.length), ps[i] =
      (BS.run (letF n w LT) (lvAt (letF n w LT) NL D.base.toList i) n (D.base.toList.getD i 0),
        levMaskAt n w LT NL D.base.toList i) := by
    intro i hi
    subst hps'
    simp
  have hgood : ∀ p ∈ ps, GoodBS n (letF n w LT) p.1 := by
    intro p hp
    rw [hps'] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have hi' := List.mem_range.1 hi
    exact goodBS_run (hbs _ (mth_getD_mem hi')) (fun l hl => hL l (lvAt_sub _ _ _ _ l hl))
  have hfst : ps.map Prod.fst =
      (natLevels n (letF n w LT) NL D.base.toList).map (fun e => e.2.2) := by
    rw [hps']
    simp [natLevels, List.map_map, Function.comp_def]
  have hblk : ∀ l, blk LT (n * w) (mask (n * w)) l = fd (n * w) LT l := fun l =>
    blk_eq LT (n * w) l
  have hblkF : ∀ l x, fd w (blk LT (n * w) (mask (n * w)) l) x = letF n w LT l x := fun l x => by
    rw [hblk]
    rfl
  have hblkLt : ∀ l, blk LT (n * w) (mask (n * w)) l < 2 ^ (w * n) := fun l => by
    rw [hblk, Nat.mul_comm w n]
    exact fd_lt (n * w) LT l
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i hi
    have hi' : i < ps.length := by rw [hlen]; exact hi
    have habs : absChain n (letF n w LT) NL ps = true := by
      rw [← chainSch_eq hn16 hw hL hgood]
      exact hsch
    have h1 := (mth_absChain_iff ps).1 habs i hi'
    have e1 := hget i hi'
    have e2 : (ps[i]'hi').2 = levMaskAt n w LT NL D.base.toList i := by rw [e1]
    have e3 : (ps[i]'hi').1 =
        BS.run (letF n w LT) (lvAt (letF n w LT) NL D.base.toList i) n (D.base.toList.getD i 0) := by
      rw [e1]
    have hmask : maskL NL (levMaskAt n w LT NL D.base.toList i) =
        lvAt (letF n w LT) NL D.base.toList i := by
      rw [maskL_levMaskAt, Nat.min_eq_left (Nat.le_of_lt hi)]
    have hdrop : (ps.drop (i + 1)).map Prod.fst =
        ((natLevels n (letF n w LT) NL D.base.toList).drop (i + 1)).map (fun e => e.2.2) := by
      rw [List.map_drop, hfst, List.map_drop]
    rw [e2, e3, hmask, hdrop] at h1
    exact h1
  ·
    rw [maskId_iff hn16 hw, maskL_levMaskAt, Nat.min_self] at hmid
    exact hmid
  ·
    have h1 := (sizesEq_iff _ _).1 hsz
    have h2 : List.map lcnt (List.map (fun p => recBS n w (letF n w LT) p.fst p.snd) ps) =
        ps.map (fun p => p.1.pts.length) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact lcnt_recBS hn16 hw (hgood p hp) p.2
    rw [h2] at h1
    rw [← h1]
    have h3 : (natLevels n (letF n w LT) NL D.base.toList).map (fun e => e.2.2.pts.length) =
        ((natLevels n (letF n w LT) NL D.base.toList).map (fun e => e.2.2)).map
          (fun s => s.pts.length) := by
      rw [List.map_map]
      rfl
    have h4 : ps.map (fun p => p.1.pts.length) = (ps.map Prod.fst).map (fun s => s.pts.length) := by
      rw [List.map_map]
      rfl
    rw [h3, ← hfst, h4]
  · rw [sift_eq hn16 hw hgood hgA, hfst] at hsA
    exact hsA
  · rw [sift_eq hn16 hw hgood hgB, hfst] at hsB
    exact hsB
  · rw [Nat.ble_eq, lenN_eq] at hk
    exact hk
  ·
    intro i hik
    have hk' : D.k ≤ D.base.toList.length := by
      rw [Nat.ble_eq, lenN_eq] at hk
      exact hk
    have hi' : i < ps.length := by rw [hlen]; omega
    rw [allN_iff] at hcov
    have h1 := hcov i hik
    rw [Bool.and_eq_true, Nat.beq_eq, nget_eq, lget_eq] at h1
    obtain ⟨h1a, h1b⟩ := h1
    refine ⟨h1a, ?_⟩
    have e1 := hget i hi'
    have e : (List.map (fun p => recBS n w (letF n w LT) p.fst p.snd) ps).getD i 0 =
        recBS n w (letF n w LT)
          (BS.run (letF n w LT) (lvAt (letF n w LT) NL D.base.toList i) n (D.base.toList.getD i 0))
          (levMaskAt n w LT NL D.base.toList i) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi']
      simp [e1]
    have hg : GoodBS n (letF n w LT)
        (BS.run (letF n w LT) (lvAt (letF n w LT) NL D.base.toList i) n (D.base.toList.getD i 0)) := by
      have := hgood (ps[i]'hi') (List.getElem_mem hi')
      rw [e1] at this
      exact this
    rw [e, coverOK_iff hn16 hw hg] at h1b
    exact h1b
  ·
    rw [orderOK_iff hn16 hw (hblkLt 0)] at hox
    refine mth_ord_congr (f := fd w (blk LT (n * w) (mask (n * w)) 0)) (g := letF n w LT 0)
      (fun x hx => ?_) (fun x hx => hblkF 0 x) hox
    rw [hblkF]
    exact (hL 0 (by omega)).1 x hx
  · rw [orderOK_iff hn16 hw (hblkLt 2)] at hoy
    refine mth_ord_congr (f := fd w (blk LT (n * w) (mask (n * w)) 2)) (g := letF n w LT 2)
      (fun x hx => ?_) (fun x hx => hblkF 2 x) hoy
    rw [hblkF]
    exact (hL 2 h2).1 x hx
  · rw [orderOK_iff hn16 hw (pcomp_lt hn32 w _ _)] at hoxy
    refine mth_ord_congr
      (f := fd w (pcomp n w (mask w) (blk LT (n * w) (mask (n * w)) 0) (blk LT (n * w) (mask (n * w)) 2)))
      (g := fun x => letF n w LT 0 (letF n w LT 2 x))
      (fun x hx => ?_) (fun x hx => ?_) hoxy
    · rw [fd_pcomp hn32 w _ _ hx, hblkF, hblkF]
      exact (hL 0 (by omega)).1 _ ((hL 2 h2).1 x hx)
    · rw [fd_pcomp hn32 w _ _ hx, hblkF, hblkF]

private theorem mth_isPermN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x)
    (hf : IsPermN n f) : IsPermN n g :=
  ⟨fun x hx => by rw [← h x hx]; exact hf.1 x hx,
    fun x hx y hy e => hf.2 x hx y hy (by rw [h x hx, h y hy]; exact e)⟩

theorem mcheck_sound' {n w : Nat} {D : Data} (hD : D.words.size < 2 ^ 31)
    (h : mcheck n w D = true) : check n D = true := by
  unfold mcheck at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.mul_eq, Nat.succ_eq_add_one, Nat.add_eq,
    Nat.blt_eq, Nat.beq_eq, Nat.ble_eq] at h
  obtain ⟨hn0, hnm, hn16, hlA, hltA, hlB, hltB, hpA, hpB, hws, h2, hbase, hch⟩ := h
  have hn16' : n < 2 ^ 16 := by simpa using hn16
  have hn32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hw : n + 1 < 2 ^ w := by
    rw [mask_eq] at hnm
    omega
  obtain ⟨hTA, hPA, hAe, hAie⟩ := mth_table hn16' hw hlA hltA hpA
  obtain ⟨hTB, hPB, hBe, hBie⟩ := mth_table hn16' hw hlB hltB hpB
  have hlen : D.words.toList.length = D.words.size := Array.length_toList
  have hNL : lenW D.words.toList + lenW D.words.toList = 2 * D.words.size := by
    rw [lenW_eq, hlen]
    omega
  have h2' : 2 ≤ D.words.size := by
    rw [lenW_eq, hlen] at h2
    exact h2
  have hbs : ∀ b ∈ D.base.toList, b < n := (allLtN_iff n _).1 hbase
  have hlet := mth_lettersP hn16' hw hPA hPB hAe hAie hBe hBie hws
  rw [hlet, hAe, hBe, hNL] at hch
  obtain ⟨hsz, hTR⟩ := letters_TR hn32 hTA hPA hTB hPB hws
  have hFa : ∀ l < 2 * D.words.size,
      IsPermN n ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) := fun l hl =>
    lettersFn_isPermN (fun z _ _ => mth_gens_perm hPA hPB z) hws (by rw [hlen]; exact hl)
  have hagree : ∀ l < 2 * D.words.size, ∀ x < n,
      letF n w (enc (n * w) (fun l => enc w
        ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) n) (2 * D.words.size)) l x =
        tabF (letters n D) l x := by
    intro l hl x hx
    rw [mth_letF_enc (Nat.lt_of_succ_lt hw) hFa hl hx]
    exact ((hTR l hl).2 x hx).1.symm
  have hL : ∀ l < 2 * D.words.size,
      IsPermN n (letF n w (enc (n * w) (fun l => enc w
        ((lettersFn n (gensT n D.tA D.tB) D.words.toList).getD l id) n) (2 * D.words.size)) l) :=
    fun l hl => mth_isPermN_congr (fun x hx =>
      (mth_letF_enc (Nat.lt_of_succ_lt hw) hFa hl hx).symm) (hFa l hl)
  have hc := mth_packed_chain hn16' hw hn0 hL (by omega) hbs hPA.1 hPB.1 hch
  have hc' := ChainCond.congr hn0 hbs hL hagree (by omega) hPA.1 hPB.1 hc
  rw [← hsz] at hc'
  exact mth_native hn32 hn0 hTA hPA hTB hPB hws hD h2' hbs hc'

end CFSG.KS.PK

end
