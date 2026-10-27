module

public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Certificates.Kernel.Spor.PK.ChainSim
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Monster.B.Mathieu.CertText5
public import Certificates.Data.Kernel.Spor.MCount

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

@[expose] def dsum (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | N + 1 => dsum a N + a N * 2 ^ (20 * N)

theorem dsum_lt {a : Nat → Nat} (ha : ∀ f, a f < 2 ^ 20) : ∀ N, dsum a N < 2 ^ (20 * N)
  | 0 => by simp [dsum]
  | N + 1 => by
    have h1 := dsum_lt ha N
    have h2 : a N + 1 ≤ 2 ^ 20 := ha N
    have h3 : (a N + 1) * 2 ^ (20 * N) ≤ 2 ^ 20 * 2 ^ (20 * N) := Nat.mul_le_mul_right _ h2
    have hP : 2 ^ (20 * (N + 1)) = 2 ^ 20 * 2 ^ (20 * N) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hP]
    change dsum a N + a N * 2 ^ (20 * N) < _
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem dsum_digit {a : Nat → Nat} (ha : ∀ f, a f < 2 ^ 20) (e : Nat) :
    ∀ N, dsum a N / 2 ^ (20 * e) % 2 ^ 20 = if e < N then a e else 0
  | 0 => by simp [dsum]
  | N + 1 => by
    have hS := dsum_lt ha N
    change (dsum a N + a N * 2 ^ (20 * N)) / 2 ^ (20 * e) % 2 ^ 20 = _
    rcases Nat.lt_trichotomy e N with h | h | h
    · rw [if_pos (by omega)]
      obtain ⟨d, rfl⟩ : ∃ d, N = e + 1 + d := ⟨N - e - 1, by omega⟩
      have hP : 2 ^ (20 * (e + 1 + d)) = 2 ^ (20 * e) * (2 ^ 20 * 2 ^ (20 * d)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        congr 1
        ring
      have e2 : a (e + 1 + d) * (2 ^ (20 * e) * (2 ^ 20 * 2 ^ (20 * d))) =
          2 ^ 20 * (a (e + 1 + d) * 2 ^ (20 * d)) * 2 ^ (20 * e) := by ring
      rw [hP, e2, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_left]
      have hd := dsum_digit ha e (e + 1 + d)
      rw [if_pos (by omega)] at hd
      exact hd
    · subst h
      rw [if_pos (by omega), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hS, Nat.zero_add]
      exact Nat.mod_eq_of_lt (ha e)
    · rw [if_neg (by omega)]
      have hlt : dsum a N + a N * 2 ^ (20 * N) < 2 ^ (20 * e) := by
        have h1 := dsum_lt ha (N + 1)
        have h2 : 2 ^ (20 * (N + 1)) ≤ 2 ^ (20 * e) := Nat.pow_le_pow_right (by decide) (by omega)
        change dsum a N + a N * 2 ^ (20 * N) < _ at h1
        omega
      rw [Nat.div_eq_of_lt hlt, Nat.zero_mod]

theorem sum_dsum {α : Type*} (L : List α) (b : α → Nat → Nat) (N : Nat) :
    (L.map fun g => dsum (b g) N).sum = dsum (fun f => (L.map fun g => b g f).sum) N := by
  induction N with
  | zero => simp [dsum]
  | succ N ih =>
    change (L.map fun g => dsum (b g) N + b g N * 2 ^ (20 * N)).sum = _ + _
    rw [List.sum_map_add, ih, List.sum_map_mul_right]

@[expose] def flds (c0 c1 : Nat) (P M : Nat → Nat) (f : Nat) : Nat :=
  if f = 0 then c0 else if f = 1 then c1 else if f % 2 = 0 then P ((f - 2) / 2)
    else M ((f - 3) / 2)

theorem flds_zero (c0 c1 : Nat) (P M : Nat → Nat) : flds c0 c1 P M 0 = c0 := rfl

theorem flds_one (c0 c1 : Nat) (P M : Nat → Nat) : flds c0 c1 P M 1 = c1 := rfl

theorem flds_even (c0 c1 : Nat) (P M : Nat → Nat) (j : Nat) : flds c0 c1 P M (2 + 2 * j) = P j := by
  unfold flds
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem flds_odd (c0 c1 : Nat) (P M : Nat → Nat) (j : Nat) : flds c0 c1 P M (3 + 2 * j) = M j := by
  unfold flds
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

theorem dsum_split (a : Nat → Nat) (J : Nat) :
    dsum a (2 + 2 * J) = a 0 + a 1 * 2 ^ 20 + ((List.range J).map fun j =>
      a (2 + 2 * j) * 2 ^ (40 + 40 * j) + a (3 + 2 * j) * 2 ^ (60 + 40 * j)).sum := by
  induction J with
  | zero => simp [dsum]
  | succ J ih =>
    have e : 2 + 2 * (J + 1) = (2 + 2 * J) + 1 + 1 := by omega
    rw [e]
    change dsum a (2 + 2 * J) + a (2 + 2 * J) * 2 ^ (20 * (2 + 2 * J)) +
      a (2 + 2 * J + 1) * 2 ^ (20 * (2 + 2 * J + 1)) = _
    rw [ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    have e1 : 20 * (2 + 2 * J) = 40 + 40 * J := by omega
    have e2 : 20 * (2 + 2 * J + 1) = 60 + 40 * J := by omega
    have e3 : 2 + 2 * J + 1 = 3 + 2 * J := by omega
    rw [e1, e2, e3]
    omega

section Step

variable (n w m ky r : Nat) (Rs : List (Nat × Nat))

@[expose] def rAt (j : Nat) : Nat × Nat := Rs.getD j (0, 0)

@[expose] noncomputable def cfld (g : Nat → Nat) : Nat → Nat :=
  flds (if powId n g 2 = true ∧ powId n g 1 = false then 1 else 0)
    (if powId n g 2 = false ∧ powId n g ky = true then 1 else 0)
    (fun j => if powId n g 2 = false ∧ powId n g ky = true ∧
        partZ n w m ky r (rAt Rs j).1 (rAt Rs j).2 g = true then 1 else 0)
    (fun j => if powId n g 2 = true ∧ powId n g 1 = false ∧
        allFrom (fun i => Nat.beq (g i) (pg w m (rAt Rs j).1 i)) n 0 = true then 1 else 0)

end Step

private theorem nIf_eq' (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem shl_one (e : Nat) : Nat.shiftLeft 1 e = 2 ^ e := by
  change 1 <<< e = 2 ^ e
  exact Nat.one_shiftLeft e

private theorem split_head (c : Nat → Nat) (L e : Nat) (b : Nat) (hb : b = c 0) :
    b * 2 ^ e + ((List.range L).map fun j => c (j + 1) * 2 ^ (e + 40 + 40 * j)).sum =
      ((List.range (L + 1)).map fun j => c j * 2 ^ (e + 40 * j)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map, hb]
  refine congrArg₂ (· + ·) (by simp) ?_
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    rw [show e + 40 + 40 * j = e + 40 * (j + 1) by omega]

theorem memsZ_eq (n w m : Nat) (g : Nat → Nat) :
    ∀ (Rs : List (Nat × Nat)) (e : Nat), memsZ n w m g Rs e = ((List.range Rs.length).map fun j =>
      (if allFrom (fun i => Nat.beq (g i) (pg w m (rAt Rs j).1 i)) n 0 = true then 1 else 0) *
        2 ^ (e + 40 * j)).sum
  | [], e => rfl
  | (R, Ri) :: Rs, e => by
    have hc : memsZ n w m g ((R, Ri) :: Rs) e =
        Nat.add (nIf(allFrom (fun i => Nat.beq (g i) (pg w m R i)) n (nat_lit 0),
          Nat.shiftLeft (nat_lit 1) e, nat_lit 0)) (memsZ n w m g Rs (Nat.add e (nat_lit 40))) :=
      rfl
    rw [hc, memsZ_eq n w m g Rs, nIf_eq', shl_one, List.length_cons]
    refine Eq.trans ?_ (split_head (fun j => if allFrom (fun i => Nat.beq (g i)
      (pg w m (rAt ((R, Ri) :: Rs) j).1 i)) n 0 = true then 1 else 0) Rs.length e
      (if allFrom (fun i => Nat.beq (g i) (pg w m R i)) n 0 = true then 1 else 0) rfl)
    simp only [Nat.add_eq]
    refine congrArg₂ (· + ·) ?_ rfl
    split <;> simp

theorem partsZ_eq (n w m ky r : Nat) (g : Nat → Nat) :
    ∀ (Rs : List (Nat × Nat)) (e : Nat), partsZ n w m ky r g Rs e =
      ((List.range Rs.length).map fun j =>
        (if partZ n w m ky r (rAt Rs j).1 (rAt Rs j).2 g = true then 1 else 0) *
          2 ^ (e + 40 * j)).sum
  | [], e => rfl
  | (R, Ri) :: Rs, e => by
    have hc : partsZ n w m ky r g ((R, Ri) :: Rs) e =
        Nat.add (nIf(partZ n w m ky r R Ri g, Nat.shiftLeft (nat_lit 1) e, nat_lit 0))
          (partsZ n w m ky r g Rs (Nat.add e (nat_lit 40))) := rfl
    rw [hc, partsZ_eq n w m ky r g Rs, nIf_eq', shl_one, List.length_cons]
    refine Eq.trans ?_ (split_head (fun j => if partZ n w m ky r (rAt ((R, Ri) :: Rs) j).1
      (rAt ((R, Ri) :: Rs) j).2 g = true then 1 else 0) Rs.length e
      (if partZ n w m ky r R Ri g = true then 1 else 0) rfl)
    simp only [Nat.add_eq]
    refine congrArg₂ (· + ·) ?_ rfl
    split <;> simp

theorem cntZ_eq (n w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat) (s : Nat) :
    cntZ n w m ky r Rs g s = s + dsum (cfld n w m ky r Rs g) (2 + 2 * Rs.length) := by
  rw [dsum_split]
  simp only [cfld, flds_zero, flds_one, flds_even, flds_odd]
  unfold cntZ
  rw [memsZ_eq, partsZ_eq]
  cases h2 : powId n g 2 <;> cases h1 : powId n g 1 <;> cases hk : powId n g ky <;>
    simp <;> omega

private theorem foldl_add (g : Nat → Nat → Nat) (hg : ∀ k s, g k s = s + g k 0) :
    ∀ (L : List Nat) (s : Nat), L.foldl (fun s i => g i s) s = s + (L.map fun i => g i 0).sum
  | [], s => by simp
  | i :: L, s => by
    rw [List.foldl_cons, foldl_add g hg L, hg i s, List.map_cons, List.sum_cons]
    omega

theorem foldUp_add {c : Nat} (g : Nat → Nat → Nat) (hg : ∀ k s, g k s = s + g k 0) (s : Nat) :
    foldUp c g s = s + ((List.range c).map fun k => g k 0).sum := by
  rw [foldUp_eq]
  exact foldl_add g hg _ s

@[expose] noncomputable def raw3 (w m h t3 t4 : Nat) : Nat → Nat :=
  fun x => pg w m h (pg w m t3 (pg w m t4 x))

theorem lastZ_eq (n w m nw pm ky r : Nat) (Rs : List (Nat × Nat)) (L3 L4 h s : Nat) :
    lastZ n w m nw pm ky r Rs L3 L4 h s = s + ((List.range (lcnt L3)).map fun k3 =>
      ((List.range (lcnt L4)).map fun k4 =>
        cntZ n w m ky r Rs (raw3 w m h (ltr nw pm L3 k3) (ltr nw pm L4 k4)) 0).sum).sum := by
  have h4 : ∀ (g : Nat → Nat) (s : Nat), cntZ n w m ky r Rs g s = s + cntZ n w m ky r Rs g 0 :=
    fun g s => by rw [cntZ_eq, cntZ_eq _ _ _ _ _ _ _ 0, Nat.zero_add]
  unfold lastZ
  simp only [strictN_eq]
  rw [foldUp_add]
  · refine congrArg (s + ·) (congrArg List.sum (List.map_congr_left fun k3 _ => ?_))
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k4 s
      exact h4 _ s
  · intro k3 s
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k4 s
      exact h4 _ s
    · intro k4 s
      exact h4 _ s

theorem sliceZ_eq (n w m nw pm ky r : Nat) (Rs : List (Nat × Nat)) (L0 L1 L2 L3 L4 sub i : Nat) :
    sliceZ n w m nw pm ky r Rs L0 L1 L2 L3 L4 sub i =
      ((List.range (lcnt L1 / sub)).map fun j => ((List.range (lcnt L2)).map fun k2 =>
        lastZ n w m nw pm ky r Rs L3 L4 (pcomp n w m (pcomp n w m (ltr nw pm L0 (i / sub))
          (ltr nw pm L1 (lcnt L1 / sub * (i % sub) + j))) (ltr nw pm L2 k2)) 0).sum).sum := by
  have hl : ∀ h s, lastZ n w m nw pm ky r Rs L3 L4 h s = s + lastZ n w m nw pm ky r Rs L3 L4 h 0 :=
    fun h s => by rw [lastZ_eq, lastZ_eq _ _ _ _ _ _ _ _ _ _ _ 0, Nat.zero_add]
  unfold sliceZ
  simp only [strictN_eq]
  rw [foldUp_add, Nat.zero_add]
  · refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
    rw [foldUp_add, Nat.zero_add]
    · rfl
    · intro k2 s
      exact hl _ s
  · intro j s
    rw [foldUp_add, foldUp_add, Nat.zero_add]
    · intro k2 s
      exact hl _ s
    · intro k2 s
      exact hl _ s

private theorem mc_recBS_ok {n w : Nat} {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) :
    RecOK n w s.pts.length (fun k => s.pts.getD k 0) (posBS w s)
      (fun k => if k < s.pts.length then enc w (BS.trans F s k) n else 0)
      (fun k => if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) := by
  obtain ⟨hpos, hle, -, hlt, hperm⟩ := hs
  have hnw : n < 2 ^ w := by omega
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · intro k _
    change s.pts.getD k 0 < 2 ^ w
    by_cases h : k < s.pts.length
    · rw [← List.getElem_eq_getD 0 (h := h)]
      exact Nat.lt_trans (hlt _ (List.getElem_mem h)) hnw
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact Nat.two_pow_pos w
  · intro x _
    change posBS w s x < 2 ^ w
    unfold posBS
    split
    · rename_i hx
      have := List.idxOf_lt_length_iff.mpr hx
      omega
    · rw [mask_eq]
      have := Nat.two_pow_pos w
      omega
  · intro k _
    change (if k < s.pts.length then enc w (BS.trans F s k) n else 0) < 2 ^ (n * w)
    split
    · rename_i hk
      rw [Nat.mul_comm n w]
      exact enc_lt fun i hi => Nat.lt_trans ((hperm k hk).1 i hi) hnw
    · exact Nat.two_pow_pos _
  · intro k _
    change (if k < s.pts.length then enc w (finv n (BS.trans F s k)) n else 0) < 2 ^ (n * w)
    split
    · rw [Nat.mul_comm n w]
      exact enc_lt fun i hi => Nat.lt_trans (finv_lt (by omega) _ _) hnw
    · exact Nat.two_pow_pos _

theorem ltr_recBS {n w : Nat} {F : Nat → Nat → Nat} {s : BS} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hs : GoodBS n F s) (V : Nat) {k : Nat} (hk : k < s.pts.length) :
    ltr (n * w) (mask (n * w)) (recBS n w F s V) k = enc w (BS.trans F s k) n := by
  have h : ltr (n * w) (mask (n * w)) (recBS n w F s V) k =
      if k < s.pts.length then enc w (BS.trans F s k) n else 0 :=
    ltr_recOf (mc_recBS_ok hn16 hw hs) (Nat.lt_of_lt_of_le hk hs.2.1)
  rw [if_pos hk] at h
  exact h

theorem pcomp_encode {n w : Nat} (hn32 : n < 2 ^ 32) (hw : n < 2 ^ w) {p q : Nat → Nat}
    (hp : ∀ x < n, p x < n) (hq : ∀ x < n, q x < n) :
    pcomp n w (mask w) (enc w p n) (enc w q n) = enc w (fun x => p (q x)) n := by
  have hq' : ∀ j < n, q j < 2 ^ w := fun j hj => Nat.lt_trans (hq j hj) hw
  have hp' : ∀ j < n, p j < 2 ^ w := fun j hj => Nat.lt_trans (hp j hj) hw
  rw [pcomp_eq hn32]
  refine enc_congr fun i hi => ?_
  rw [fd_enc hq' hi, fd_enc hp' (hq i hi)]

theorem pg_encode {n w : Nat} (hw : n < 2 ^ w) {p : Nat → Nat} (hp : ∀ x < n, p x < n) {x : Nat}
    (hx : x < n) : pg w (mask w) (enc w p n) x = p x := by
  rw [pg_eq]
  exact fd_enc (fun j hj => Nat.lt_trans (hp j hj) hw) hx

@[expose] def cfn {n : Nat} (σ : Equiv.Perm (Fin n)) : Nat → Nat :=
  fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x

theorem cfn_lt {n : Nat} (σ : Equiv.Perm (Fin n)) {x : Nat} (hx : x < n) : cfn σ x < n := by
  simp only [cfn, dif_pos hx]
  exact (σ ⟨x, hx⟩).isLt

theorem cfn_apply {n : Nat} (σ : Equiv.Perm (Fin n)) (x : Fin n) : cfn σ x = σ x := by
  simp [cfn]

theorem allFrom_iff (p : Nat → Bool) : ∀ (c lo : Nat),
    allFrom p c lo = true ↔ ∀ i < c, p (lo + i) = true
  | 0, lo => by simp [allFrom]
  | c + 1, lo => by
    change bAnd(p lo, allFrom p c (Nat.succ lo)) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, allFrom_iff p c]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := h1 i (by omega)
        rwa [show Nat.succ lo + i = lo + (i + 1) by omega] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      rw [show Nat.succ lo + i = lo + (i + 1) by omega]
      exact h (i + 1) (by omega)

theorem itr_succ (f : Nat → Nat) (k i : Nat) : MEnum.itr f (k + 1) i = f (MEnum.itr f k i) := rfl

theorem itr_congr {n : Nat} {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) (k : Nat) {i : Nat} (hi : i < n) :
    MEnum.itr g k i = MEnum.itr g' k i ∧ MEnum.itr g k i < n := by
  induction k with
  | zero => exact ⟨rfl, hi⟩
  | succ k ih =>
    rw [itr_succ, itr_succ, ← ih.1, h _ ih.2]
    exact ⟨rfl, by rw [← h _ ih.2]; exact hg _ ih.2⟩

theorem powId_congr {n : Nat} {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) (k : Nat) : powId n g k = powId n g' k := by
  apply Bool.eq_iff_iff.2
  unfold powId
  rw [allFrom_iff, allFrom_iff]
  refine forall_congr' fun i => imp_congr_right fun hi => ?_
  rw [Nat.zero_add, (itr_congr h hg k hi).1]

theorem itr_cfn {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Nat) (i : Fin n) :
    MEnum.itr (cfn σ) k i = ((σ ^ k) i : Nat) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [itr_succ, ih, pow_succ', Equiv.Perm.mul_apply, cfn_apply]

theorem powId_cfn {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Nat) :
    powId n (cfn σ) k = true ↔ σ ^ k = 1 := by
  unfold powId
  rw [allFrom_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have := h i.val i.isLt
    rw [Nat.zero_add, Nat.beq_eq, itr_cfn σ k i] at this
    simpa using this
  · intro h i hi
    rw [Nat.zero_add, Nat.beq_eq, itr_cfn σ k ⟨i, hi⟩, h]
    rfl

@[expose] def rsum (c : Nat) (f : Nat → Nat) : Nat := ((List.range c).map f).sum

theorem rsum_congr {c : Nat} {f g : Nat → Nat} (h : ∀ k < c, f k = g k) : rsum c f = rsum c g :=
  congrArg List.sum (List.map_congr_left fun k hk => h k (List.mem_range.1 hk))

theorem rsum_le {c M : Nat} {f : Nat → Nat} (h : ∀ k < c, f k ≤ M) : rsum c f ≤ c * M := by
  unfold rsum
  induction c with
  | zero => simp
  | succ c ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      Nat.succ_mul]
    have := ih fun k hk => h k (by omega)
    have := h c (by omega)
    omega

theorem rsum_add (a b : Nat) (f : Nat → Nat) : rsum (a + b) f = rsum a f + rsum b (fun k => f (a + k)) := by
  unfold rsum
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl

theorem rsum_slices (c0 sub q : Nat) (G : Nat → Nat → Nat) :
    rsum (c0 * sub) (fun i => rsum q fun j => G (i / sub) (q * (i % sub) + j)) =
      rsum c0 fun k0 => rsum (q * sub) fun k1 => G k0 k1 := by
  have inner : ∀ k0 u, u ≤ sub → rsum u (fun u' => rsum q fun j => G k0 (q * u' + j)) =
      rsum (q * u) fun k1 => G k0 k1 := by
    intro k0 u _
    induction u with
    | zero => simp [rsum]
    | succ u ih =>
      rw [rsum_add, ih (by omega), Nat.mul_succ, rsum_add]
      simp [rsum]
  induction c0 with
  | zero => simp [rsum]
  | succ c0 ih =>
    rw [Nat.succ_mul, rsum_add, ih, rsum_add]
    congr 1
    have h1 : (rsum 1 fun k => rsum (q * sub) fun k1 => G (c0 + k) k1) =
        rsum (q * sub) fun k1 => G c0 k1 := by simp [rsum]
    rw [h1, ← inner c0 sub le_rfl]
    refine rsum_congr fun u hu => rsum_congr fun j _ => ?_
    have hpos : 0 < sub := by omega
    have hd : (c0 * sub + u) / sub = c0 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hu, Nat.zero_add]
    have hm : (c0 * sub + u) % sub = u := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
    rw [hd, hm]

theorem sum_map_eq_rsum {α : Type*} (L : List α) (φ : α → Nat) (d : α) :
    (L.map φ).sum = rsum L.length fun i => φ (L.getD i d) := by
  unfold rsum
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem sum_products_cons {M : Type*} [Monoid M] (c : Nat) (τ : Nat → M) (Ts : List (List M))
    (φ : M → Nat) :
    ((products (((List.range c).map τ) :: Ts)).map φ).sum =
      rsum c fun k => ((products Ts).map fun x => φ (τ k * x)).sum := by
  rw [products, sum_flatMap, List.map_map]
  unfold rsum
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp [List.map_map, Function.comp_def]

theorem rsum_dsum (c : Nat) (b : Nat → Nat → Nat) (N : Nat) :
    rsum c (fun k => dsum (b k) N) = dsum (fun f => rsum c fun k => b k f) N :=
  sum_dsum (List.range c) b N

theorem cfld_le_one (n w m ky r : Nat) (Rs : List (Nat × Nat)) (g : Nat → Nat) (f : Nat) :
    cfld n w m ky r Rs g f ≤ 1 := by
  unfold cfld flds
  dsimp only
  split_ifs <;> omega

section Five

variable {n w : Nat} {F : Nat → Nat → Nat} {s : Nat → BS} {V : Nat → Nat}

@[expose] noncomputable def raw5 (n w : Nat) (F : Nat → Nat → Nat) (s : Nat → BS) (V : Nat → Nat)
    (k0 k1 k2 k3 k4 : Nat) : Nat → Nat :=
  raw3 w (mask w) (pcomp n w (mask w) (pcomp n w (mask w)
    (ltr (n * w) (mask (n * w)) (recBS n w F (s 0) (V 0)) k0)
    (ltr (n * w) (mask (n * w)) (recBS n w F (s 1) (V 1)) k1))
    (ltr (n * w) (mask (n * w)) (recBS n w F (s 2) (V 2)) k2))
    (ltr (n * w) (mask (n * w)) (recBS n w F (s 3) (V 3)) k3)
    (ltr (n * w) (mask (n * w)) (recBS n w F (s 4) (V 4)) k4)

@[expose] noncomputable def tau (n : Nat) (F : Nat → Nat → Nat) (s : Nat → BS) (i k : Nat) :
    Equiv.Perm (Fin n) :=
  permOf n (BS.trans F (s i) k)

theorem raw5_eq (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < (s 0).pts.length) (h1 : k1 < (s 1).pts.length)
    (h2 : k2 < (s 2).pts.length) (h3 : k3 < (s 3).pts.length) (h4 : k4 < (s 4).pts.length) :
    ∀ x < n, raw5 n w F s V k0 k1 k2 k3 k4 x =
      cfn (tau n F s 0 k0 * (tau n F s 1 k1 * (tau n F s 2 k2 * (tau n F s 3 k3 *
        (tau n F s 4 k4 * 1))))) x := by
  intro x hx
  have hn32 : n < 2 ^ 32 := by
    have : 2 ^ 16 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by decide)
    omega
  have hwn : n < 2 ^ w := by omega
  have p0 := (hg 0).2.2.2.2 k0 h0
  have p1 := (hg 1).2.2.2.2 k1 h1
  have p2 := (hg 2).2.2.2.2 k2 h2
  have p3 := (hg 3).2.2.2.2 k3 h3
  have p4 := (hg 4).2.2.2.2 k4 h4
  unfold raw5 raw3
  rw [ltr_recBS hn16 hw (hg 0) _ h0, ltr_recBS hn16 hw (hg 1) _ h1, ltr_recBS hn16 hw (hg 2) _ h2,
    ltr_recBS hn16 hw (hg 3) _ h3, ltr_recBS hn16 hw (hg 4) _ h4,
    pcomp_encode hn32 hwn p0.1 p1.1, pcomp_encode hn32 hwn (p0.comp p1).1 p2.1,
    pg_encode hwn p4.1 hx, pg_encode hwn p3.1 (p4.1 x hx), pg_encode hwn (p0.comp (p1.comp p2)).1
      (p3.1 _ (p4.1 x hx))]
  simp only [cfn, dif_pos hx, mul_one, Equiv.Perm.mul_apply, tau]
  rw [permOf_apply p0, permOf_apply p1, permOf_apply p2, permOf_apply p3, permOf_apply p4]

theorem raw5_lt (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    {k0 k1 k2 k3 k4 : Nat} (h0 : k0 < (s 0).pts.length) (h1 : k1 < (s 1).pts.length)
    (h2 : k2 < (s 2).pts.length) (h3 : k3 < (s 3).pts.length) (h4 : k4 < (s 4).pts.length) :
    ∀ x < n, raw5 n w F s V k0 k1 k2 k3 k4 x < n := by
  intro x hx
  rw [raw5_eq hn16 hw hg h0 h1 h2 h3 h4 x hx]
  exact cfn_lt _ hx

theorem sliceZ_five (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    (ky r : Nat) (Rs : List (Nat × Nat)) (sub i : Nat) :
    sliceZ n w (mask w) (n * w) (mask (n * w)) ky r Rs (recBS n w F (s 0) (V 0))
        (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2)) (recBS n w F (s 3) (V 3))
        (recBS n w F (s 4) (V 4)) sub i =
      rsum ((s 1).pts.length / sub) fun j => rsum (s 2).pts.length fun k2 =>
        rsum (s 3).pts.length fun k3 => rsum (s 4).pts.length fun k4 =>
          cntZ n w (mask w) ky r Rs (raw5 n w F s V (i / sub)
            ((s 1).pts.length / sub * (i % sub) + j) k2 k3 k4) 0 := by
  rw [sliceZ_eq]
  simp only [lastZ_eq, Nat.zero_add, lcnt_recBS hn16 hw (hg _)]
  rfl

theorem cntSum_five (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w) (hg : ∀ i, GoodBS n F (s i))
    (ky r : Nat) (Rs : List (Nat × Nat)) {sub : Nat} (hsub : 0 < sub ∧ (s 1).pts.length % sub = 0)
    (hsz : (s 1).pts.length * (s 2).pts.length * (s 3).pts.length * (s 4).pts.length < 2 ^ 20)
    {CS : List Nat} (hCS : CS.length = (s 0).pts.length * sub)
    (hc : ∀ i < (s 0).pts.length * sub, sliceZ n w (mask w) (n * w) (mask (n * w)) ky r Rs
      (recBS n w F (s 0) (V 0)) (recBS n w F (s 1) (V 1)) (recBS n w F (s 2) (V 2))
      (recBS n w F (s 3) (V 3)) (recBS n w F (s 4) (V 4)) sub i = CS.getD i 0)
    {P : Nat → Prop}
    (hP : ∀ f, P f → ∀ g g' : Nat → Nat, (∀ x < n, g x = g' x) → (∀ x < n, g x < n) →
      cfld n w (mask w) ky r Rs g f = cfld n w (mask w) ky r Rs g' f)
    {f : Nat} (hf : f < 2 + 2 * Rs.length) (hPf : P f) :
    cntSum CS f = ((products ((List.range 5).map fun i =>
      (List.range (s i).pts.length).map (tau n F s i))).map fun σ =>
        cfld n w (mask w) ky r Rs (cfn σ) f).sum := by
  set c : Nat → Nat := fun i => (s i).pts.length with hcdef
  set N := 2 + 2 * Rs.length
  set q := c 1 / sub
  have hq : q * sub = c 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hsub.2)
  have hqle : q ≤ c 1 := Nat.div_le_self _ _
  have hdig : ∀ i < c 0 * sub, (CS.getD i 0 >>> (20 * f)) % 2 ^ 20 =
      rsum q fun j => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
        cfld n w (mask w) ky r Rs (raw5 n w F s V (i / sub) (q * (i % sub) + j) k2 k3 k4) f := by
    intro i hi
    rw [← hc i hi, sliceZ_five hn16 hw hg]
    simp only [cntZ_eq, Nat.zero_add, rsum_dsum]
    rw [Nat.shiftRight_eq_div_pow, dsum_digit _ f N, if_pos hf]
    intro f'
    have hb : (rsum q fun j => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
        cfld n w (mask w) ky r Rs (raw5 n w F s V (i / sub) (q * (i % sub) + j) k2 k3 k4) f') ≤
        q * (c 2 * (c 3 * (c 4 * 1))) :=
      rsum_le fun j _ => rsum_le fun k2 _ => rsum_le fun k3 _ => rsum_le fun k4 _ =>
        cfld_le_one _ _ _ _ _ _ _ _
    have h1 : q * (c 2 * (c 3 * (c 4 * 1))) ≤ c 1 * (c 2 * (c 3 * (c 4 * 1))) :=
      Nat.mul_le_mul_right _ hqle
    have h2 : c 1 * (c 2 * (c 3 * (c 4 * 1))) < 2 ^ 20 := by
      simp only [Nat.mul_one, ← Nat.mul_assoc]
      exact hsz
    exact lt_of_le_of_lt (hb.trans h1) h2
  unfold cntSum
  rw [sum_map_eq_rsum CS _ 0, hCS]
  rw [rsum_congr hdig, rsum_slices (c 0) sub q
    (fun k0 k1 => rsum (c 2) fun k2 => rsum (c 3) fun k3 => rsum (c 4) fun k4 =>
      cfld n w (mask w) ky r Rs (raw5 n w F s V k0 k1 k2 k3 k4) f), hq]
  have hT : (List.range 5).map (fun i => (List.range (s i).pts.length).map (tau n F s i)) =
      [(List.range (c 0)).map (tau n F s 0), (List.range (c 1)).map (tau n F s 1),
        (List.range (c 2)).map (tau n F s 2), (List.range (c 3)).map (tau n F s 3),
        (List.range (c 4)).map (tau n F s 4)] := rfl
  rw [hT]
  simp only [sum_products_cons]
  refine rsum_congr fun k0 h0 => rsum_congr fun k1 h1 => rsum_congr fun k2 h2 =>
    rsum_congr fun k3 h3 => rsum_congr fun k4 h4 => ?_
  rw [hP f hPf _ _ (raw5_eq hn16 hw hg h0 h1 h2 h3 h4) (raw5_lt hn16 hw hg h0 h1 h2 h3 h4)]
  rfl

end Five

theorem partZ_congr {n w m ky r R Ri : Nat} (hR : ∀ x < n, pg w m R x < n)
    (hRi : ∀ x < n, pg w m Ri x < n) {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) : partZ n w m ky r R Ri g = partZ n w m ky r R Ri g' := by
  have h1 : ∀ x < n, pg w m R (g x) = pg w m R (g' x) := fun x hx => by rw [h x hx]
  have h1' : ∀ x < n, pg w m R (g x) < n := fun x hx => hR _ (hg x hx)
  have hi := fun i (hi : i < n) => itr_congr h hg (Nat.sub ky 1) hi
  have h2 : ∀ x < n, pg w m R (g (pg w m Ri (MEnum.itr g (Nat.sub ky 1) x))) =
      pg w m R (g' (pg w m Ri (MEnum.itr g' (Nat.sub ky 1) x))) := fun x hx => by
    rw [← (hi x hx).1, h _ (hRi _ (hi x hx).2)]
  have h2' : ∀ x < n, pg w m R (g (pg w m Ri (MEnum.itr g (Nat.sub ky 1) x))) < n :=
    fun x hx => hR _ (hg _ (hRi _ (hi x hx).2))
  unfold partZ ordPZ ord6Z
  rw [powId_congr h1 h1', powId_congr h1 h1', powId_congr h2 h2', powId_congr h2 h2',
    powId_congr h2 h2', powId_congr h2 h2']

theorem allFrom_congr {n : Nat} {p q : Nat → Bool} (h : ∀ i < n, p i = q i) :
    allFrom p n 0 = allFrom q n 0 := by
  apply Bool.eq_iff_iff.2
  rw [allFrom_iff, allFrom_iff]
  exact forall_congr' fun i => imp_congr_right fun hi => by rw [Nat.zero_add, h i hi]

theorem cfld_congr_mem {n w m ky r : Nat} {Rs : List (Nat × Nat)} {f : Nat}
    (hf : f = 0 ∨ f = 1 ∨ (3 ≤ f ∧ f % 2 = 1)) {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) : cfld n w m ky r Rs g f = cfld n w m ky r Rs g' f := by
  have hp : ∀ k, powId n g k = powId n g' k := powId_congr h hg
  have ha : ∀ R, allFrom (fun i => Nat.beq (g i) (pg w m R i)) n 0 =
      allFrom (fun i => Nat.beq (g' i) (pg w m R i)) n 0 := fun R =>
    allFrom_congr fun i hi => by rw [h i hi]
  unfold cfld flds
  rcases hf with rfl | rfl | hf
  · simp only [if_true, hp]
  · simp only [if_true, if_false, hp, one_ne_zero]
  · have h0 : f ≠ 0 := by omega
    have h1 : f ≠ 1 := by omega
    have h2 : f % 2 ≠ 0 := by omega
    simp only [h0, h1, h2, ite_false, hp, ha]

theorem cfld_congr {n w m ky r : Nat} {Rs : List (Nat × Nat)}
    (hR : ∀ j, ∀ x < n, pg w m (rAt Rs j).1 x < n ∧ pg w m (rAt Rs j).2 x < n) (f : Nat)
    {g g' : Nat → Nat} (h : ∀ x < n, g x = g' x)
    (hg : ∀ x < n, g x < n) : cfld n w m ky r Rs g f = cfld n w m ky r Rs g' f := by
  have hp : ∀ k, powId n g k = powId n g' k := powId_congr h hg
  have ha : ∀ R, allFrom (fun i => Nat.beq (g i) (pg w m R i)) n 0 =
      allFrom (fun i => Nat.beq (g' i) (pg w m R i)) n 0 := fun R =>
    allFrom_congr fun i hi => by rw [h i hi]
  have hz : ∀ j, partZ n w m ky r (rAt Rs j).1 (rAt Rs j).2 g =
      partZ n w m ky r (rAt Rs j).1 (rAt Rs j).2 g' := fun j =>
    partZ_congr (fun x hx => (hR j x hx).1) (fun x hx => (hR j x hx).2) h hg
  unfold cfld flds
  simp only [hp, ha, hz]

theorem orderOf_two_iff {n : Nat} (σ : Equiv.Perm (Fin n)) :
    (σ ^ 2 = 1 ∧ ¬ σ ^ 1 = 1) ↔ orderOf σ = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_one]

theorem orderOf_ky_iff {n ky : Nat} (hky : ky = 3 ∨ ky = 4) (σ : Equiv.Perm (Fin n)) :
    (¬ σ ^ 2 = 1 ∧ σ ^ ky = 1) ↔ orderOf σ = ky := by
  constructor
  · rintro ⟨h2, hk⟩
    have hd := orderOf_dvd_of_pow_eq_one hk
    have h2' : ¬ orderOf σ ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.1 h)
    generalize orderOf σ = o at hd h2' ⊢
    rcases hky with rfl | rfl
    · have hle := Nat.le_of_dvd (by decide) hd
      interval_cases o <;> omega
    · have hle := Nat.le_of_dvd (by decide) hd
      interval_cases o <;> omega
  · intro h
    refine ⟨fun h2 => ?_, h ▸ pow_orderOf_eq_one σ⟩
    have := Nat.le_of_dvd (by decide) (h ▸ orderOf_dvd_of_pow_eq_one h2)
    omega

theorem orderOf_prime_iff {n r : Nat} (hr : r.Prime) (τ : Equiv.Perm (Fin n)) :
    (τ ^ r = 1 ∧ ¬ τ ^ 1 = 1) ↔ orderOf τ = r := by
  have : Fact r.Prime := ⟨hr⟩
  rw [orderOf_eq_prime_iff, pow_one]

theorem orderOf_six_iff {n : Nat} (τ : Equiv.Perm (Fin n)) :
    (¬ τ ^ 1 = 1 ∧ ¬ τ ^ 2 = 1 ∧ ¬ τ ^ 3 = 1 ∧ τ ^ 6 = 1) ↔ orderOf τ = 6 := by
  constructor
  · rintro ⟨h1, h2, h3, h6⟩
    have hd := orderOf_dvd_of_pow_eq_one h6
    have n1 : ¬ orderOf τ ∣ 1 := fun h => h1 (orderOf_dvd_iff_pow_eq_one.1 h)
    have n2 : ¬ orderOf τ ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.1 h)
    have n3 : ¬ orderOf τ ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.1 h)
    generalize orderOf τ = o at hd n1 n2 n3 ⊢
    have hle := Nat.le_of_dvd (by decide) hd
    interval_cases o <;> omega
  · intro h
    have hk : ∀ k, τ ^ k = 1 → 6 ∣ k := fun k hk => h ▸ orderOf_dvd_of_pow_eq_one hk
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, h ▸ pow_orderOf_eq_one τ⟩
    · have := hk 1 e; omega
    · have := hk 2 e; omega
    · have := hk 3 e; omega

private theorem beq_cfn {n : Nat} (τ : Equiv.Perm (Fin n)) {g : Nat → Nat}
    (h : ∀ x : Fin n, g x = τ x) (k : Nat) : powId n g k = powId n (cfn τ) k :=
  powId_congr (fun x hx => by rw [h ⟨x, hx⟩]; simp [cfn, hx]) (fun x hx => by
    rw [h ⟨x, hx⟩]; exact (τ ⟨x, hx⟩).isLt) k

theorem powId_cfn_false {n : Nat} (σ : Equiv.Perm (Fin n)) (k : Nat) :
    powId n (cfn σ) k = false ↔ ¬ σ ^ k = 1 := by
  rw [← powId_cfn, Bool.not_eq_true]

theorem cfld_zero_cfn {n w m ky r : Nat} {Rs : List (Nat × Nat)} (σ : Equiv.Perm (Fin n)) :
    cfld n w m ky r Rs (cfn σ) 0 = if orderOf σ = 2 then 1 else 0 := by
  unfold cfld
  rw [flds_zero]
  refine if_congr ?_ rfl rfl
  rw [powId_cfn, powId_cfn_false]
  exact orderOf_two_iff σ

theorem cfld_one_cfn {n w m ky r : Nat} {Rs : List (Nat × Nat)} (hky : ky = 3 ∨ ky = 4)
    (σ : Equiv.Perm (Fin n)) :
    cfld n w m ky r Rs (cfn σ) 1 = if orderOf σ = ky then 1 else 0 := by
  unfold cfld
  rw [flds_one]
  refine if_congr ?_ rfl rfl
  rw [powId_cfn, powId_cfn_false]
  exact orderOf_ky_iff hky σ

theorem cfld_mem_cfn {n w m ky r : Nat} {Rs : List (Nat × Nat)} (σ : Equiv.Perm (Fin n))
    (j : Nat) : cfld n w m ky r Rs (cfn σ) (3 + 2 * j) =
      if orderOf σ = 2 ∧ ∀ x : Fin n, (σ x : Nat) = pg w m (rAt Rs j).1 x then 1 else 0 := by
  unfold cfld
  rw [flds_odd]
  have he : allFrom (fun i => Nat.beq (cfn σ i) (pg w m (rAt Rs j).1 i)) n 0 = true ↔
      ∀ x : Fin n, (σ x : Nat) = pg w m (rAt Rs j).1 x := by
    rw [allFrom_iff]
    constructor
    · intro h x
      have := h x.val x.isLt
      rw [Nat.zero_add, Nat.beq_eq, cfn_apply] at this
      exact this
    · intro h i hi
      rw [Nat.zero_add, Nat.beq_eq]
      have := h ⟨i, hi⟩
      rw [← cfn_apply] at this
      exact this
  refine if_congr ?_ rfl rfl
  rw [powId_cfn, powId_cfn_false, he, ← orderOf_two_iff, and_assoc]

theorem cfld_part_cfn {n w ky r R Ri : Nat} {Rs : List (Nat × Nat)} (hky : ky = 3 ∨ ky = 4)
    (hr : r.Prime) (σ ρ : Equiv.Perm (Fin n)) (j : Nat) (hj : rAt Rs j = (R, Ri))
    (pR : ∀ x : Fin n, pg w (mask w) R x = ρ x) (pRi : ∀ x : Fin n, pg w (mask w) Ri x = ρ⁻¹ x) :
    cfld n w (mask w) ky r Rs (cfn σ) (2 + 2 * j) =
      if orderOf σ = ky ∧ orderOf (ρ * σ) = r ∧ orderOf (ρ * σ * ρ⁻¹ * σ⁻¹) = 6 then 1 else 0 := by
  unfold cfld
  rw [flds_even, hj]
  dsimp only
  by_cases ho : orderOf σ = ky
  · have hk := (orderOf_ky_iff hky σ).2 ho
    have hinv : σ ^ (Nat.sub ky 1) = σ⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, show Nat.sub ky 1 + 1 = ky by
        change ky - 1 + 1 = ky; omega, hk.2]
    have h1 : ∀ x : Fin n, pg w (mask w) R (cfn σ x) = (ρ * σ) x := fun x => by
      rw [cfn_apply, pR, Equiv.Perm.mul_apply]
    have h2 : ∀ x : Fin n, pg w (mask w) R (cfn σ (pg w (mask w) Ri
        (MEnum.itr (cfn σ) (Nat.sub ky 1) x))) = (ρ * σ * ρ⁻¹ * σ⁻¹) x := fun x => by
      rw [itr_cfn, hinv, pRi, cfn_apply, pR]
      simp only [Equiv.Perm.mul_apply]
    have hp2 : powId n (cfn σ) 2 = false := (powId_cfn_false σ 2).2 hk.1
    have hpk : powId n (cfn σ) ky = true := (powId_cfn σ ky).2 hk.2
    have hz : partZ n w (mask w) ky r R Ri (cfn σ) = true ↔
        orderOf (ρ * σ) = r ∧ orderOf (ρ * σ * ρ⁻¹ * σ⁻¹) = 6 := by
      unfold partZ ordPZ ord6Z
      simp only [beq_cfn (ρ * σ) (g := fun i => pg w (mask w) R (cfn σ i)) h1,
        beq_cfn _ (g := fun i => pg w (mask w) R (cfn σ (pg w (mask w) Ri
          (MEnum.itr (cfn σ) (Nat.sub ky 1) i)))) h2,
        bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', powId_cfn, powId_cfn_false]
      rw [← orderOf_prime_iff hr, ← orderOf_six_iff]
    refine if_congr ?_ rfl rfl
    rw [hp2, hpk, hz]
    simp only [ho, true_and]
  · have hn : ¬ (powId n (cfn σ) 2 = false ∧ powId n (cfn σ) ky = true) := by
      rintro ⟨h2, hk⟩
      exact ho ((orderOf_ky_iff hky σ).1 ⟨(powId_cfn_false σ 2).1 h2, (powId_cfn σ ky).1 hk⟩)
    rw [if_neg (fun h => hn ⟨h.1, h.2.1⟩), if_neg (fun h => ho h.1)]

end CFSG.KS.PK

end
