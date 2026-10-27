module

public import Certificates.Data.Kernel.LocalQT.SlpP
public import CFSG.Certificates.Kernel.LocalQTTcPSound
import CFSG.Certificates.Kernel.LocalQTTcKSound

public section

namespace CFSG.KC.LQT.SP

open CFSG.KS.Raw CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.J2Excl CFSG.KC.LQT.TC
  CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TCK CFSG.Monster.B.Co2.Native

private theorem clogR_le (n : ℕ) : ∀ k, CFSG.KS.PF.clogR n k ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have e : CFSG.KS.PF.clogR n (k + 1) = nIf(Nat.blt (Nat.shiftLeft (nat_lit 1)
        (CFSG.KS.PF.clogR n k)) n, Nat.succ (CFSG.KS.PF.clogR n k), CFSG.KS.PF.clogR n k) := rfl
    have ih := clogR_le n k
    rw [e]
    generalize CFSG.KS.PF.clogR n k = c at ih ⊢
    cases Nat.blt (Nat.shiftLeft 1 c) n
    · exact Nat.le_succ_of_le ih
    · exact Nat.succ_le_succ ih

private theorem idK_small {n w : ℕ} (h : idK n w (mask w) = true) : n < 2 ^ 32 := by
  by_contra hcon
  have hn : 2 ^ 24 < n := by
    have : (2 : ℕ) ^ 32 = 2 ^ 24 * 256 := by norm_num
    omega
  unfold idK at h
  have hh := CFSG.KS.Raw.Orb.allN_iff.1 h
  have hf : ∀ x < n, x < 2 ^ w := fun x hx => by
    have := Nat.eq_of_beq_eq_true (hh x hx)
    rw [← this]
    exact CFSG.KS.PF.pg_lt w _ x
  have hfl := CFSG.KS.PF.fld_pmkT n w (fun i => i) hf (clog n) 0
  have e : pidn n w = pmkT n w (fun i => i) (clog n) 0 := by
    unfold pidn pmk
    rw [CFSG.KS.PF.strictN_eqP]
  have hc : clog n ≤ 24 := clogR_le n 24
  have hlt : ¬ (2 ^ 24 < 2 ^ clog n) := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
    omega
  have hpg := CFSG.KS.PF.pg_of_fld (i := 2 ^ 24) (e ▸ hfl) (by simp only [hlt, ↓reduceIte]; exact Nat.two_pow_pos w)
  have h24 := Nat.eq_of_beq_eq_true (hh (2 ^ 24) hn)
  simp only [hlt, ↓reduceIte] at hpg
  rw [hpg] at h24
  exact absurd h24 (by norm_num)


private theorem lenPr_eq (L : List (ℤ × ℤ)) : lenPr L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Nat.succ (lenPr L) = _
    rw [ih]
    rfl

private theorem appPr_eq (L M : List (ℤ × ℤ)) : appPr L M = L ++ M := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change List.cons x (appPr L M) = _
    rw [ih]
    rfl

private theorem revPr_eq (L : List (ℤ × ℤ)) : ∀ M, revPr L M = L.reverse ++ M := by
  induction L with
  | nil => intro M; rfl
  | cons x L ih =>
    intro M
    change revPr L (List.cons x M) = _
    rw [ih]
    simp

private theorem getPr_eq (L : List (ℤ × ℤ)) : ∀ k, getPr L k = L.getD k (Int.ofNat 0, Int.ofNat 0) := by
  induction L with
  | nil => intro k; rfl
  | cons x L ih =>
    intro k
    cases k with
    | zero => rfl
    | succ k =>
      change getPr L k = _
      rw [ih]
      rfl

private theorem getN_eq (l : List ℕ) (k : ℕ) : getN l k = l.getD k 0 := getTc_eq 0 l k

private theorem inRegs_eq (g : ℕ) : inRegs g = (List.range g).reverse := by
  induction g with
  | zero => rfl
  | succ g ih =>
    change List.cons g (inRegs g) = _
    rw [ih, List.range_succ]
    simp

private def RR (n : ℕ) (v : PArr) (g : Equiv.Perm (Fin n)) : Prop :=
  PRep n v g ∧ v.1.size = n ∧ v.2.size = n

private theorem rr_id {n : ℕ} : RR n (pId n) 1 :=
  ⟨pRep_id, by simp [pId, idA], by simp [pId, idA]⟩

private theorem RR.mul {n : ℕ} {x y : PArr} {g h : Equiv.Perm (Fin n)} (hx : RR n x g)
    (hy : RR n y h) : RR n (pMul n x y) (g * h) :=
  ⟨hx.1.mul hy.1, by simp [pMul, compA], by simp [pMul, compA]⟩

private theorem RR.inv {n : ℕ} {x : PArr} {g : Equiv.Perm (Fin n)} (hx : RR n x g) :
    RR n (pInv x) g⁻¹ :=
  ⟨hx.1.inv, hx.2.2, hx.2.1⟩

private theorem unpack_size' (n w P : ℕ) : (unpack n w P).size = n := by
  simp [unpack]

private theorem rr_unpack {n w : ℕ} {P Q : ℕ} (h : permOK n w (mask w) (n * w) P Q = true) :
    ∃ g : Equiv.Perm (Fin n), RR n (unpack n w P, unpack n w Q) g ∧ RP n w P g ∧
      RP n w Q g⁻¹ := by
  obtain ⟨g, h1, h2, h3⟩ := of_permOK h
  exact ⟨g, ⟨h1, unpack_size' n w P, unpack_size' n w Q⟩, h2, h3⟩

private theorem arr_eq {n : ℕ} {a b : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ha : CFSG.Monster.B.Co2.Rep n a g) (hb : CFSG.Monster.B.Co2.Rep n b g) (sa : a.size = n) (sb : b.size = n) : a = b := by
  apply Array.ext
  · omega
  · intro i h1 h2
    have hi : i < n := by omega
    have := (ha.apply hi).trans (hb.apply hi).symm
    rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

private theorem rp_unique {n w : ℕ} {P : ℕ} {g h : Equiv.Perm (Fin n)} (h1 : RP n w P g)
    (h2 : RP n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

open scoped Classical in
private noncomputable def permOfP (n w P : ℕ) : Equiv.Perm (Fin n) :=
  if h : ∃ g, RP n w P g then h.choose else 1

private theorem permOfP_spec {n w P : ℕ} (h : ∃ g, RP n w P g) : RP n w P (permOfP n w P) := by
  unfold permOfP
  rw [dif_pos h]
  exact h.choose_spec

private theorem permOfP_eq {n w P : ℕ} {g : Equiv.Perm (Fin n)} (h : RP n w P g) :
    permOfP n w P = g :=
  rp_unique (permOfP_spec ⟨g, h⟩) h

private def rp {n : ℕ} (perm : ℕ → Equiv.Perm (Fin n)) : ℤ → Equiv.Perm (Fin n)
  | Int.ofNat 0 => 1
  | Int.ofNat (m + 1) => perm m
  | Int.negSucc m => (perm m)⁻¹

private def pa (idn : ℕ) (X XI : ℕ → ℕ) : ℤ → ℕ × ℕ
  | Int.ofNat 0 => (idn, idn)
  | Int.ofNat (m + 1) => (X m, XI m)
  | Int.negSucc m => (XI m, X m)

private theorem refSP_eq (idn : ℕ) (X XI : ℕ → ℕ) (z : ℤ) (k : ℕ → ℕ → Bool) :
    refSP idn X XI z k = k (pa idn X XI z).1 (pa idn X XI z).2 := by
  rcases z with (_ | m) | m
  · rfl
  · rfl
  · rfl

private theorem rp_neg {n : ℕ} (perm : ℕ → Equiv.Perm (Fin n)) (g : ℤ) :
    rp perm (Int.neg g) = (rp perm g)⁻¹ := by
  rcases g with (_ | m) | m
  · simp [rp, Int.neg, Int.negOfNat]
  · change rp perm (Int.negSucc m) = _
    rfl
  · change rp perm (Int.ofNat (m + 1)) = _
    simp [rp]

private def letOK (g : ℕ) : ℤ → Prop
  | Int.ofNat m => m ≤ g
  | Int.negSucc m => m < g

private theorem letter_gen {n : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {gens : List PArr}
    (hg : ∀ k (hk : k < gens.length), RR n gens[k] (perm k)) {z : ℤ}
    (hz : letOK gens.length z) : RR n (pLetter n gens z) (rp perm z) := by
  rcases z with (_ | j) | k
  · simpa [pLetter, rp] using (rr_id (n := n))
  · rw [pLetter_pos]
    have hj : j < gens.length := hz
    rw [List.getD_eq_getElem _ _ hj]
    exact hg j hj
  · rw [pLetter_neg]
    have hk : k < gens.length := hz
    rw [List.getD_eq_getElem _ _ hk]
    exact (hg k hk).inv

private theorem regRef_pos_lt (regs : List ℕ) (len j : ℕ) (h : j < len) :
    regRef regs len (Int.ofNat (j + 1)) = Int.ofNat (getN regs (len - j - 1) + 1) := by
  have hb : Nat.blt j len = true := Nat.blt_eq.mpr h
  show Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
    (Int.ofNat (Nat.succ (getN regs (Nat.sub (Nat.sub len j) 1)))) (Nat.blt j len) = _
  rw [hb]
  try rfl

private theorem regRef_pos_ge (regs : List ℕ) (len j : ℕ) (h : ¬ j < len) :
    regRef regs len (Int.ofNat (j + 1)) = Int.ofNat 0 := by
  have hb : Nat.blt j len = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact h (Nat.blt_eq.mp e)
  show Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
    (Int.ofNat (Nat.succ (getN regs (Nat.sub (Nat.sub len j) 1)))) (Nat.blt j len) = _
  rw [hb]
  try rfl

private theorem regRef_neg_lt (regs : List ℕ) (len j : ℕ) (h : j < len) :
    regRef regs len (Int.negSucc j) = Int.negSucc (getN regs (len - j - 1)) := by
  have hb : Nat.blt j len = true := Nat.blt_eq.mpr h
  show Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
    (Int.negSucc (getN regs (Nat.sub (Nat.sub len j) 1))) (Nat.blt j len) = _
  rw [hb]
  try rfl

private theorem regRef_neg_ge (regs : List ℕ) (len j : ℕ) (h : ¬ j < len) :
    regRef regs len (Int.negSucc j) = Int.ofNat 0 := by
  have hb : Nat.blt j len = false := by
    rw [Bool.eq_false_iff]
    intro e
    exact h (Nat.blt_eq.mp e)
  show Bool.rec (motive := fun _ => Int) (Int.ofNat 0)
    (Int.negSucc (getN regs (Nat.sub (Nat.sub len j) 1))) (Nat.blt j len) = _
  rw [hb]
  try rfl

private theorem regRef_zero (regs : List ℕ) (len : ℕ) :
    regRef regs len (Int.ofNat 0) = Int.ofNat 0 := rfl

private theorem rel_get {n : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {rg : List PArr} {regs : List ℕ}
    (hrel : List.Forall₂ (fun r x => RR n r (perm x)) rg regs.reverse) {len : ℕ}
    (hlen : regs.length = len) {j : ℕ} (hj : j < len) :
    ∃ hj' : j < rg.length, RR n rg[j] (perm (getN regs (len - j - 1))) := by
  have hl := hrel.length_eq
  simp only [List.length_reverse] at hl
  have hj' : j < rg.length := by omega
  refine ⟨hj', ?_⟩
  have := (List.forall₂_iff_get.1 hrel).2 j hj' (by simpa using (by omega : j < regs.length))
  have e : getN regs (len - j - 1) = regs.reverse[j]'(by simp; omega) := by
    rw [getN_eq, List.getElem_reverse, List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega
  rw [e]
  simpa using this

private theorem letter_reg {n : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {rg : List PArr}
    {regs : List ℕ} (hrel : List.Forall₂ (fun r x => RR n r (perm x)) rg regs.reverse) {len : ℕ}
    (hlen : regs.length = len) (z : ℤ) :
    RR n (pLetter n rg z) (rp perm (regRef regs len z)) := by
  rcases z with (_ | j) | k
  · rw [regRef_zero]
    simpa [pLetter, rp] using (rr_id (n := n))
  · rw [pLetter_pos]
    by_cases hj : j < len
    · obtain ⟨hj', h⟩ := rel_get hrel hlen hj
      rw [regRef_pos_lt _ _ _ hj, List.getD_eq_getElem _ _ hj']
      exact h
    · rw [regRef_pos_ge _ _ _ hj]
      have hl := hrel.length_eq
      simp only [List.length_reverse] at hl
      rw [List.getD_eq_default _ _ (by omega)]
      simpa [rp] using (rr_id (n := n))
  · rw [pLetter_neg]
    by_cases hj : k < len
    · obtain ⟨hj', h⟩ := rel_get hrel hlen hj
      rw [regRef_neg_lt _ _ _ hj, List.getD_eq_getElem _ _ hj']
      exact h.inv
    · rw [regRef_neg_ge _ _ _ hj]
      have hl := hrel.length_eq
      simp only [List.length_reverse] at hl
      rw [List.getD_eq_default _ _ (by omega)]
      simpa [rp, pInv, pId] using (rr_id (n := n))

private theorem letW_spec (g : ℕ) : ∀ wd : List ℤ,
    List.rec (motive := fun _ => Bool) true
      (fun z _ ih2 => bAnd(Int.rec (motive := fun _ => Bool) (fun m => Nat.ble m g)
        (fun m => Nat.blt m g) z, ih2)) wd = true → ∀ z ∈ wd, letOK g z
  | [], _ => by simp
  | z' :: wd, h => by
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · rcases z with m | m
      · exact Nat.le_of_ble_eq_true h3
      · exact Nat.blt_eq.mp h3
    · exact letW_spec g wd h4 z hz

private theorem letSP_spec (g : ℕ) : ∀ ws : List (List ℤ), letSP g ws = true →
    ∀ wd ∈ ws, ∀ z ∈ wd, letOK g z
  | [], _ => by simp
  | wd :: ws, h => by
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    have ih := letSP_spec g ws h2
    intro wd' hwd'
    rcases List.mem_cons.1 hwd' with rfl | hwd'
    · exact letW_spec g _ h1
    · exact ih wd' hwd'

private theorem inSP_spec (X XI : ℕ → ℕ) : ∀ (IN INI : List ℕ) (j : ℕ),
    inSP IN INI X XI j = true → IN.length = INI.length ∧
      ∀ k < IN.length, X (j + k) = IN.getD k 0 ∧ XI (j + k) = INI.getD k 0
  | [], INI, j, h => by
    cases INI with
    | nil => simp
    | cons _ _ => exact absurd h (by simp [inSP])
  | x :: IN, INI, j, h => by
    cases INI with
    | nil => exact absurd h (by simp [inSP])
    | cons xi INI' =>
      change bAnd(Nat.beq (X j) x, bAnd(Nat.beq (XI j) xi, strictB (Nat.succ j)
        fun j' => inSP IN INI' X XI j')) = true at h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
      rw [sB] at h4
      obtain ⟨hl, hk⟩ := inSP_spec X XI IN INI' (Nat.succ j) h4
      refine ⟨by simp [hl], fun k hk' => ?_⟩
      cases k with
      | zero => exact ⟨by simpa using Nat.eq_of_beq_eq_true h1, by simpa using Nat.eq_of_beq_eq_true h3⟩
      | succ k =>
        have := hk k (by simpa using hk')
        rw [show j + (k + 1) = Nat.succ j + k by omega]
        simpa using this

private theorem wfSP_spec : ∀ (D : List (ℤ × ℤ)) (j : ℕ), wfSP j D = true →
    ∀ (pre post : List (ℤ × ℤ)) (a b : ℤ), D = pre ++ (a, b) :: post →
      refLt a (j + pre.length) = true ∧ refLt b (j + pre.length) = true
  | [], _, _, pre, post, a, b, hD => by simp at hD <;> cases pre <;> simp at hD
  | ab :: D', j, h, pre, post, a, b, hD => by
    change bAnd(refLt ab.1 j, bAnd(refLt ab.2 j, strictB (Nat.succ j) fun j' => wfSP j' D')) = true
      at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    rw [sB] at h4
    cases pre with
    | nil =>
      simp at hD
      obtain ⟨rfl, -⟩ := hD
      exact ⟨by simpa using h1, by simpa using h3⟩
    | cons c pre =>
      simp at hD
      obtain ⟨-, hD⟩ := hD
      have := wfSP_spec D' (Nat.succ j) h4 pre post a b hD
      simp only [List.length_cons]
      rw [show j + (pre.length + 1) = Nat.succ j + pre.length by omega]
      exact this

private theorem nodes_all {n w gi K L : ℕ} {D : List (ℤ × ℤ)} {X XI : ℕ → ℕ}
    (hK : D.length ≤ K * L)
    (hn : ∀ s < K, nodesSP n w gi D X XI (Nat.add gi (Nat.mul s L)) L = true) :
    ∀ j, gi ≤ j → j < gi + D.length → nodeSP n w gi D X XI j = true := by
  intro j hj1 hj2
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h
      rw [Nat.mul_zero] at hK
      omega
    · exact h
  have hs : (j - gi) / L < K := by
    rw [Nat.div_lt_iff_lt_mul hL]
    omega
  have h := hn _ hs
  unfold nodesSP at h
  rw [sB] at h
  have h2 := allBlk_spec h ((j - gi) % L) (Nat.mod_lt _ hL)
  have e : Nat.add (Nat.add gi (Nat.mul ((j - gi) / L) L)) ((j - gi) % L) = j := by
    have := Nat.div_add_mod (j - gi) L
    change gi + (j - gi) / L * L + (j - gi) % L = j
    rw [Nat.mul_comm] at this
    omega
  rw [e] at h2
  have c1 : Nat.ble gi j = true := Nat.ble_eq.mpr hj1
  have c2 : Nat.blt j (Nat.add gi (lenPr D)) = true := by
    rw [Nat.blt_eq, lenPr_eq]
    change j < gi + D.length
    exact hj2
  rw [c1, c2] at h2
  exact h2

private theorem nodeSP_spec {n w gi : ℕ} {D : List (ℤ × ℤ)} {X XI : ℕ → ℕ} {j : ℕ}
    {pre post : List (ℤ × ℤ)} {a b : ℤ} (hD : D = pre ++ (a, b) :: post)
    (hj : j = gi + pre.length) (h : nodeSP n w gi D X XI j = true) :
    X j = pcomp n w (mask w) (pa (pidn n w) X XI a).1 (pa (pidn n w) X XI b).1 ∧
      XI j = pcomp n w (mask w) (pa (pidn n w) X XI b).2 (pa (pidn n w) X XI a).2 := by
  have e : getPr D (Nat.sub j gi) = (a, b) := by
    change getPr D (j - gi) = _
    rw [getPr_eq, hD, hj, Nat.add_sub_cancel_left]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  unfold nodeSP at h
  rw [e] at h
  change refSP (pidn n w) X XI a (fun A AI => refSP (pidn n w) X XI b fun B BI =>
    bAnd(Nat.beq (X j) (pcomp n w (mask w) A B), Nat.beq (XI j) (pcomp n w (mask w) BI AI))) = true
    at h
  rw [refSP_eq, refSP_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

private noncomputable def permN (n w : ℕ) (X : ℕ → ℕ) (j : ℕ) : Equiv.Perm (Fin n) :=
  permOfP n w (X j)

private def Gd (n w : ℕ) (X XI : ℕ → ℕ) (j : ℕ) : Prop :=
  RP n w (X j) (permN n w X j) ∧ RP n w (XI j) (permN n w X j)⁻¹

private theorem gd_of {n w : ℕ} {X XI : ℕ → ℕ} {j : ℕ} {g : Equiv.Perm (Fin n)}
    (h1 : RP n w (X j) g) (h2 : RP n w (XI j) g⁻¹) : Gd n w X XI j ∧ permN n w X j = g := by
  have e : permN n w X j = g := permOfP_eq h1
  refine ⟨?_, e⟩
  unfold Gd
  rw [e]
  exact ⟨h1, h2⟩

private theorem res_ok {n w : ℕ} {X XI : ℕ → ℕ} (hid : RP n w (pidn n w) 1) {j : ℕ}
    (hb : ∀ m < j, Gd n w X XI m) {z : ℤ} (hz : refLt z j = true) :
    RP n w (pa (pidn n w) X XI z).1 (rp (permN n w X) z) ∧
      RP n w (pa (pidn n w) X XI z).2 (rp (permN n w X) z)⁻¹ := by
  rcases z with (_ | m) | m
  · simpa [pa, rp] using hid
  · have : m < j := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hz)
    exact hb m this
  · have : m < j := Nat.blt_eq.mp hz
    obtain ⟨h1, h2⟩ := hb m this
    refine ⟨h2, ?_⟩
    simpa [pa, rp] using h1

private theorem step_node {n w : ℕ} {X XI : ℕ → ℕ} (hn32 : n < 2 ^ 32)
    (hid : RP n w (pidn n w) 1) {j : ℕ} (hb : ∀ m < j, Gd n w X XI m) {a b : ℤ}
    (ha : refLt a j = true) (hbb : refLt b j = true)
    (h : X j = pcomp n w (mask w) (pa (pidn n w) X XI a).1 (pa (pidn n w) X XI b).1 ∧
      XI j = pcomp n w (mask w) (pa (pidn n w) X XI b).2 (pa (pidn n w) X XI a).2) :
    Gd n w X XI j ∧ permN n w X j = rp (permN n w X) a * rp (permN n w X) b := by
  obtain ⟨a1, a2⟩ := res_ok hid hb ha
  obtain ⟨b1, b2⟩ := res_ok hid hb hbb
  refine gd_of (g := rp (permN n w X) a * rp (permN n w X) b) ?_ ?_
  · rw [h.1]
    exact rp_pcomp hn32 a1 b1
  · rw [h.2, mul_inv_rev]
    exact rp_pcomp hn32 b2 a2

private theorem split_at {α : Type _} (D : List α) (k : ℕ) (hk : k < D.length) :
    ∃ (pre : List α) (x : α) (post : List α), D = pre ++ x :: post ∧ pre.length = k := by
  refine ⟨D.take k, D[k], D.drop (k + 1), ?_, by simp; omega⟩
  conv_lhs => rw [← List.take_append_drop k D]
  rw [List.drop_eq_getElem_cons hk]

private theorem good_all {n w gi : ℕ} {X XI : ℕ → ℕ} {D : List (ℤ × ℤ)} (hn32 : n < 2 ^ 32)
    (hid : RP n w (pidn n w) 1)
    (hin : ∀ j < gi, ∃ g, RP n w (X j) g ∧ RP n w (XI j) g⁻¹)
    (hwf : ∀ (pre post : List (ℤ × ℤ)) (a b : ℤ), D = pre ++ (a, b) :: post →
      refLt a (gi + pre.length) = true ∧ refLt b (gi + pre.length) = true)
    (hnode : ∀ j, gi ≤ j → j < gi + D.length → nodeSP n w gi D X XI j = true) :
    ∀ j < gi + D.length, Gd n w X XI j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    by_cases hjg : j < gi
    · obtain ⟨g, h1, h2⟩ := hin j hjg
      exact (gd_of h1 h2).1
    · obtain ⟨pre, ⟨a, b⟩, post, hD, hl⟩ := split_at D (j - gi) (by omega)
      have hj' : j = gi + pre.length := by omega
      obtain ⟨ha, hbb⟩ := hwf pre post a b hD
      rw [← hj'] at ha hbb
      exact (step_node hn32 hid (fun m hm => ih m hm (by omega)) ha hbb
        (nodeSP_spec hD hj' (hnode j (by omega) hj))).1

private def GD (n gi : ℕ) (perm : ℕ → Equiv.Perm (Fin n)) (D : List (ℤ × ℤ)) : Prop :=
  ∀ (pre post : List (ℤ × ℤ)) (a b : ℤ), D = pre ++ (a, b) :: post →
    perm (gi + pre.length) = rp perm a * rp perm b

private theorem gd_all {n w gi : ℕ} {X XI : ℕ → ℕ} {D : List (ℤ × ℤ)} (hn32 : n < 2 ^ 32)
    (hid : RP n w (pidn n w) 1)
    (hgood : ∀ j < gi + D.length, Gd n w X XI j)
    (hwf : ∀ (pre post : List (ℤ × ℤ)) (a b : ℤ), D = pre ++ (a, b) :: post →
      refLt a (gi + pre.length) = true ∧ refLt b (gi + pre.length) = true)
    (hnode : ∀ j, gi ≤ j → j < gi + D.length → nodeSP n w gi D X XI j = true) :
    GD n gi (permN n w X) D := by
  intro pre post a b hD
  have hlt : gi + pre.length < gi + D.length := by
    rw [hD]
    simp
  obtain ⟨ha, hbb⟩ := hwf pre post a b hD
  exact (step_node hn32 hid (fun m hm => hgood m (by omega)) ha hbb
    (nodeSP_spec hD rfl (hnode _ (by omega) hlt))).2

private structure Inv {n : ℕ} (gi : ℕ) (perm : ℕ → Equiv.Perm (Fin n)) (D : List (ℤ × ℤ))
    (st : LSt) (rg : List PArr) : Prop where
  fut : ∃ ext, D = st.ns.reverse ++ ext
  cnt : st.cnt = gi + st.ns.length
  rlen : st.regs.length = st.len
  rlt : ∀ x ∈ st.regs, x < st.cnt
  rel : List.Forall₂ (fun r x => RR n r (perm x)) rg st.regs.reverse

private theorem word_sound {n gi : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {D : List (ℤ × ℤ)}
    (hGD : GD n gi perm D) {gens : List PArr}
    (hg : ∀ k (hk : k < gens.length), RR n gens[k] (perm k)) :
    ∀ (wd : List ℤ), (∀ z ∈ wd, letOK gens.length z) → ∀ (pre ext : List (ℤ × ℤ)) (b : ℕ),
      b = gi + pre.length → D = pre ++ (wordSP wd b).1.reverse ++ ext →
      RR n (pWord n gens wd) (rp perm (wordSP wd b).2) := by
  intro wd
  induction wd with
  | nil =>
    intro _ pre ext b _ _
    exact rr_id
  | cons z wd ih =>
    intro hz pre ext b hb hD
    have e : wordSP (z :: wd) b = ((z, (wordSP wd b).2) :: (wordSP wd b).1,
        Int.ofNat (Nat.succ (Nat.add b (lenPr (wordSP wd b).1)))) := rfl
    rw [e, lenPr_eq] at hD ⊢
    simp only [List.reverse_cons, List.append_assoc] at hD
    have ih' := ih (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz')) pre ((z, (wordSP wd b).2) :: ext) b hb
      (by rw [hD]; simp)
    have hgd := hGD (pre ++ (wordSP wd b).1.reverse) ext z (wordSP wd b).2
      (by rw [hD]; simp)
    simp only [List.length_append, List.length_reverse] at hgd
    have hl := letter_gen hg (hz z List.mem_cons_self)
    have := hl.mul ih'
    have e2 : rp perm (Int.ofNat (Nat.succ (Nat.add b (wordSP wd b).1.length))) =
        rp perm z * rp perm (wordSP wd b).2 := by
      rw [← hgd]
      change perm (b + (wordSP wd b).1.length) = _
      rw [hb]
      congr 1
      omega
    rw [e2]
    exact this

private noncomputable def stepC (g : ℤ) (t0 m i : ℕ) (st : LSt) : LSt :=
  LSt.mk
    (List.cons (Prod.mk (Int.ofNat (Nat.succ st.cnt)) (Int.neg g))
      (List.cons (Prod.mk g (Int.ofNat (Nat.succ (Nat.add t0 (Nat.sub (Nat.sub m 1) i)))))
        st.ns))
    (Nat.succ (Nat.succ st.cnt)) (List.cons (Nat.succ st.cnt) st.regs) (Nat.succ st.len)

private noncomputable def cl (g : ℤ) (t0 m c : ℕ) (st : LSt) : LSt :=
  Nat.rec (motive := fun _ => LSt → LSt) (fun st => st)
    (fun i ih st => ih (stepC g t0 m i st)) c st

private theorem conjsLay_eq (g : ℤ) (t0 m : ℕ) (st : LSt) : conjsLay g t0 m st = cl g t0 m m st :=
  rfl

private theorem cl_zero (g : ℤ) (t0 m : ℕ) (st : LSt) : cl g t0 m 0 st = st := rfl

private theorem cl_succ (g : ℤ) (t0 m c : ℕ) (st : LSt) :
    cl g t0 m (c + 1) st = cl g t0 m c (stepC g t0 m c st) := rfl

private theorem cl_mono (g : ℤ) (t0 m : ℕ) : ∀ (c : ℕ) (st : LSt),
    ∃ e, (cl g t0 m c st).ns = e ++ st.ns := by
  intro c
  induction c with
  | zero => intro st; exact ⟨[], by simp [cl_zero]⟩
  | succ c ih =>
    intro st
    obtain ⟨e, he⟩ := ih (stepC g t0 m c st)
    rw [cl_succ]
    refine ⟨e ++ [(Prod.mk (Int.ofNat (Nat.succ st.cnt)) (Int.neg g)),
      (Prod.mk g (Int.ofNat (Nat.succ (Nat.add t0 (Nat.sub (Nat.sub m 1) c)))))], ?_⟩
    rw [he]
    simp [stepC]

private theorem cl_sound {n gi : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {D : List (ℤ × ℤ)}
    (hGD : GD n gi perm D) {gw : PArr} {g : ℤ} (hg : RR n gw (rp perm g)) {ts : List PArr}
    {t0 : ℕ} (hts : ∀ j (hj : j < ts.length), RR n ts[j] (perm (t0 + j))) (m : ℕ)
    (hm : ts.length = m) :
    ∀ c ≤ m, ∀ (st : LSt) (rg : List PArr), Inv gi perm D st rg →
      (∃ ext, D = (cl g t0 m c st).ns.reverse ++ ext) →
      Inv gi perm D (cl g t0 m c st) (rg ++ (ts.drop (m - c)).map (pConj n gw)) := by
  intro c
  induction c with
  | zero =>
    intro _ st rg hI _
    rw [cl_zero, Nat.sub_zero, ← hm, List.drop_length]
    simpa using hI
  | succ c ih =>
    intro hc st rg hI hfut
    rw [cl_succ] at hfut ⊢
    set st' := stepC g t0 m c st with hst'
    have hj : m - (c + 1) < ts.length := by omega
    have hfut' : ∃ ext, D = st'.ns.reverse ++ ext := by
      obtain ⟨e, he⟩ := cl_mono g t0 m c st'
      obtain ⟨ext, hext⟩ := hfut
      refine ⟨e.reverse ++ ext, ?_⟩
      rw [hext, he]
      simp
    obtain ⟨ext', hext'⟩ := hfut'
    have hidx : Nat.sub (Nat.sub m 1) c = m - (c + 1) := by
      show m - 1 - c = m - (c + 1)
      omega
    have hidx' : m - 1 - c = m - (c + 1) := by omega
    have hD : D = st.ns.reverse ++ (g, Int.ofNat (Nat.succ (t0 + (m - (c + 1))))) ::
        (Int.ofNat (Nat.succ st.cnt), Int.neg g) :: ext' := by
      rw [hext']
      simp [hst', stepC, hidx, hidx']
    have h1 := hGD st.ns.reverse _ g _ hD
    have h2 := hGD (st.ns.reverse ++ [(g, Int.ofNat (Nat.succ (t0 + (m - (c + 1)))))]) ext'
      (Int.ofNat (Nat.succ st.cnt)) (Int.neg g) (by rw [hD]; simp)
    simp only [List.length_append, List.length_reverse, List.length_singleton] at h1 h2
    rw [← hI.cnt] at h1
    have hcnt := hI.cnt
    rw [show gi + (st.ns.length + 1) = st.cnt + 1 by omega] at h2
    have hcn : rp perm (Int.ofNat (Nat.succ (t0 + (m - (c + 1))))) = perm (t0 + (m - (c + 1))) := rfl
    rw [hcn] at h1
    have h3 : perm (st.cnt + 1) = rp perm g * perm (t0 + (m - (c + 1))) * (rp perm g)⁻¹ := by
      rw [h2, rp_neg, ← h1]
      rfl
    have hconj : RR n (pConj n gw ts[m - (c + 1)]) (perm (st.cnt + 1)) := by
      rw [h3]
      exact (hg.mul (hts _ hj)).mul hg.inv
    have hI' : Inv gi perm D st' (rg ++ [pConj n gw ts[m - (c + 1)]]) := by
      refine ⟨⟨ext', hext'⟩, ?_, ?_, ?_, ?_⟩
      · simp [hst', stepC, hI.cnt]
        omega
      · simp [hst', stepC, hI.rlen]
      · intro x hx
        simp only [hst', stepC, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · omega
        · have := hI.rlt x hx
          omega
      · simp only [hst', stepC, List.reverse_cons]
        exact List.rel_append hI.rel (List.Forall₂.cons hconj List.Forall₂.nil)
    have := ih (by omega) st' _ hI' hfut
    have e : (rg ++ [pConj n gw ts[m - (c + 1)]]) ++ (ts.drop (m - c)).map (pConj n gw) =
        rg ++ (ts.drop (m - (c + 1))).map (pConj n gw) := by
      rw [List.drop_eq_getElem_cons hj, List.map_cons, show m - (c + 1) + 1 = m - c by omega]
      simp
    rw [e] at this
    exact this

private theorem wordsLay_cons (wd : List ℤ) (ws : List (List ℤ)) (t0 m : ℕ) (st : LSt) :
    wordsLay (wd :: ws) t0 m st = wordsLay ws t0 m
      (cl (wordSP wd st.cnt).2 t0 m m
        (LSt.mk (appPr (wordSP wd st.cnt).1 st.ns)
          (Nat.add st.cnt (lenPr (wordSP wd st.cnt).1)) st.regs st.len)) := rfl

private theorem wordsLay_mono (t0 m : ℕ) : ∀ (ws : List (List ℤ)) (st : LSt),
    ∃ e, (wordsLay ws t0 m st).ns = e ++ st.ns := by
  intro ws
  induction ws with
  | nil => intro st; exact ⟨[], by simp [wordsLay]⟩
  | cons wd ws ih =>
    intro st
    rw [wordsLay_cons]
    obtain ⟨e1, h1⟩ := ih (cl (wordSP wd st.cnt).2 t0 m m
        (LSt.mk (appPr (wordSP wd st.cnt).1 st.ns)
          (Nat.add st.cnt (lenPr (wordSP wd st.cnt).1)) st.regs st.len))
    obtain ⟨e2, h2⟩ := cl_mono (wordSP wd st.cnt).2 t0 m m
        (LSt.mk (appPr (wordSP wd st.cnt).1 st.ns)
          (Nat.add st.cnt (lenPr (wordSP wd st.cnt).1)) st.regs st.len)
    refine ⟨e1 ++ e2 ++ (wordSP wd st.cnt).1, ?_⟩
    rw [h1, h2]
    simp [appPr_eq]

private theorem wl_sound {n gi : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {D : List (ℤ × ℤ)}
    (hGD : GD n gi perm D) {gens : List PArr}
    (hg : ∀ k (hk : k < gens.length), RR n gens[k] (perm k)) {ts : List PArr} {m : ℕ}
    (hm : ts.length = m) (hts : ∀ j (hj : j < ts.length), RR n ts[j] (perm (gens.length + j))) :
    ∀ (ws : List (List ℤ)), (∀ wd ∈ ws, ∀ z ∈ wd, letOK gens.length z) →
      ∀ (st : LSt) (rg : List PArr), Inv gi perm D st rg →
      (∃ ext, D = (wordsLay ws gens.length m st).ns.reverse ++ ext) →
      Inv gi perm D (wordsLay ws gens.length m st)
        (rg ++ ws.flatMap fun wd => ts.map fun t => pConj n (pWord n gens wd) t) := by
  intro ws
  induction ws with
  | nil =>
    intro _ st rg hI _
    simpa [wordsLay] using hI
  | cons wd ws ih =>
    intro hz st rg hI hfut
    rw [wordsLay_cons] at hfut ⊢
    set ns := (wordSP wd st.cnt).1 with hns
    set gref := (wordSP wd st.cnt).2 with hgref
    set stw : LSt := LSt.mk (appPr ns st.ns) (Nat.add st.cnt (lenPr ns)) st.regs st.len with hstw
    have hf1 : ∃ ext, D = (cl gref gens.length m m stw).ns.reverse ++ ext := by
      obtain ⟨e, he⟩ := wordsLay_mono gens.length m ws (cl gref gens.length m m stw)
      obtain ⟨ext, hext⟩ := hfut
      refine ⟨e.reverse ++ ext, ?_⟩
      rw [hext, he]
      simp
    have hf2 : ∃ ext, D = stw.ns.reverse ++ ext := by
      obtain ⟨e, he⟩ := cl_mono gref gens.length m m stw
      obtain ⟨ext, hext⟩ := hf1
      refine ⟨e.reverse ++ ext, ?_⟩
      rw [hext, he]
      simp
    obtain ⟨ext, hext⟩ := hf2
    have hword : RR n (pWord n gens wd) (rp perm gref) := by
      refine word_sound hGD hg wd (fun z hz' => hz wd List.mem_cons_self z hz') st.ns.reverse ext
        st.cnt (by rw [hI.cnt]; simp) ?_
      rw [hext]
      simp [hstw, appPr_eq, hns]
    have hIw : Inv gi perm D stw rg := by
      have hcnt := hI.cnt
      refine ⟨⟨ext, hext⟩, ?_, hI.rlen, ?_, hI.rel⟩
      · simp only [hstw, lenPr_eq, appPr_eq, List.length_append]
        change st.cnt + _ = _
        omega
      · intro x hx
        have := hI.rlt x hx
        simp only [hstw]
        change x < st.cnt + _
        omega
    have hIc := cl_sound hGD hword hts m hm m (Nat.le_refl _) stw rg hIw hf1
    rw [Nat.sub_self, List.drop_zero] at hIc
    have := ih (fun wd' hwd' => hz wd' (List.mem_cons_of_mem _ hwd')) _ _ hIc hfut
    rw [List.flatMap_cons, ← List.append_assoc]
    exact this

private theorem progLay_cons (pq : ℤ × ℤ) (prog : List (ℤ × ℤ)) (st : LSt) :
    progLay (pq :: prog) st = progLay prog (LSt.mk
      (List.cons (Prod.mk (regRef st.regs st.len pq.1) (regRef st.regs st.len pq.2)) st.ns)
      (Nat.succ st.cnt) (List.cons st.cnt st.regs) (Nat.succ st.len)) := rfl

private theorem progLay_mono : ∀ (prog : List (ℤ × ℤ)) (st : LSt),
    ∃ e, (progLay prog st).ns = e ++ st.ns := by
  intro prog
  induction prog with
  | nil => intro st; exact ⟨[], by simp [progLay]⟩
  | cons pq prog ih =>
    intro st
    rw [progLay_cons]
    obtain ⟨e, he⟩ := ih (LSt.mk
      (List.cons (Prod.mk (regRef st.regs st.len pq.1) (regRef st.regs st.len pq.2)) st.ns)
      (Nat.succ st.cnt) (List.cons st.cnt st.regs) (Nat.succ st.len))
    refine ⟨e ++ [(regRef st.regs st.len pq.1, regRef st.regs st.len pq.2)], ?_⟩
    rw [he]
    simp

private theorem pl_sound {n gi : ℕ} {perm : ℕ → Equiv.Perm (Fin n)} {D : List (ℤ × ℤ)}
    (hGD : GD n gi perm D) :
    ∀ (prog : List (ℤ × ℤ)) (st : LSt) (rg : List PArr), Inv gi perm D st rg →
      (∃ ext, D = (progLay prog st).ns.reverse ++ ext) →
      Inv gi perm D (progLay prog st) (pRun n rg prog) := by
  intro prog
  induction prog with
  | nil =>
    intro st rg hI _
    exact hI
  | cons pq prog ih =>
    intro st rg hI hfut
    rw [progLay_cons] at hfut ⊢
    set st' : LSt := LSt.mk
      (List.cons (Prod.mk (regRef st.regs st.len pq.1) (regRef st.regs st.len pq.2)) st.ns)
      (Nat.succ st.cnt) (List.cons st.cnt st.regs) (Nat.succ st.len) with hst'
    have hfut' : ∃ ext, D = st'.ns.reverse ++ ext := by
      obtain ⟨e, he⟩ := progLay_mono prog st'
      obtain ⟨ext, hext⟩ := hfut
      refine ⟨e.reverse ++ ext, ?_⟩
      rw [hext, he]
      simp
    obtain ⟨ext', hext'⟩ := hfut'
    have hD : D = st.ns.reverse ++ (regRef st.regs st.len pq.1, regRef st.regs st.len pq.2) :: ext' := by
      rw [hext']
      simp [hst']
    have h1 := hGD st.ns.reverse ext' _ _ hD
    simp only [List.length_reverse] at h1
    have hcnt := hI.cnt
    rw [← hcnt] at h1
    have hnew : RR n (pMul n (pLetter n rg pq.1) (pLetter n rg pq.2)) (perm st.cnt) := by
      rw [h1]
      exact (letter_reg hI.rel hI.rlen pq.1).mul (letter_reg hI.rel hI.rlen pq.2)
    have hI' : Inv gi perm D st' (rg ++ [pMul n (pLetter n rg pq.1) (pLetter n rg pq.2)]) := by
      refine ⟨⟨ext', hext'⟩, ?_, ?_, ?_, ?_⟩
      · simp [hst']
        omega
      · simp [hst', hI.rlen]
      · intro x hx
        simp only [hst', List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · omega
        · have := hI.rlt x hx
          omega
      · simp only [hst', List.reverse_cons]
        exact List.rel_append hI.rel (List.Forall₂.cons hnew List.Forall₂.nil)
    rw [pRun_cons]
    exact ih st' _ hI' hfut

private theorem lenTc_eq (L : List ℕ) : lenTc L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change Nat.succ (lenTc L) = _
    rw [ih]
    rfl

private theorem inputs_sound {n w : ℕ} {G GI : List ℕ} {X XI : ℕ → ℕ} {j0 : ℕ}
    (hg : gensTc n w G GI = true) (hin : inSP G GI X XI j0 = true) :
    (unpackP n w G GI).length = G.length ∧
    ∀ k (hk : k < (unpackP n w G GI).length), ∃ g : Equiv.Perm (Fin n),
      RR n (unpackP n w G GI)[k] g ∧ RP n w (X (j0 + k)) g ∧ RP n w (XI (j0 + k)) g⁻¹ := by
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  have hlen : (unpackP n w G GI).length = G.length := by
    simp [unpackP, hl]
  refine ⟨hlen, fun k hk => ?_⟩
  have hk' : k < G.length := hlen ▸ hk
  have hk2 : k < GI.length := hl ▸ hk'
  have hkz : k < (G.zip GI).length := by simp [hk', hk2]
  have e1 : (G.zip GI)[k] = (G[k], GI[k]) := by simp
  obtain ⟨g, h1, h2, h3⟩ := rr_unpack (hz (G[k], GI[k]) (by rw [← e1]; exact List.getElem_mem hkz))
  obtain ⟨-, hx⟩ := inSP_spec X XI G GI j0 hin
  obtain ⟨hx1, hx2⟩ := hx k hk'
  refine ⟨g, ?_, ?_, ?_⟩
  · have : (unpackP n w G GI)[k] = (unpack n w G[k], unpack n w GI[k]) := by
      simp [unpackP]
    rw [this]
    exact h1
  · rw [hx1, List.getD_eq_getElem _ _ hk']
    exact h2
  · rw [hx2, List.getD_eq_getElem _ _ hk2]
    exact h3

private theorem memSP (X : ℕ → ℕ) (A : ℕ) : ∀ (regs : List ℕ),
    List.rec (motive := fun _ => Bool) false (fun r _ ih2 => bIf(Nat.beq (X r) A, true, ih2))
      regs = true → ∃ r ∈ regs, X r = A
  | [], h => by simp at h
  | r :: regs, h => by
    change Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false
      (fun r _ ih2 => bIf(Nat.beq (X r) A, true, ih2)) regs) true (Nat.beq (X r) A) = true at h
    cases hb : Nat.beq (X r) A
    · rw [hb] at h
      obtain ⟨r', hr', e⟩ := memSP X A regs h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
    · exact ⟨r, List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

private theorem targSP_spec {n w : ℕ} {X : ℕ → ℕ} {regs : List ℕ} :
    ∀ (targets : List ℕ), targSP n w X regs targets = true → ∀ A ∈ targets, ∃ r ∈ regs, X r = A
  | [], _ => by simp
  | A :: targets, h => by
    obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact memSP X _ regs h1
    · exact targSP_spec targets h2 B hB

private theorem selSP_spec (X : ℕ → ℕ) (regs : List ℕ) (len : ℕ) :
    ∀ (idx S : List ℕ), selSP X regs len idx S = true → idx.length = S.length ∧
      ∀ i < idx.length, idx.getD i 0 < len ∧
        X (getN regs (len - idx.getD i 0 - 1)) = S.getD i 0
  | [], S, h => by
    cases S with
    | nil => simp
    | cons _ _ => exact absurd h (by simp [selSP])
  | k :: idx, S, h => by
    cases S with
    | nil => exact absurd h (by simp [selSP])
    | cons s S' =>
      change bAnd(Nat.blt k len, bAnd(Nat.beq (X (getN regs (Nat.sub (Nat.sub len k) 1))) s,
        selSP X regs len idx S')) = true at h
      obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
      obtain ⟨hl, hk⟩ := selSP_spec X regs len idx S' h4
      refine ⟨by simp [hl], fun i hi => ?_⟩
      cases i with
      | zero =>
        exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h3⟩
      | succ i => exact hk i (by simpa using hi)

private theorem mc_core {n w gi : ℕ} {X XI : ℕ → ℕ} {D : List (ℤ × ℤ)} {gens ts : List PArr}
    {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} {targets : List ℕ}
    (hgi : gens.length + ts.length = gi)
    (hD : nodesOf (layMC gens.length ts.length ws prog) = D)
    (hgood : ∀ j < gi + D.length, Gd n w X XI j) (hGD : GD n gi (permN n w X) D)
    (hgensRR : ∀ k (hk : k < gens.length), RR n gens[k] (permN n w X k))
    (htsRR : ∀ j (hj : j < ts.length), RR n ts[j] (permN n w X (gens.length + j)))
    (hlet : ∀ wd ∈ ws, ∀ z ∈ wd, letOK gens.length z)
    (ht : ∀ A ∈ targets, ∃ r ∈ (layMC gens.length ts.length ws prog).regs, X r = A) :
    multiConjCheck n gens ts ws prog (targets.map (unpack n w)) = true := by
  subst hgi
  set st0 : LSt := LSt.mk List.nil (Nat.add gens.length ts.length) List.nil (nat_lit 0) with hst0
  have hF : layMC gens.length ts.length ws prog =
      progLay prog (wordsLay ws gens.length ts.length st0) := rfl
  have hfutF : ∃ ext, D = (progLay prog (wordsLay ws gens.length ts.length st0)).ns.reverse ++ ext :=
    ⟨[], by rw [← hD, hF]; simp [nodesOf, revPr_eq]⟩
  obtain ⟨e, he⟩ := progLay_mono prog (wordsLay ws gens.length ts.length st0)
  have hfutW : ∃ ext, D = (wordsLay ws gens.length ts.length st0).ns.reverse ++ ext := by
    obtain ⟨ext, hext⟩ := hfutF
    exact ⟨e.reverse ++ ext, by rw [hext, he]; simp⟩
  have hInit : Inv (gens.length + ts.length) (permN n w X) D st0 [] :=
    ⟨⟨D, by simp [hst0]⟩, by simp [hst0], rfl, by simp [hst0], List.Forall₂.nil⟩
  have hI1 := wl_sound hGD hgensRR rfl htsRR ws hlet st0 [] hInit hfutW
  have hI2 := pl_sound hGD prog _ _ hI1 hfutF
  rw [List.nil_append] at hI2
  have hlenD : D.length = (progLay prog (wordsLay ws gens.length ts.length st0)).ns.length := by
    rw [← hD, hF]
    simp [nodesOf, revPr_eq]
  simp only [multiConjCheck, List.all_eq_true, List.any_eq_true]
  intro A' hA'
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
  obtain ⟨r, hr, hXr⟩ := ht A hA
  rw [hF] at hr
  have hrr := List.mem_reverse.2 hr
  obtain ⟨i, hi, hir⟩ := List.getElem_of_mem hrr
  have hl := hI2.rel.length_eq
  have hi' : i < (pRun n (ws.flatMap fun wd => ts.map fun t =>
      pConj n (pWord n gens wd) t) prog).length := by omega
  have hrel := (List.forall₂_iff_get.1 hI2.rel).2 i hi' hi
  simp only [List.get_eq_getElem, hir] at hrel
  have hrlt := hI2.rlt r hr
  rw [hI2.cnt, ← hlenD] at hrlt
  obtain ⟨hX1, -⟩ := hgood r hrlt
  refine ⟨(pRun n (ws.flatMap fun wd => ts.map fun t => pConj n (pWord n gens wd) t) prog)[i],
    List.getElem_mem hi', ?_⟩
  rw [← hXr]
  exact (CFSG.Monster.B.Co2.eqA_iff hrel.1.1 (CFSG.KS.Raw.Orb.rep_unpack hX1)).2 rfl

private theorem run_core {n w gi : ℕ} {X XI : ℕ → ℕ} {D : List (ℤ × ℤ)} {gens : List PArr}
    {prog : List (ℤ × ℤ)} {idx S : List ℕ}
    (hgi : gens.length = gi) (hD : nodesOf (layRun gi prog) = D)
    (hgood : ∀ j < gi + D.length, Gd n w X XI j) (hGD : GD n gi (permN n w X) D)
    (hgensRR : ∀ k (hk : k < gens.length), RR n gens[k] (permN n w X k))
    (hs : selRun gi prog X idx S = true) :
    (idx.map fun k => (pRun n gens prog).getD k (pId n)).map Prod.fst = S.map (unpack n w) := by
  subst hgi
  set st0 : LSt := LSt.mk List.nil gens.length (inRegs gens.length) gens.length with hst0
  have hF : layRun gens.length prog = progLay prog st0 := rfl
  have hfutF : ∃ ext, D = (progLay prog st0).ns.reverse ++ ext :=
    ⟨[], by rw [← hD, hF]; simp [nodesOf, revPr_eq]⟩
  obtain ⟨e, he⟩ := progLay_mono prog st0
  have hInit : Inv gens.length (permN n w X) D st0 gens := by
    refine ⟨⟨D, by simp [hst0]⟩, by simp [hst0], by simp [hst0, inRegs_eq], ?_, ?_⟩
    · intro x hx
      simp only [hst0, inRegs_eq, List.mem_reverse, List.mem_range] at hx ⊢
      exact hx
    · simp only [hst0, inRegs_eq, List.reverse_reverse]
      refine List.forall₂_iff_get.2 ⟨by simp, fun i h1 h2 => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_range]
      exact hgensRR i h1
  have hI2 := pl_sound hGD prog _ _ hInit hfutF
  have hlenD : D.length = (progLay prog st0).ns.length := by
    rw [← hD, hF]
    simp [nodesOf, revPr_eq]
  have hs' : selSP X (progLay prog st0).regs (progLay prog st0).len idx S = true := hs
  obtain ⟨hlis, hsel⟩ := selSP_spec X _ _ idx S hs'
  apply List.ext_getElem
  · simp [hlis]
  · intro i h1 h2
    simp only [List.length_map] at h1 h2
    obtain ⟨hk1, hk2⟩ := hsel i h1
    simp only [List.getElem_map]
    have hk1' : idx[i] < (progLay prog st0).len := by
      rw [List.getD_eq_getElem _ _ h1] at hk1
      exact hk1
    obtain ⟨hj', hrel⟩ := rel_get hI2.rel hI2.rlen hk1'
    rw [List.getD_eq_getElem _ _ hj']
    rw [List.getD_eq_getElem _ _ h1] at hk2
    rw [List.getD_eq_getElem _ _ (by omega)] at hk2
    have hxmem : getN (progLay prog st0).regs ((progLay prog st0).len - idx[i] - 1) ∈
        (progLay prog st0).regs := by
      rw [getN_eq, List.getD_eq_getElem _ _ (by have := hI2.rlen; omega)]
      exact List.getElem_mem _
    have hrlt := hI2.rlt _ hxmem
    rw [hI2.cnt, ← hlenD] at hrlt
    obtain ⟨hX1, -⟩ := hgood _ hrlt
    rw [← hk2]
    exact arr_eq hrel.1.1 (CFSG.KS.Raw.Orb.rep_unpack hX1) hrel.2.1 (unpack_size' n w _)
theorem mcSP_sound {n w gi K L : Nat} {G GI TS TIS : List Nat} {ws : List (List Int)}
    {prog : List (Int × Int)} {targets : List Nat} {X XI : Nat → Nat} {D : List (Int × Int)}
    (hgi : Nat.add (lenTc G) (lenTc TS) = gi)
    (hD : nodesOf (layMC (lenTc G) (lenTc TS) ws prog) = D)
    (hh : headMC n w G GI TS TIS ws prog X XI = true) (hK : lenPr D ≤ K * L)
    (hn : ∀ s < K, nodesSP n w gi D X XI (Nat.add gi (Nat.mul s L)) L = true)
    (ht : targMC n w (lenTc G) (lenTc TS) ws prog X targets = true) :
    multiConjCheck n (unpackP n w G GI) (unpackP n w TS TIS) ws prog
      (targets.map (unpack n w)) = true := by
  unfold headMC at hh
  obtain ⟨hid, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hgens, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨htens, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hinG, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hinT, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hlet, hwf⟩ := (bAnd_iff _ _).1 hh
  have hn32 := idK_small hid
  have hidn := rp_idn hid
  obtain ⟨hlG, hG⟩ := inputs_sound hgens hinG
  obtain ⟨hlT, hT⟩ := inputs_sound htens hinT
  have e1 : lenTc G = (unpackP n w G GI).length := by rw [hlG, lenTc_eq]
  have e2 : lenTc TS = (unpackP n w TS TIS).length := by rw [hlT, lenTc_eq]
  have hgi' : (unpackP n w G GI).length + (unpackP n w TS TIS).length = gi := by
    rw [← e1, ← e2, ← hgi]
    rfl
  have hwf1 : wfSP gi D = true := by
    rw [← hD, ← hgi]
    exact hwf
  have hwf2 := wfSP_spec D gi hwf1
  have hin : ∀ j < gi, ∃ g, RP n w (X j) g ∧ RP n w (XI j) g⁻¹ := by
    intro j hj
    by_cases hjG : j < (unpackP n w G GI).length
    · obtain ⟨g, -, h1, h2⟩ := hG j hjG
      rw [Nat.zero_add] at h1 h2
      exact ⟨g, h1, h2⟩
    · have hjT : j - lenTc G < (unpackP n w TS TIS).length := by omega
      obtain ⟨g, -, h1, h2⟩ := hT _ hjT
      have ej : lenTc G + (j - lenTc G) = j := by omega
      rw [ej] at h1 h2
      exact ⟨g, h1, h2⟩
  have hK' : D.length ≤ K * L := by rw [← lenPr_eq]; exact hK
  have hnode := nodes_all hK' hn
  have hgood := good_all hn32 hidn hin hwf2 hnode
  have hGD := gd_all hn32 hidn hgood hwf2 hnode
  have hgensRR : ∀ k (hk : k < (unpackP n w G GI).length), RR n (unpackP n w G GI)[k]
      (permN n w X k) := by
    intro k hk
    obtain ⟨g, h1, h2, -⟩ := hG k hk
    rw [Nat.zero_add] at h2
    have : permN n w X k = g := permOfP_eq h2
    rw [this]
    exact h1
  have htsRR : ∀ j (hj : j < (unpackP n w TS TIS).length), RR n (unpackP n w TS TIS)[j]
      (permN n w X ((unpackP n w G GI).length + j)) := by
    intro j hj
    obtain ⟨g, h1, h2, -⟩ := hT j hj
    rw [← e1]
    have : permN n w X (lenTc G + j) = g := permOfP_eq h2
    rw [this]
    exact h1
  have hlet' : ∀ wd ∈ ws, ∀ z ∈ wd, letOK (unpackP n w G GI).length z := by
    rw [← e1]
    exact letSP_spec _ ws hlet
  unfold targMC at ht
  rw [e1, e2] at hD
  exact mc_core hgi' hD hgood hGD hgensRR htsRR hlet' (by
    intro A hA
    rw [e1, e2] at ht
    exact targSP_spec targets ht A hA)

theorem runSP_sound {n w gi K L : Nat} {G GI : List Nat} {prog : List (Int × Int)}
    {idx S : List Nat} {X XI : Nat → Nat} {D : List (Int × Int)}
    (hgi : lenTc G = gi) (hD : nodesOf (layRun gi prog) = D)
    (hh : headRun n w G GI prog X XI = true) (hK : lenPr D ≤ K * L)
    (hn : ∀ s < K, nodesSP n w gi D X XI (Nat.add gi (Nat.mul s L)) L = true)
    (hs : selRun gi prog X idx S = true) :
    (idx.map fun k => (pRun n (unpackP n w G GI) prog).getD k (pId n)).map Prod.fst =
      S.map (unpack n w) := by
  unfold headRun at hh
  obtain ⟨hid, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hgens, hh⟩ := (bAnd_iff _ _).1 hh
  obtain ⟨hinG, hwf⟩ := (bAnd_iff _ _).1 hh
  have hn32 := idK_small hid
  have hidn := rp_idn hid
  obtain ⟨hlG, hG⟩ := inputs_sound hgens hinG
  have e1 : lenTc G = (unpackP n w G GI).length := by rw [hlG, lenTc_eq]
  have hgi' : (unpackP n w G GI).length = gi := by rw [← e1]; exact hgi
  have hwf1 : wfSP gi D = true := by
    rw [← hD, ← hgi]
    exact hwf
  have hwf2 := wfSP_spec D gi hwf1
  have hin : ∀ j < gi, ∃ g, RP n w (X j) g ∧ RP n w (XI j) g⁻¹ := by
    intro j hj
    obtain ⟨g, -, h1, h2⟩ := hG j (by omega)
    rw [Nat.zero_add] at h1 h2
    exact ⟨g, h1, h2⟩
  have hK' : D.length ≤ K * L := by rw [← lenPr_eq]; exact hK
  have hnode := nodes_all hK' hn
  have hgood := good_all hn32 hidn hin hwf2 hnode
  have hGD := gd_all hn32 hidn hgood hwf2 hnode
  have hgensRR : ∀ k (hk : k < (unpackP n w G GI).length), RR n (unpackP n w G GI)[k]
      (permN n w X k) := by
    intro k hk
    obtain ⟨g, h1, h2, -⟩ := hG k hk
    rw [Nat.zero_add] at h2
    have : permN n w X k = g := permOfP_eq h2
    rw [this]
    exact h1
  exact run_core hgi' hD hgood hGD hgensRR hs

theorem threeConj_of_SP {n w gi K L : Nat} {G GI : List Nat} {T TI : Nat}
    {ws : List (List Int)} {prog : List (Int × Int)} {targets : List Nat} {X XI : Nat → Nat}
    {D : List (Int × Int)}
    (hgi : Nat.add (lenTc G) (lenTc [T]) = gi)
    (hD : nodesOf (layMC (lenTc G) (lenTc [T]) ws prog) = D)
    (hh : headMC n w G GI [T] [TI] ws prog X XI = true) (hK : lenPr D ≤ K * L)
    (hn : ∀ s < K, nodesSP n w gi D X XI (Nat.add gi (Nat.mul s L)) L = true)
    (ht : targMC n w (lenTc G) (lenTc [T]) ws prog X targets = true) :
    threeConjCheck n (unpackP n w G GI) (unpack n w T, unpack n w TI) ws prog
      (targets.map (unpack n w)) = true := by
  rw [threeConj_eq_multi]
  exact mcSP_sound hgi hD hh hK hn ht

end CFSG.KC.LQT.SP

end
