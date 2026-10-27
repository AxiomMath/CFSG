module

public import Certificates.Data.Kernel.J3Tk
public import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

namespace CFSG.KC.J3Tk

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

theorem nBf {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem nLt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem nLtF {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  rcases Nat.lt_or_ge a b with h' | h'
  · have : Nat.blt a b = true := Nat.ble_eq_true_of_le h'
    rw [h] at this
    exact absurd this Bool.false_ne_true
  · exact h'

theorem nLEf {a b : Nat} (h : Nat.ble a b = false) : b < a := by
  rcases Nat.lt_or_ge b a with h' | h'
  · exact h'
  · have : Nat.ble a b = true := Nat.ble_eq_true_of_le h'
    rw [h] at this
    exact absurd this Bool.false_ne_true

theorem nLEf' {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

theorem fne {P : Prop} (h : false = true) : P := absurd h Bool.false_ne_true

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bA {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := (bAnd_iff a b).1 h

def Tb (X : Nat) (g : Gp) : Prop := ∀ p : Fin 6156, ap X p = (g p : Nat)

theorem ap_lt (X i : Nat) : ap X i < 8192 := pg_lt 13 X i

theorem ap_pc (X Y : Nat) {i : Nat} (hi : i < 6156) : ap (pc X Y) i = ap X (ap Y i) :=
  pg_pcomp (n := 6156) (w := 13) (p := X) (q := Y) (by norm_num) hi

theorem ap_pid {i : Nat} (hi : i < 6156) : ap pid i = i :=
  pg_pidn (n := 6156) (w := 13) (by norm_num) (by norm_num) hi

theorem tb_pc {X Y : Nat} {g h : Gp} (hX : Tb X g) (hY : Tb Y h) : Tb (pc X Y) (g * h) := by
  intro p
  rw [ap_pc X Y p.2, hY p, hX (h p)]
  rfl

theorem tb_pid : Tb pid 1 := fun p => ap_pid p.2

theorem tb_pw {X : Nat} {g : Gp} (hX : Tb X g) : ∀ e, Tb (pw X e) (g ^ e)
  | 0 => by rw [pow_zero]; exact tb_pid
  | e + 1 => by
    have h : pw X (e + 1) = pc X (pw X e) := sN _ _
    rw [h, pow_succ']
    exact tb_pc hX (tb_pw hX e)

theorem tb_inv {X V : Nat} {g : Gp} (hX : Tb X g) (h : pc V X = pid) : Tb V g⁻¹ := by
  intro p
  have e : ap (pc V X) (g⁻¹ p : Nat) = ap pid (g⁻¹ p : Nat) := by rw [h]
  rw [ap_pc V X (g⁻¹ p).2, ap_pid (g⁻¹ p).2, hX (g⁻¹ p)] at e
  simpa using e

theorem unpack_get (X : Nat) {i : Nat} (hi : i < 6156) : (unpack 6156 13 X)[i]! = ap X i := by
  unfold unpack
  rw [getElem!_ofFn_nat _ hi]
  rfl

theorem tb_of_rep {X : Nat} {g : Gp} (h : Rep 6156 (unpack 6156 13 X) g) : Tb X g := fun p => by
  rw [← unpack_get X p.2]
  exact h p

theorem tb_of_thRep {X : Nat} {g : Gp}
    (h : CFSG.Sporadic.Th.Rep 6156 (CFSG.KS.MulH.tabT (unpack 6156 13 X)) g) : Tb X g := by
  intro p
  have h1 := h p p.2
  rw [CFSG.KS.MulH.ap_tabT _ (by rw [unpack_get X p.2]; exact (ap_lt X p).trans (by norm_num)),
    unpack_get X p.2, CFSG.Sporadic.Th.idx_of_lt g p.2] at h1
  rw [h1]
  rfl

theorem perm_eq {X : Nat} {g : Gp} (h : Tb X g) : permOfArr 6156 (unpack 6156 13 X) = g := by
  have hc : (∀ i < 6156, (unpack 6156 13 X)[i]! < 6156) ∧
      ∀ i < 6156, ∀ j < 6156, (unpack 6156 13 X)[i]! = (unpack 6156 13 X)[j]! → i = j := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [unpack_get X hi, h ⟨i, hi⟩]
      exact (g _).2
    · rw [unpack_get X hi, unpack_get X hj, h ⟨i, hi⟩, h ⟨j, hj⟩] at hij
      have := g.injective (Fin.ext hij)
      simpa using this
  ext x
  rw [permOfArr, dif_pos hc]
  simp only [Equiv.ofBijective_apply]
  rw [unpack_get X x.2, h x]

def Gd (X : Nat) : Prop := ∃ g ∈ j3R, Tb X g

theorem gd_pc {X Y : Nat} (hX : Gd X) (hY : Gd Y) : Gd (pc X Y) := by
  obtain ⟨g, hg, hX⟩ := hX
  obtain ⟨h, hh, hY⟩ := hY
  exact ⟨g * h, mul_mem hg hh, tb_pc hX hY⟩

theorem gd_pid : Gd pid := ⟨1, one_mem _, tb_pid⟩

theorem gd_pw {X : Nat} (hX : Gd X) (e : Nat) : Gd (pw X e) := by
  obtain ⟨g, hg, hX⟩ := hX
  exact ⟨g ^ e, pow_mem hg e, tb_pw hX e⟩

theorem gd_inv {X V : Nat} (hX : Gd X) (h : pc V X = pid) : Gd V := by
  obtain ⟨g, hg, hX⟩ := hX
  exact ⟨g⁻¹, inv_mem hg, tb_inv hX h⟩

noncomputable def keyG (g : Gp) : Nat := k4 (g 0) (g 1) (g 3) (g 2)

theorem fld_k4 {a b c d : Nat} (ha : a < 8192) (hb : b < 8192) (hc : c < 8192) (hd : d < 8192) :
    Fld 13 (k4 a b c d)
      (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d
        else 0) := by
  have h := fld_or (fld_one (w := 13) ha) (fld_or (fld_shl 1 (fld_one (w := 13) hb))
    (fld_or (fld_shl 2 (fld_one (w := 13) hc)) (fld_shl 3 (fld_one (w := 13) hd))))
  refine fld_congr h ?_
  intro i
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i <;> simp
  · have h1 : i ≠ 0 := by omega
    have h2 : i ≠ 1 := by omega
    have h3 : i ≠ 2 := by omega
    have h4 : i ≠ 3 := by omega
    have h5 : i - 1 ≠ 0 := by omega
    have h6 : i - 2 ≠ 0 := by omega
    have h7 : i - 3 ≠ 0 := by omega
    simp [h1, h2, h3, h4, h5, h6, h7]

theorem kf_k4 {a b c d : Nat} (ha : a < 8192) (hb : b < 8192) (hc : c < 8192) (hd : d < 8192) :
    kf (k4 a b c d) 0 = a ∧ kf (k4 a b c d) 1 = b ∧ kf (k4 a b c d) 2 = c ∧
      kf (k4 a b c d) 3 = d := by
  have h := fld_k4 ha hb hc hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (pg_of_fld (i := 0) h (by simpa using ha)).trans (by simp)
  · exact (pg_of_fld (i := 1) h (by simpa using hb)).trans (by simp)
  · exact (pg_of_fld (i := 2) h (by simpa using hc)).trans (by simp)
  · exact (pg_of_fld (i := 3) h (by simpa using hd)).trans (by simp)

theorem fin_lt (p : Fin 6156) : (p : Nat) < 8192 := p.2.trans (by norm_num)

theorem keyG_eq {g h : Gp} (e : keyG g = keyG h) :
    g 0 = h 0 ∧ g 1 = h 1 ∧ g 3 = h 3 ∧ g 2 = h 2 := by
  have h1 := kf_k4 (fin_lt (g 0)) (fin_lt (g 1)) (fin_lt (g 3)) (fin_lt (g 2))
  have h2 := kf_k4 (fin_lt (h 0)) (fin_lt (h 1)) (fin_lt (h 3)) (fin_lt (h 2))
  unfold keyG at e
  rw [e] at h1
  exact ⟨Fin.ext (h1.1.symm.trans h2.1), Fin.ext (h1.2.1.symm.trans h2.2.1),
    Fin.ext (h1.2.2.1.symm.trans h2.2.2.1), Fin.ext (h1.2.2.2.symm.trans h2.2.2.2)⟩

theorem keyF_eq {f : Nat → Nat} {g : Gp} (h : ∀ p : Fin 6156, f p = (g p : Nat)) :
    keyF f = keyG g := by
  unfold keyF keyG
  rw [← h 0, ← h 1, ← h 3, ← h 2]
  rfl

theorem keyL_eq {X : Nat} {g x : Gp} (hX : Tb X g) : keyL X (keyG x) = keyG (g * x) := by
  have h1 := kf_k4 (fin_lt (x 0)) (fin_lt (x 1)) (fin_lt (x 3)) (fin_lt (x 2))
  unfold keyL keyG
  unfold keyG at h1
  rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, hX, hX, hX, hX]
  rfl

theorem key1_eq : key1 = keyG 1 := rfl

theorem eq_of_key (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 → g 2 = 2 → g = 1) {g h : Gp}
    (hg : g ∈ j3R) (hh : h ∈ j3R) (e : keyG g = keyG h) : g = h := by
  obtain ⟨e0, e1, e3, e2⟩ := keyG_eq e
  have hk := hB (h⁻¹ * g) (mul_mem (inv_mem hh) hg) (by simp [e0]) (by simp [e1]) (by simp [e3])
    (by simp [e2])
  exact (inv_mul_eq_one.1 hk).symm

theorem val_reg (RT MT : Nat → Nat) (x : Nat) : val RT MT (Nat.add (Nat.mul 2 x) 2) = RT x := by
  have h0 : Nat.beq (Nat.add (Nat.mul 2 x) 2) 0 = false := nBf (by
    change 2 * x + 2 ≠ 0
    omega)
  have h1 : Nat.land (Nat.add (Nat.mul 2 x) 2) 1 = 0 :=
    (Nat.and_one_is_mod (2 * x + 2)).trans (by omega)
  have h2 : Nat.shiftRight (Nat.add (Nat.mul 2 x) 2) 1 = x + 1 :=
    (Nat.shiftRight_eq_div_pow (2 * x + 2) 1).trans (by omega)
  unfold val
  rw [h0, h1, h2]
  rfl

theorem val_mid (RT MT : Nat → Nat) (m : Nat) : val RT MT (Nat.add (Nat.mul 2 m) 1) = MT m := by
  have h0 : Nat.beq (Nat.add (Nat.mul 2 m) 1) 0 = false := nBf (by
    change 2 * m + 1 ≠ 0
    omega)
  have h1 : Nat.land (Nat.add (Nat.mul 2 m) 1) 1 = 1 :=
    (Nat.and_one_is_mod (2 * m + 1)).trans (by omega)
  have h2 : Nat.shiftRight (Nat.add (Nat.mul 2 m) 1) 1 = m :=
    (Nat.shiftRight_eq_div_pow (2 * m + 1) 1).trans (by omega)
  unfold val
  rw [h0, h1, h2]
  rfl

theorem run_good {RT MT : Nat → Nat} {PR k i e : Nat}
    (hop : ∀ x, opOK PR k i x = true → x ≠ k → Gd (RT x)) :
    ∀ (ins : List (Nat × Nat × Nat)) (v : Nat), Gd v → runK RT MT PR k i e ins v = true →
      Gd (val RT MT e)
  | [], v, hv, h => by
    have : v = val RT MT e := Nat.eq_of_beq_eq_true h
    rw [← this]
    exact hv
  | (op, a, b) :: ins, v, hv, h => by
    have h' : bAnd(stepOK RT MT PR k i e v op a b,
        strictB (stepV RT MT k e v op a b) (runK RT MT PR k i e ins)) = true := h
    obtain ⟨hs, hr⟩ := bA h'
    rw [sB] at hr
    refine run_good hop ins _ ?_ hr
    have hs' : bAnd(Nat.blt op (nat_lit 3), bAnd(opOK PR k i a,
      Bool.rec (Bool.rec
        ((fun V => bAnd(Nat.beq (pc (Bool.rec (RT a) v (Nat.beq a k)) V) pid,
            Nat.beq (pc V (Bool.rec (RT a) v (Nat.beq a k))) pid)) (val RT MT e))
        true (Nat.beq op (nat_lit 1)))
      (opOK PR k i b) (Nat.beq op (nat_lit 0)))) = true := hs
    obtain ⟨-, ha, hrest⟩ := And.intro (bA hs').1 (bA (bA hs').2)
    have hg : ∀ x, opOK PR k i x = true → Gd (Bool.rec (RT x) v (Nat.beq x k)) := by
      intro x hx
      cases hxk : Nat.beq x k
      · exact hop x hx (Nat.ne_of_beq_eq_false hxk)
      · exact hv
    have hsa := hg a ha
    change Gd (Bool.rec (Bool.rec (val RT MT e) (pw (Bool.rec (RT a) v (Nat.beq a k)) b)
      (Nat.beq op 1)) (pc (Bool.rec (RT a) v (Nat.beq a k)) (Bool.rec (RT b) v (Nat.beq b k)))
      (Nat.beq op 0))
    generalize Bool.rec (motive := fun _ => Nat) (RT a) v (Nat.beq a k) = sa at hsa hrest ⊢
    cases h0 : Nat.beq op 0
    · rw [h0] at hrest
      cases h1 : Nat.beq op 1
      · rw [h1] at hrest
        obtain ⟨-, hinv⟩ := bA hrest
        exact gd_inv hsa (Nat.eq_of_beq_eq_true hinv)
      · exact gd_pw hsa b
    · rw [h0] at hrest
      exact gd_pc hsa (hg b hrest)

theorem chunk_good {RT MT : Nat → Nat} {PR PM NM c : Nat}
    {ch : Nat × Nat × Nat × List (Nat × Nat × Nat)} (h : chunkK RT MT PR PM NM c ch = true)
    (hR : ∀ x, x < 109 → (x < 19 ∨ kf PR x < c) → Gd (RT x))
    (hM : ∀ m < NM, kf PM m < c → Gd (MT m)) : Gd (val RT MT (endOf ch)) := by
  obtain ⟨k, s, e, ins⟩ := ch
  dsimp only [chunkK] at h
  obtain ⟨-, h2⟩ := bA h
  obtain ⟨-, h3⟩ := bA h2
  obtain ⟨hst, h4⟩ := bA h3
  obtain ⟨-, hrun⟩ := bA h4
  rw [sN] at hrun
  have hrun' : runK RT MT PR k c e ins (val RT MT s) = true := by
    cases hr : runK RT MT PR k c e ins (val RT MT s)
    · rw [hr] at hrun
      exact fne hrun
    · rfl
  have hs : Gd (val RT MT s) := by
    cases hs0 : Nat.beq s 0
    · rw [hs0] at hst
      cases hs1 : Nat.beq (Nat.land s 1) 1
      · rw [hs1] at hst
        exact fne hst
      · rw [hs1] at hst
        obtain ⟨hm1, hm2⟩ := bA hst
        have hv : val RT MT s = MT (Nat.shiftRight s 1) := by
          unfold val
          rw [hs0, hs1]
        rw [hv]
        exact hM _ (nLt hm1) (nLt hm2)
    · rw [Nat.eq_of_beq_eq_true hs0]
      exact gd_pid
  refine run_good (fun x hx hxk => ?_) ins _ hs hrun'
  have hx' : bAnd(Nat.blt x (nat_lit 109),
      Bool.rec (Bool.rec (Nat.blt (kf PR x) c) true (Nat.blt x (nat_lit 19))) true
        (Nat.beq x k)) = true := hx
  obtain ⟨hx1, hx2⟩ := bA hx'
  have hne : Nat.beq x k = false := nBf hxk
  rw [hne] at hx2
  refine hR x (nLt hx1) ?_
  cases h19 : Nat.blt x 19
  · rw [h19] at hx2
    exact Or.inr (nLt hx2)
  · exact Or.inl (nLt h19)

theorem nth_eq : ∀ (l : List Nat) (j : Nat), nth l j = l.getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, j + 1 => nth_eq l j

theorem ends_eq : ∀ l : List (Nat × Nat × Nat × List (Nat × Nat × Nat)), ends l = l.map endOf
  | [] => rfl
  | c :: l => by
    have h : ends (c :: l) = endOf c :: ends l := rfl
    rw [h, ends_eq l]
    rfl

theorem chunksK_get {RT MT : Nat → Nat} {PR PM NM : Nat} :
    ∀ (l : List (Nat × Nat × Nat × List (Nat × Nat × Nat))) (i : Nat),
      chunksK RT MT PR PM NM l i = true →
      ∀ t (ht : t < l.length), chunkK RT MT PR PM NM (i + t) l[t] = true
  | [], _, _, t, ht => absurd ht (by simp)
  | c :: l, i, h, t, ht => by
    have h' : bAnd(chunkK RT MT PR PM NM i c, chunksK RT MT PR PM NM l (Nat.succ i)) = true := h
    obtain ⟨h1, h2⟩ := bA h'
    cases t with
    | zero => exact h1
    | succ t =>
      have e : i + (t + 1) = Nat.succ i + t := by omega
      rw [e]
      exact chunksK_get l _ h2 t (by simpa using ht)

theorem slp_good {RT MT : Nat → Nat} {PR PM NM : Nat}
    {chunks : List (Nat × Nat × Nat × List (Nat × Nat × Nat))}
    (hI : ∀ r < 19, Gd (RT r)) (hlen : chunks.length ≤ 152)
    (hslp : ∀ j < 19, chunksK RT MT PR PM NM ((chunks.drop (Nat.mul 8 j)).take 8) (Nat.mul 8 j) =
      true)
    (hcov : coverK PR (ends chunks) = true) (hcovM : coverM PM NM (ends chunks) = true) :
    ∀ x < 109, Gd (RT x) := by
  have hch : ∀ c (hc : c < chunks.length), chunkK RT MT PR PM NM c chunks[c] = true := by
    intro c hc
    have hj : c / 8 < 19 := by omega
    have h := chunksK_get _ _ (hslp (c / 8) hj) (c % 8) (by
      simp only [List.length_take, List.length_drop]
      have : Nat.mul 8 (c / 8) = 8 * (c / 8) := rfl
      omega)
    have e1 : Nat.mul 8 (c / 8) + c % 8 = c := by
      have : Nat.mul 8 (c / 8) = 8 * (c / 8) := rfl
      omega
    rw [e1] at h
    simp only [List.getElem_take, List.getElem_drop] at h
    convert h using 2
    congr 1
    omega
  have hend : ∀ c v, (ends chunks).getD c 0 = v → v ≠ 0 →
      ∃ hc : c < chunks.length, endOf chunks[c] = v := by
    intro c v h hv
    rw [ends_eq] at h
    by_cases hc : c < chunks.length
    · refine ⟨hc, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simpa using hc)] at h
      simpa using h
    · rw [List.getD_eq_default _ _ (by simpa using hc)] at h
      exact absurd h.symm hv
  have key : ∀ c, (∀ x, 19 ≤ x → x < 109 → kf PR x = c → Gd (RT x)) ∧
      (∀ m < NM, kf PM m = c → Gd (MT m)) := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
    have hR : ∀ x, x < 109 → (x < 19 ∨ kf PR x < c) → Gd (RT x) := by
      intro x hx h
      rcases Nat.lt_or_ge x 19 with h19 | h19
      · exact hI x h19
      · rcases h with h | h
        · omega
        · exact (ih _ h).1 x h19 hx rfl
    have hM : ∀ m < NM, kf PM m < c → Gd (MT m) := fun m hm h => (ih _ h).2 m hm rfl
    refine ⟨fun x h19 hx hxc => ?_, fun m hm hmc => ?_⟩
    · have h := allBlk_spec hcov (x - 19) (by
        have : x - 19 < 90 := by omega
        exact this)
      have e : Nat.add 19 (x - 19) = x := by
        change 19 + (x - 19) = x
        omega
      rw [e, hxc, nth_eq] at h
      obtain ⟨hc, he⟩ := hend c _ (Nat.eq_of_beq_eq_true h) (by simp)
      have := chunk_good (hch c hc) hR hM
      rw [he, val_reg] at this
      exact this
    · have h := allBlk_spec hcovM m hm
      have e : Nat.add 0 m = m := Nat.zero_add m
      rw [e, hmc, nth_eq] at h
      obtain ⟨hc, he⟩ := hend c _ (Nat.eq_of_beq_eq_true h) (by simp)
      have := chunk_good (hch c hc) hR hM
      rw [he, val_mid] at this
      exact this
  intro x hx
  rcases Nat.lt_or_ge x 19 with h19 | h19
  · exact hI x h19
  · exact (key _).1 x h19 hx rfl

noncomputable def ent (g : Nat → Gp) (PA LA i : Nat) : Gp :=
  if h : i ≠ 0 ∧ kf PA i < i then g (kf LA i) * ent g PA LA (kf PA i) else 1
termination_by i
decreasing_by exact h.2

theorem ent_zero (g : Nat → Gp) (PA LA : Nat) : ent g PA LA 0 = 1 := by
  rw [ent]
  simp

theorem ent_pos (g : Nat → Gp) (PA LA : Nat) {i : Nat} (h1 : i ≠ 0) (h2 : kf PA i < i) :
    ent g PA LA i = g (kf LA i) * ent g PA LA (kf PA i) := by
  rw [ent, dif_pos ⟨h1, h2⟩]

noncomputable def bsr (K SR t : Nat) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false) (fun _ ih lo hi =>
    Bool.rec
      ((fun mid => (fun v => Bool.rec (Bool.rec (ih lo mid) (ih (Nat.succ mid) hi) (Nat.blt v t))
        true (Nat.beq v t)) (keyAt K (kf SR mid))) (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)))
      false (Nat.ble hi lo))

theorem memK_eq (K SR N t : Nat) : memK K SR N t = bsr K SR t (nat_lit 14) (nat_lit 0) N := rfl

theorem kf_lt (X t : Nat) : kf X t < 8192 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right) (by norm_num)

theorem mid_eq (lo hi : Nat) : Nat.shiftRight (Nat.add lo hi) 1 = (lo + hi) / 2 :=
  (Nat.shiftRight_eq_div_pow (lo + hi) 1).trans (by norm_num)

theorem bsr_sound (K SR t : Nat) : ∀ f lo hi, bsr K SR t f lo hi = true →
    ∃ j, lo ≤ j ∧ j < hi ∧ keyAt K (kf SR j) = t
  | 0, _, _, h => fne h
  | f + 1, lo, hi, h => by
    have h' : Bool.rec
      ((fun mid => (fun v => Bool.rec (Bool.rec (bsr K SR t f lo mid)
          (bsr K SR t f (Nat.succ mid) hi) (Nat.blt v t))
        true (Nat.beq v t)) (keyAt K (kf SR mid))) (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)))
      false (Nat.ble hi lo) = true := h
    cases hle : Nat.ble hi lo
    · rw [hle] at h'
      have hlt : lo < hi := by
        exact nLEf hle
      dsimp only at h'
      rw [mid_eq] at h'
      cases hv : Nat.beq (keyAt K (kf SR ((lo + hi) / 2))) t
      · rw [hv] at h'
        cases hb : Nat.blt (keyAt K (kf SR ((lo + hi) / 2))) t
        · rw [hb] at h'
          obtain ⟨j, h1, h2, h3⟩ := bsr_sound K SR t f lo _ h'
          exact ⟨j, h1, by omega, h3⟩
        · rw [hb] at h'
          obtain ⟨j, h1, h2, h3⟩ := bsr_sound K SR t f _ hi h'
          exact ⟨j, by omega, h2, h3⟩
      · exact ⟨(lo + hi) / 2, by omega, by omega, Nat.eq_of_beq_eq_true hv⟩
    · rw [hle] at h'
      exact fne h'

theorem bsr_complete (K SR t N : Nat)
    (hmono : ∀ j j', j < j' → j' < N → keyAt K (kf SR j) < keyAt K (kf SR j')) :
    ∀ f lo hi, hi - lo < 2 ^ f → hi ≤ N → ∀ j, lo ≤ j → j < hi → keyAt K (kf SR j) = t →
      bsr K SR t f lo hi = true
  | 0, lo, hi, hs, _, j, h1, h2, _ => by
    have : hi - lo < 1 := by simpa using hs
    omega
  | f + 1, lo, hi, hs, hN, j, h1, h2, h3 => by
    change Bool.rec
      ((fun mid => (fun v => Bool.rec (Bool.rec (bsr K SR t f lo mid)
          (bsr K SR t f (Nat.succ mid) hi) (Nat.blt v t))
        true (Nat.beq v t)) (keyAt K (kf SR mid))) (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)))
      false (Nat.ble hi lo) = true
    have hle : Nat.ble hi lo = false := nLEf' (by omega)
    rw [hle]
    dsimp only
    rw [mid_eq]
    rw [pow_succ] at hs
    cases hv : Nat.beq (keyAt K (kf SR ((lo + hi) / 2))) t
    · have hne : keyAt K (kf SR ((lo + hi) / 2)) ≠ t := Nat.ne_of_beq_eq_false hv
      cases hb : Nat.blt (keyAt K (kf SR ((lo + hi) / 2))) t
      · have hge : t < keyAt K (kf SR ((lo + hi) / 2)) := by
          have := nLtF hb
          omega
        have hj : j < (lo + hi) / 2 := by
          by_contra hc
          rcases Nat.lt_or_ge ((lo + hi) / 2) j with hc' | hc'
          · have := hmono _ _ hc' (by omega)
            omega
          · have : j = (lo + hi) / 2 := by omega
            subst this
            exact hne h3
        exact bsr_complete K SR t N hmono f lo _ (by omega) (by omega) j h1 hj h3
      · have hlt : keyAt K (kf SR ((lo + hi) / 2)) < t := nLt hb
        have hj : (lo + hi) / 2 < j := by
          by_contra hc
          rcases Nat.lt_or_ge j ((lo + hi) / 2) with hc' | hc'
          · have := hmono _ _ hc' (by omega)
            omega
          · have : j = (lo + hi) / 2 := by omega
            subst this
            exact hne h3
        exact bsr_complete K SR t N hmono f _ hi (by omega) hN j hj h2 h3
    · rfl

noncomputable def atF (G : Nat → Nat) (PA LA : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => Bool.rec (ap (G (kf LA i)) (ih (kf PA i) p)) p (Nat.beq i (nat_lit 0)))

noncomputable def atIF (GI : Nat → Nat) (PA LA : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => Bool.rec (ih (kf PA i) (ap (GI (kf LA i)) p)) p (Nat.beq i (nat_lit 0)))

theorem atE_eq (G : Nat → Nat) (PA LA i p : Nat) : atE G PA LA i p = atF G PA LA i i p := rfl

theorem atIE_eq (GI : Nat → Nat) (PA LA i p : Nat) : atIE GI PA LA i p = atIF GI PA LA i i p :=
  rfl

theorem atF_succ (G : Nat → Nat) (PA LA n i p : Nat) : atF G PA LA (n + 1) i p =
    Bool.rec (ap (G (kf LA i)) (atF G PA LA n (kf PA i) p)) p (Nat.beq i 0) := rfl

theorem atIF_succ (GI : Nat → Nat) (PA LA n i p : Nat) : atIF GI PA LA (n + 1) i p =
    Bool.rec (atIF GI PA LA n (kf PA i) (ap (GI (kf LA i)) p)) p (Nat.beq i 0) := rfl

theorem len_eq : ∀ l : List Nat, len l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (len_eq l)

theorem enum_core (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 → g 2 = 2 → g = 1)
    {g : Nat → Gp} {G GI : Nat → Nat} {m N K PA LA SR : Nat}
    (hG : ∀ j < m, Tb (G j) (g j) ∧ g j ∈ j3R) (hGI : ∀ j < m, Tb (GI j) (g j)⁻¹)
    (hN : 1 ≤ N) (h0 : keyAt K 0 = key1) (hlast : kf SR (N - 1) < N)
    (hent : ∀ i < N, i ≠ 0 → kf PA i < i ∧ kf LA i < m ∧
      keyAt K i = keyL (G (kf LA i)) (keyAt K (kf PA i)))
    (hsrt : ∀ i, i + 1 < N → kf SR i < N ∧ kf SR (i + 1) < N ∧
      keyAt K (kf SR i) < keyAt K (kf SR (i + 1)))
    (hclo : ∀ i < N, ∀ j < m, memK K SR N (keyL (G j) (keyAt K i)) = true) :
    (∀ i < N, keyAt K i = keyG (ent g PA LA i) ∧ ent g PA LA i ∈ j3R ∧
      ent g PA LA i ∈ Subgroup.closure (g '' {j | j < m})) ∧
    (∀ y ∈ Subgroup.closure (g '' {j | j < m}), ∃ i < N, ent g PA LA i = y) ∧
    (∀ i < N, ∀ i' < N, ent g PA LA i = ent g PA LA i' → i = i') ∧
    (∀ t, memK K SR N t = true ↔ ∃ i < N, keyAt K i = t) ∧
    (∀ i < N, ∀ p : Fin 6156, atE G PA LA i p = (ent g PA LA i p : Nat)) ∧
    (∀ i < N, ∀ p : Fin 6156, atIE GI PA LA i p = ((ent g PA LA i)⁻¹ p : Nat)) := by
  set x := ent g PA LA with hx
  have hk : ∀ i < N, keyAt K i = keyG (x i) ∧ x i ∈ j3R ∧
      x i ∈ Subgroup.closure (g '' {j | j < m}) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hx, ent_zero, h0, key1_eq]
      exact ⟨rfl, one_mem _, one_mem _⟩
    · obtain ⟨hp, hl, hkey⟩ := hent i hi (by omega)
      obtain ⟨k1, k2, k3⟩ := ih _ hp (by omega)
      rw [hx, ent_pos g PA LA (by omega) hp, hkey, k1, keyL_eq (hG _ hl).1]
      exact ⟨rfl, mul_mem (hG _ hl).2 k2,
        mul_mem (Subgroup.subset_closure ⟨_, hl, rfl⟩) k3⟩
  have hσ : ∀ j < N, kf SR j < N := by
    intro j hj
    rcases Nat.lt_or_ge (j + 1) N with h | h
    · exact (hsrt j h).1
    · have : j = N - 1 := by omega
      rw [this]
      exact hlast
  have hmono : ∀ j j', j < j' → j' < N → keyAt K (kf SR j) < keyAt K (kf SR j') := by
    intro j j' hjj hj'
    induction j' with
    | zero => omega
    | succ j' ih =>
      rcases Nat.lt_or_ge j j' with h | h
      · exact (ih h (by omega)).trans (hsrt j' hj').2.2
      · have : j = j' := by omega
        subst this
        exact (hsrt j hj').2.2
  have hσinj : ∀ j < N, ∀ j' < N, kf SR j = kf SR j' → j = j' := by
    intro j hj j' hj' e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hmono _ _ h hj'
      rw [e] at this
      exact lt_irrefl _ this
    · have := hmono _ _ h hj
      rw [e] at this
      exact lt_irrefl _ this
  have hσsurj : ∀ i < N, ∃ j < N, kf SR j = i := by
    intro i hi
    obtain ⟨j, hj, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N)
      (t := Finset.range N) (fun j _ => kf SR j)
      (fun j hj => Finset.mem_range.2 (hσ j (Finset.mem_range.1 hj)))
      (fun j j' hj hj' e => hσinj j (Finset.mem_range.1 hj) j' (Finset.mem_range.1 hj') e)
      le_rfl i (Finset.mem_range.2 hi)
    exact ⟨j, Finset.mem_range.1 hj, e.symm⟩
  have hN8 : N ≤ 8192 := by
    have := Finset.card_le_card_of_injOn (s := Finset.range N) (t := Finset.range 8192)
      (fun j => kf SR j) (fun j _ => Finset.mem_range.2 (kf_lt SR j))
      (fun j hj j' hj' e => hσinj j (Finset.mem_range.1 hj) j' (Finset.mem_range.1 hj') e)
    simpa using this
  have hkinj : ∀ i < N, ∀ i' < N, keyAt K i = keyAt K i' → i = i' := by
    intro i hi i' hi' e
    obtain ⟨j, hj, rfl⟩ := hσsurj i hi
    obtain ⟨j', hj', rfl⟩ := hσsurj i' hi'
    by_contra hne
    have hne' : j ≠ j' := fun h => hne (by rw [h])
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact lt_irrefl _ (e ▸ hmono _ _ h hj')
    · exact lt_irrefl _ (e ▸ hmono _ _ h hj)
  have hmem : ∀ t, memK K SR N t = true ↔ ∃ i < N, keyAt K i = t := by
    intro t
    rw [memK_eq]
    constructor
    · intro h
      obtain ⟨j, -, hj, e⟩ := bsr_sound K SR t 14 0 N h
      exact ⟨_, hσ j hj, e⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, hj, rfl⟩ := hσsurj i hi
      exact bsr_complete K SR _ N hmono 14 0 N (by norm_num; omega) le_rfl j (Nat.zero_le _) hj
        rfl
  have hcl : ∀ i < N, ∀ j < m, ∃ i' < N, x i' = g j * x i := by
    intro i hi j hj
    obtain ⟨i', hi', e⟩ := (hmem _).1 (hclo i hi j hj)
    refine ⟨i', hi', eq_of_key hB (hk i' hi').2.1 (mul_mem (hG j hj).2 (hk i hi).2.1) ?_⟩
    rw [← (hk i' hi').1, e, (hk i hi).1, keyL_eq (hG j hj).1]
  have hinj : ∀ i < N, ∀ i' < N, x i = x i' → i = i' := by
    intro i hi i' hi' e
    refine hkinj i hi i' hi' ?_
    rw [(hk i hi).1, (hk i' hi').1, e]
  set X : Set Gp := x '' {i | i < N} with hX
  have hXf : X.Finite := (Set.finite_lt_nat N).image _
  have hcov : ∀ y ∈ Subgroup.closure (g '' {j | j < m}), ∀ z ∈ X, y * z ∈ X := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨i', hi', e⟩ := hcl i hi j hj
      exact ⟨i', hi', e⟩
    | one => intro z hz; simpa using hz
    | mul a b _ _ ha hb => intro z hz; rw [mul_assoc]; exact ha _ (hb z hz)
    | inv a _ ha =>
      intro z hz
      have hbij := (hXf.injOn_iff_bijOn_of_mapsTo (f := fun w => a * w) ha).1
        (fun w _ w' _ e => mul_left_cancel e)
      obtain ⟨w, hw, e⟩ := hbij.surjOn hz
      have : a⁻¹ * z = w := by rw [← e]; simp
      rw [this]
      exact hw
  have h0X : (1 : Gp) ∈ X := ⟨0, hN, by rw [hx, ent_zero]⟩
  have hatE : ∀ n i, i < N → i ≤ n → ∀ p : Fin 6156, atF G PA LA n i p = (x i p : Nat) := by
    intro n
    induction n with
    | zero =>
      intro i hi hin p
      have : i = 0 := by omega
      subst this
      rw [hx, ent_zero]
      rfl
    | succ n ih =>
      intro i hi hin p
      rw [atF_succ]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hx, ent_zero]
        rfl
      · have hb : Nat.beq i 0 = false := nBf (by omega)
        rw [hb]
        obtain ⟨hp, hl, -⟩ := hent i hi (by omega)
        rw [ih _ (by omega) (by omega) p, (hG _ hl).1, hx, ent_pos g PA LA (by omega) hp]
        rfl
  have hatIE : ∀ n i, i < N → i ≤ n → ∀ p : Fin 6156,
      atIF GI PA LA n i p = ((x i)⁻¹ p : Nat) := by
    intro n
    induction n with
    | zero =>
      intro i hi hin p
      have : i = 0 := by omega
      subst this
      rw [hx, ent_zero]
      rfl
    | succ n ih =>
      intro i hi hin p
      rw [atIF_succ]
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hx, ent_zero]
        rfl
      · have hb : Nat.beq i 0 = false := nBf (by omega)
        rw [hb]
        obtain ⟨hp, hl, -⟩ := hent i hi (by omega)
        rw [hGI _ hl p, ih _ (by omega) (by omega), hx, ent_pos g PA LA (by omega) hp, mul_inv_rev]
        rfl
  refine ⟨hk, fun y hy => ?_, hinj, hmem, fun i hi p => (atE_eq _ _ _ _ _).trans
    (hatE i i hi le_rfl p), fun i hi p => (atIE_eq _ _ _ _ _).trans (hatIE i i hi le_rfl p)⟩
  have := hcov y hy 1 h0X
  rw [mul_one] at this
  obtain ⟨i, hi, e⟩ := this
  exact ⟨i, hi, e⟩

theorem nth_get {l : List Nat} {j : Nat} (hj : j < l.length) : nth l j = l[j] := by
  rw [nth_eq, List.getD_eq_getElem _ _ hj]

theorem enum_glue (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 → g 2 = 2 → g = 1)
    {RT ET : Nat → Nat} {D : TData} {Rg : Nat → Gp}
    (hRg : ∀ x < 109, Tb (RT x) (Rg x) ∧ Rg x ∈ j3R) {e : Nat}
    (hh : enumHeadK RT ET D e = true)
    (hp : ∀ j < cardOf D e / 512 + 1, enumPartK RT ET D e (Nat.mul 512 j) 512 = true) :
    e < D.enums.length ∧ ∃ x : Nat → Gp,
      (∀ i < cardOf D e, keyAt (ET (Nat.mul 4 e)) i = keyG (x i) ∧ x i ∈ j3R ∧
        x i ∈ Ksub Rg (gensOf D e)) ∧
      (∀ y ∈ Ksub Rg (gensOf D e), ∃ i < cardOf D e, x i = y) ∧
      (∀ i < cardOf D e, ∀ i' < cardOf D e, x i = x i' → i = i') ∧
      (∀ t, memK (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 3)) (cardOf D e) t = true ↔
        ∃ i < cardOf D e, keyAt (ET (Nat.mul 4 e)) i = t) ∧
      (∀ i < cardOf D e, ∀ p : Fin 6156, atE (gT RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1))
        (ET (Nat.add (Nat.mul 4 e) 2)) i p = (x i p : Nat)) ∧
      (∀ i < cardOf D e, ∀ p : Fin 6156, atIE (gTI RT (gensOf D e))
        (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)) i p = ((x i)⁻¹ p : Nat)) := by
  have hpart : ∀ i < cardOf D e,
      (i ≠ 0 → entK (gT RT (gensOf D e)) (len (gensOf D e)) (ET (Nat.mul 4 e))
        (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)) i = true) ∧
      (i + 1 < cardOf D e →
        srtK (cardOf D e) (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 3)) i = true) ∧
      cloK (gT RT (gensOf D e)) (len (gensOf D e)) (cardOf D e) (ET (Nat.mul 4 e))
        (ET (Nat.add (Nat.mul 4 e) 3)) i = true := by
    intro i hi
    have h1 := hp (i / 512) (Nat.lt_succ_of_le (Nat.div_le_div_right hi.le))
    dsimp only [enumPartK] at h1
    have h2 := allBlk_spec h1 (i % 512) (Nat.mod_lt _ (by norm_num))
    have e1 : Nat.add (Nat.mul 512 (i / 512)) (i % 512) = i := Nat.div_add_mod i 512
    rw [e1] at h2
    obtain ⟨h3, h4⟩ := bA h2
    obtain ⟨h4, h5⟩ := bA h4
    have hb : Nat.blt i (cardOf D e) = true := Nat.ble_eq_true_of_le hi
    refine ⟨fun hi0 => ?_, fun hi1 => ?_, ?_⟩
    · rw [nBf hi0, hb] at h3
      exact h3
    · have hb1 : Nat.blt (Nat.succ i) (cardOf D e) = true := Nat.ble_eq_true_of_le hi1
      rw [hb1] at h4
      exact h4
    · rw [hb] at h5
      exact h5
  dsimp only [enumHeadK] at hh
  obtain ⟨he, hh⟩ := bA hh
  obtain ⟨hN1, hh⟩ := bA hh
  obtain ⟨hk0, hh⟩ := bA hh
  obtain ⟨hlast, hgens⟩ := bA hh
  have he' : e < D.enums.length := by
    have := nLt he
    rwa [len_eq, List.length_map] at this
  refine ⟨he', ?_⟩
  generalize gensOf D e = gl at hpart hgens ⊢
  generalize cardOf D e = N at hpart hN1 hlast ⊢
  generalize ET (Nat.mul 4 e) = K at hpart hk0 ⊢
  generalize ET (Nat.add (Nat.mul 4 e) 1) = PA at hpart ⊢
  generalize ET (Nat.add (Nat.mul 4 e) 2) = LA at hpart ⊢
  generalize ET (Nat.add (Nat.mul 4 e) 3) = SR at hpart hlast ⊢
  have hG : ∀ j < len gl, Tb (gT RT gl j) (Rg (nth gl j)) ∧ Rg (nth gl j) ∈ j3R ∧
      Tb (gTI RT gl j) (Rg (nth gl j))⁻¹ ∧ nth gl j < 109 := by
    intro j hj
    have h1 := allBlk_spec hgens j hj
    have e0 : Nat.add 0 j = j := Nat.zero_add j
    rw [e0] at h1
    obtain ⟨h2, h3⟩ := bA h1
    obtain ⟨-, h4⟩ := bA h3
    have hr := hRg _ (nLt h2)
    exact ⟨hr.1, hr.2, tb_inv hr.1 (Nat.eq_of_beq_eq_true h4), nLt h2⟩
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := enum_core hB (g := fun j => Rg (nth gl j)) (G := gT RT gl)
    (GI := gTI RT gl) (m := len gl) (N := N) (K := K) (PA := PA) (LA := LA) (SR := SR)
    (fun j hj => ⟨(hG j hj).1, (hG j hj).2.1⟩) (fun j hj => (hG j hj).2.2.1)
    (Nat.le_of_ble_eq_true hN1) (Nat.eq_of_beq_eq_true hk0) (nLt hlast)
    (fun i hi hi0 => by
      have h := (hpart i hi).1 hi0
      dsimp only [entK] at h
      obtain ⟨h1, h2⟩ := bA h
      obtain ⟨h2, h3⟩ := bA h2
      exact ⟨nLt h1, nLt h2, Nat.eq_of_beq_eq_true h3⟩)
    (fun i hi => by
      have h := (hpart i (by omega)).2.1 hi
      dsimp only [srtK] at h
      obtain ⟨h1, h2⟩ := bA h
      obtain ⟨h2, h3⟩ := bA h2
      exact ⟨nLt h1, nLt h2, nLt h3⟩)
    (fun i hi j hj => by
      have h := (hpart i hi).2.2
      dsimp only [cloK] at h
      have h1 := allBlk_spec h j hj
      have e0 : Nat.add 0 j = j := Nat.zero_add j
      rw [e0] at h1
      exact h1)
  have hcl : Subgroup.closure ((fun j => Rg (nth gl j)) '' {j | j < len gl}) = Ksub Rg gl := by
    unfold Ksub
    congr 1
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : j < gl.length := by rw [← len_eq]; exact hj
      exact ⟨nth gl j, by rw [nth_get hj']; exact List.getElem_mem hj', rfl⟩
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
      exact ⟨j, by rw [len_eq]; exact hj, by simp only; rw [nth_get hj]⟩
  rw [hcl] at c1 c2
  exact ⟨_, c1, c2, c3, c4, c5, c6⟩

theorem prodAt_eq {RT : Nat → Nat} {Rg : Nat → Gp}
    (hRg : ∀ x < 109, Tb (RT x) (Rg x) ∧ Rg x ∈ j3R) :
    ∀ l : List Nat, regsLt l = true → (∀ p : Fin 6156, prodAt RT l p = (prodG Rg l p : Nat)) ∧
      prodG Rg l ∈ j3R
  | [], _ => ⟨fun p => rfl, one_mem _⟩
  | r :: l, h => by
    have h' : bAnd(Nat.blt r (nat_lit 109), regsLt l) = true := h
    obtain ⟨h1, h2⟩ := bA h'
    obtain ⟨ih1, ih2⟩ := prodAt_eq hRg l h2
    have e : prodG Rg (r :: l) = Rg r * prodG Rg l := by simp [prodG]
    rw [e]
    refine ⟨fun p => ?_, mul_mem (hRg r (nLt h1)).2 ih2⟩
    change ap (RT r) (prodAt RT l p) = _
    rw [ih1 p, (hRg r (nLt h1)).1]
    rfl

theorem wordAt_eq {PS PSI : Nat → Nat}
    (hS : ∀ h < 5, Tb (PS h) (j3StrongPerm h) ∧ Tb (PSI h) (j3StrongPerm h)⁻¹)
    (hSP : ∀ h < 5, j3StrongPerm h ∈ j3P) :
    ∀ wd : List Nat, lettersLt wd = true →
      ∃ w ∈ j3P, ∀ p : Fin 6156, wordAt PS PSI wd p = (w p : Nat)
  | [], _ => ⟨1, one_mem _, fun p => rfl⟩
  | a :: wd, h => by
    have h' : bAnd(Nat.blt a (nat_lit 10), lettersLt wd) = true := h
    obtain ⟨h1, h2⟩ := bA h'
    obtain ⟨w, hw, hwp⟩ := wordAt_eq hS hSP wd h2
    have ha : Nat.shiftRight a 1 < 5 := (Nat.shiftRight_eq_div_pow a 1).trans_lt (by
      have : a < 10 := nLt h1
      omega)
    have hs := hS _ ha
    cases hl : Nat.beq (Nat.land a 1) 1
    · refine ⟨j3StrongPerm (Nat.shiftRight a 1) * w, mul_mem (hSP _ ha) hw, fun p => ?_⟩
      change ap (Bool.rec (PS (Nat.shiftRight a 1)) (PSI (Nat.shiftRight a 1))
        (Nat.beq (Nat.land a 1) 1)) (wordAt PS PSI wd p) = _
      rw [hl, hwp p, Equiv.Perm.mul_apply]
      exact hs.1 (w p)
    · refine ⟨(j3StrongPerm (Nat.shiftRight a 1))⁻¹ * w, mul_mem (inv_mem (hSP _ ha)) hw,
        fun p => ?_⟩
      change ap (Bool.rec (PS (Nat.shiftRight a 1)) (PSI (Nat.shiftRight a 1))
        (Nat.beq (Nat.land a 1) 1)) (wordAt PS PSI wd p) = _
      rw [hl, hwp p, Equiv.Perm.mul_apply]
      exact hs.2 (w p)

theorem powAt_eq {X : Nat} {g : Gp} (hX : Tb X g) :
    ∀ m (p : Fin 6156), powAt X m p = ((g ^ m) p : Nat)
  | 0, p => rfl
  | m + 1, p => by
    change ap X (powAt X m p) = _
    rw [powAt_eq hX m p, hX, pow_succ']
    rfl

theorem prime_of {m : Nat} (h : primeK m = true) : m.Prime := by
  dsimp only [primeK] at h
  obtain ⟨h1, h2⟩ := bA h
  have h2' := allBlk_spec h2
  refine Nat.prime_def_lt'.2 ⟨Nat.le_of_ble_eq_true h1, fun d hd hdm hdvd => ?_⟩
  have h3 := h2' (d - 2) (by
    have : d - 2 < m - 2 := by omega
    exact this)
  have e : Nat.add 2 (d - 2) = d := by
    change 2 + (d - 2) = d
    omega
  rw [e] at h3
  have h4 : Nat.beq (Nat.mod m d) 0 = true := by
    have : Nat.mod m d = 0 := Nat.mod_eq_zero_of_dvd hdvd
    rw [this]
    rfl
  rw [h4] at h3
  exact fne h3

theorem allB_iff {u v : Gp} {F H : Nat → Nat} (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 →
      g 2 = 2 → g = 1) (hu : u ∈ j3R) (hv : v ∈ j3R)
    (hF : ∀ p : Fin 6156, F p = u p) (hH : ∀ p : Fin 6156, H p = v p) :
    allB (fun b => Nat.beq (F b) (H b)) = true ↔ u = v := by
  constructor
  · intro h
    dsimp only [allB] at h
    obtain ⟨h0, h⟩ := bA h
    obtain ⟨h1, h⟩ := bA h
    obtain ⟨h3, h2⟩ := bA h
    refine eq_of_key hB hu hv ?_
    have e0 : u 0 = v 0 := Fin.ext ((hF 0).symm.trans ((Nat.eq_of_beq_eq_true h0).trans (hH 0)))
    have e1 : u 1 = v 1 := Fin.ext ((hF 1).symm.trans ((Nat.eq_of_beq_eq_true h1).trans (hH 1)))
    have e3 : u 3 = v 3 := Fin.ext ((hF 3).symm.trans ((Nat.eq_of_beq_eq_true h3).trans (hH 3)))
    have e2 : u 2 = v 2 := Fin.ext ((hF 2).symm.trans ((Nat.eq_of_beq_eq_true h2).trans (hH 2)))
    unfold keyG
    rw [e0, e1, e3, e2]
  · rintro rfl
    have hb : ∀ p : Fin 6156, Nat.beq (F p) (H p) = true := fun p => by
      rw [hF p, hH p]
      exact Nat.beq_refl _
    exact (bAnd_iff _ _).2 ⟨hb 0, (bAnd_iff _ _).2 ⟨hb 1, (bAnd_iff _ _).2 ⟨hb 3, hb 2⟩⟩⟩

theorem cond_iff (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 → g 2 = 2 → g = 1)
    {RT ET : Nat → Nat} {D : TData} {Rg : Nat → Gp}
    (hRg : ∀ x < 109, Tb (RT x) (Rg x) ∧ Rg x ∈ j3R)
    (hmemE : ∀ e < D.enums.length, ∀ z ∈ j3R,
      memE ET D e (keyG z) = true ↔ z ∈ Ksub Rg (D.enums[e]!).1)
    {y : Gp} (hy : y ∈ j3R) {k : Nat} (hk : k = keyG y) {fx fxi : Nat → Nat}
    (hfx : ∀ p : Fin 6156, fx p = y p) (hfxi : ∀ p : Fin 6156, fxi p = y⁻¹ p) :
    ∀ c : Cond, c.wfB 109 D.enums.length = true →
      (condK RT ET D k fx fxi c = true ↔ c.sem Rg (fun e => Ksub Rg (D.enums[e]!).1) y)
  | .comm r, hw => by
    simp only [Cond.wfB, decide_eq_true_eq] at hw
    have hr := hRg r hw
    change bAnd(Nat.blt r (nat_lit 109),
      allB (fun b => Nat.beq (fx (ap (RT r) b)) (ap (RT r) (fx b)))) = true ↔ _
    have hb : Nat.blt r 109 = true := Nat.ble_eq_true_of_le hw
    rw [hb]
    change allB _ = true ↔ y * Rg r = Rg r * y
    refine allB_iff hB (mul_mem hy hr.2) (mul_mem hr.2 hy) (fun p => ?_) (fun p => ?_)
    · rw [hr.1, hfx]
      rfl
    · rw [hfx, hr.1]
      rfl
  | .commM w r, hw => by
    simp only [Cond.wfB, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hr := hRg r hw.2
    have hwr := hRg w hw.1
    change bAnd(Nat.blt w (nat_lit 109), bAnd(Nat.blt r (nat_lit 109),
      allB (fun b => Nat.beq (fx (ap (RT w) (ap (RT r) b))) (ap (RT r) (fx (ap (RT w) b)))))) =
        true ↔ _
    have hb1 : Nat.blt w 109 = true := Nat.ble_eq_true_of_le hw.1
    have hb2 : Nat.blt r 109 = true := Nat.ble_eq_true_of_le hw.2
    rw [hb1, hb2]
    change allB _ = true ↔ (y * Rg w) * Rg r = Rg r * (y * Rg w)
    refine allB_iff hB (mul_mem (mul_mem hy hwr.2) hr.2) (mul_mem hr.2 (mul_mem hy hwr.2))
      (fun p => ?_) (fun p => ?_)
    · rw [hr.1, hwr.1, hfx]
      rfl
    · rw [hwr.1, hfx, hr.1]
      rfl
  | .memConj e r, hw => by
    simp only [Cond.wfB, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hr := hRg r hw.2
    change bAnd(Nat.blt r (nat_lit 109),
      memE ET D e (keyF (fun b => fx (ap (RT r) (fxi b))))) = true ↔ _
    have hb : Nat.blt r 109 = true := Nat.ble_eq_true_of_le hw.2
    rw [hb]
    have hk : keyF (fun b => fx (ap (RT r) (fxi b))) = keyG (y * Rg r * y⁻¹) := keyF_eq (fun p => by
      rw [hfxi, hr.1, hfx]
      rfl)
    change memE ET D e _ = true ↔ y * Rg r * y⁻¹ ∈ _
    rw [hk]
    exact hmemE e hw.1 _ (mul_mem (mul_mem hy hr.2) (inv_mem hy))
  | .memSelf e, hw => by
    simp only [Cond.wfB, decide_eq_true_eq] at hw
    change memE ET D e k = true ↔ y ∈ _
    rw [hk]
    exact hmemE e hw y hy
  | .not c, hw => by
    have ih := cond_iff hB hRg hmemE hy hk hfx hfxi c hw
    change Bool.rec true false (condK RT ET D k fx fxi c) = true ↔ ¬ c.sem _ _ y
    rw [← ih]
    cases condK RT ET D k fx fxi c <;> simp
  | .and c d, hw => by
    simp only [Cond.wfB, Bool.and_eq_true] at hw
    have ihc := cond_iff hB hRg hmemE hy hk hfx hfxi c hw.1
    have ihd := cond_iff hB hRg hmemE hy hk hfx hfxi d hw.2
    change bAnd(condK RT ET D k fx fxi c, condK RT ET D k fx fxi d) = true ↔
      c.sem _ _ y ∧ d.sem _ _ y
    rw [bAnd_iff, ihc, ihd]
  | .imp c d, hw => by
    simp only [Cond.wfB, Bool.and_eq_true] at hw
    have ihc := cond_iff hB hRg hmemE hy hk hfx hfxi c hw.1
    have ihd := cond_iff hB hRg hmemE hy hk hfx hfxi d hw.2
    change Bool.rec true (condK RT ET D k fx fxi d) (condK RT ET D k fx fxi c) = true ↔
      (c.sem _ _ y → d.sem _ _ y)
    rw [← ihc, ← ihd]
    cases condK RT ET D k fx fxi c <;> simp

theorem cntK_succ (RT ET : Nat → Nat) (D : TData) (e : Nat) (c : Cond) (n : Nat) :
    cntK RT ET D e c 0 (n + 1) = cntK RT ET D e c 0 n +
      Bool.rec 0 1 (condK RT ET D (keyAt (ET (Nat.mul 4 e)) n)
        (atE (gT RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)) n)
        (atIE (gTI RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
          n) c) := by
  change strictN (cntK RT ET D e c 0 n) (fun s => Nat.add s (Bool.rec (nat_lit 0) (nat_lit 1)
    (condK RT ET D (keyAt (ET (Nat.mul 4 e)) (Nat.add 0 n))
      (atE (gT RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
        (Nat.add 0 n))
      (atIE (gTI RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
        (Nat.add 0 n)) c))) = _
  have e0 : Nat.add 0 n = n := Nat.zero_add n
  rw [sN, e0]
  rfl

theorem cntK_eq (RT ET : Nat → Nat) (D : TData) (e : Nat) (c : Cond) : ∀ n,
    cntK RT ET D e c 0 n = ((List.range n).filter fun j => condK RT ET D (keyAt (ET (Nat.mul 4 e)) j)
        (atE (gT RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)) j)
        (atIE (gTI RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
          j) c).length
  | 0 => rfl
  | n + 1 => by
    rw [cntK_succ, cntK_eq RT ET D e c n, List.range_succ, List.filter_append,
      List.length_append]
    congr 1
    cases h : condK RT ET D (keyAt (ET (Nat.mul 4 e)) n)
        (atE (gT RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)) n)
        (atIE (gTI RT (gensOf D e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
          n) c <;> simp only [List.filter, h, List.length_cons, List.length_nil, Nat.zero_add]

theorem ncard_eq {x : Nat → Gp} {N : Nat} {S : Set Gp} (hmem : ∀ i < N, x i ∈ S)
    (hcov : ∀ y ∈ S, ∃ i < N, x i = y) (hinj : ∀ i < N, ∀ i' < N, x i = x i' → i = i')
    (P : Gp → Prop) (F : Nat → Bool) (hF : ∀ i < N, F i = true ↔ P (x i)) :
    Set.ncard {y | y ∈ S ∧ P y} = ((List.range N).filter F).length := by
  have hset : {y | y ∈ S ∧ P y} = x '' {i | i < N ∧ F i = true} := by
    ext y
    constructor
    · rintro ⟨hy, hP⟩
      obtain ⟨i, hi, rfl⟩ := hcov y hy
      exact ⟨i, ⟨hi, (hF i hi).2 hP⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hFi⟩, rfl⟩
      exact ⟨hmem i hi, (hF i hi).1 hFi⟩
  have hinj' : Set.InjOn x {i | i < N ∧ F i = true} := fun a ha b hb hab =>
    hinj a ha.1 b hb.1 hab
  rw [hset, hinj'.ncard_image]
  have : {i | i < N ∧ F i = true} = ↑(((List.range N).filter F).toFinset) := by
    ext i
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup ((List.nodup_range).filter _)]

theorem facts_get {RT ET PS PSI : Nat → Nat} {D : TData} :
    ∀ (fs : List TFact) (W : List (List Nat)), factsK RT ET PS PSI D fs W = true →
      ∀ f ∈ fs, ∃ wd, factK RT ET PS PSI D wd f = true
  | [], _, _, f, hf => absurd hf (by simp)
  | f :: fs, W, h, f', hf => by
    have h' : bAnd(factK RT ET PS PSI D (W.headD []) f,
      factsK RT ET PS PSI D fs (Bool.rec W W.tail (isInP f))) = true := h
    obtain ⟨h1, h2⟩ := bA h'
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨_, h1⟩
    · exact facts_get fs _ h2 f' hf

end CFSG.KC.J3Tk

public section

namespace CFSG.KC.J3Tk

open CFSG.Monster.B.Co2 CFSG.KS.Raw CFSG.Sporadic.Th CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

@[expose] noncomputable def regsOf (RT : Nat → Nat) (r : ℕ) : Gp :=
  permOfArr 6156 (unpack 6156 13 (RT r))

@[expose] def loopCond : TLoop → Cond
  | .allE _ c => c
  | .countEq _ c _ => c
  | .countLe _ c _ => c
  | .exE _ c => c

theorem tcheckK_sound {RT MT ET PS PSI : Nat → Nat}
    {chunks : List (Nat × Nat × Nat × List (Nat × Nat × Nat))} {PR PM NM : Nat}
    {W : List (List Nat)} {D : TData} {initG : ℕ → Gp}
    (hfix : D.fixedBelow ≤ 19)
    (hI : ∀ r < 19, CFSG.Sporadic.Th.Rep 6156 (CFSG.KS.MulH.tabT (unpack 6156 13 (RT r)))
      (initG r))
    (hIR : ∀ r < 19, initG r ∈ j3R)
    (hS : ∀ h < 5, Rep 6156 (unpack 6156 13 (PS h)) (j3StrongPerm h) ∧
      Rep 6156 (unpack 6156 13 (PSI h)) (j3StrongPerm h)⁻¹)
    (hB : ∀ g ∈ j3R, g 0 = 0 → g 1 = 1 → g 3 = 3 → g 2 = 2 → g = 1)
    (hlen : chunks.length ≤ 152)
    (hslp : ∀ j < 19, chunksK RT MT PR PM NM ((chunks.drop (Nat.mul 8 j)).take 8) (Nat.mul 8 j) =
      true)
    (hcov : coverK PR (ends chunks) = true) (hcovM : coverM PM NM (ends chunks) = true)
    (henum : ∀ e < D.enums.length, enumHeadK RT ET D e = true ∧
      ∀ j < cardOf D e / 512 + 1, enumPartK RT ET D e (Nat.mul 512 j) 512 = true)
    (hfacts : factsK RT ET PS PSI D D.facts W = true)
    (hloops : ∀ l ∈ D.loops, loopK RT ET D l = true)
    (hSP : ∀ h < 5, j3StrongPerm h ∈ j3P)
    (hwf : ∀ l ∈ D.loops, (loopCond l).wfB 109 D.enums.length = true) :
    TSem initG (regsOf RT) D := by
  set Rg := regsOf RT with hRgdef
  have hI' : ∀ r < 19, Gd (RT r) := fun r hr => ⟨initG r, hIR r hr, tb_of_thRep (hI r hr)⟩
  have hgd := slp_good hI' hlen hslp hcov hcovM
  have hRg : ∀ x < 109, Tb (RT x) (Rg x) ∧ Rg x ∈ j3R := by
    intro x hx
    obtain ⟨g, hg, hT⟩ := hgd x hx
    have e : Rg x = g := perm_eq hT
    rw [e]
    exact ⟨hT, hg⟩
  have hgl : ∀ e < D.enums.length, gensOf D e = (D.enums[e]!).1 ∧
      cardOf D e = (D.enums[e]!).2 := by
    intro e he
    unfold gensOf cardOf
    rw [List.getD_eq_getElem _ _ he, getElem!_pos D.enums e he]
    exact ⟨rfl, rfl⟩
  have hE := fun e (he : e < D.enums.length) =>
    (enum_glue hB hRg (henum e he).1 (henum e he).2).2
  have hmemE : ∀ e < D.enums.length, ∀ z ∈ j3R,
      memE ET D e (keyG z) = true ↔ z ∈ Ksub Rg (D.enums[e]!).1 := by
    intro e he z hz
    obtain ⟨x, c1, c2, -, c4, -, -⟩ := hE e he
    have hb : Nat.blt e (len (D.enums.map fun p => p.2)) = true := by
      rw [len_eq, List.length_map]
      exact Nat.ble_eq_true_of_le he
    unfold memE
    rw [hb, ← (hgl e he).1]
    change memK _ _ _ _ = true ↔ _
    rw [c4]
    constructor
    · rintro ⟨i, hi, hk⟩
      rw [(c1 i hi).1] at hk
      rw [← eq_of_key hB (c1 i hi).2.1 hz hk]
      exact (c1 i hi).2.2
    · intro hzK
      obtain ⟨i, hi, rfl⟩ := c2 z hzK
      exact ⟨i, hi, (c1 i hi).1⟩
  have hcardK : ∀ e < D.enums.length,
      Set.ncard (Ksub Rg (D.enums[e]!).1 : Set Gp) = cardOf D e := by
    intro e he
    obtain ⟨x, c1, c2, c3, -, -, -⟩ := hE e he
    rw [← (hgl e he).1]
    have h := ncard_eq (S := (Ksub Rg (gensOf D e) : Set Gp)) (fun i hi => (c1 i hi).2.2) c2 c3
      (fun _ => True) (fun _ => true) (fun i hi => by simp)
    simpa using h
  have hloopKey : ∀ e c, e < D.enums.length → c.wfB 109 D.enums.length = true →
      Set.ncard {y | y ∈ Ksub Rg (D.enums[e]!).1 ∧
        c.sem Rg (fun e => Ksub Rg (D.enums[e]!).1) y} = cntK RT ET D e c 0 (cardOf D e) := by
    intro e c he hw
    obtain ⟨x, c1, c2, c3, -, c5, c6⟩ := hE e he
    rw [← (hgl e he).1, cntK_eq]
    exact ncard_eq (fun i hi => (c1 i hi).2.2) c2 c3 _ _ (fun i hi =>
      cond_iff hB hRg hmemE (c1 i hi).2.1 (c1 i hi).1 (c5 i hi) (c6 i hi) c hw)
  have hlen' : ∀ e, Nat.blt e (len (D.enums.map fun p => p.2)) = true → e < D.enums.length := by
    intro e h
    have := nLt h
    rwa [len_eq, List.length_map] at this
  have hPR : j3P ≤ j3R := le_sup_left
  refine ⟨fun r hr => perm_eq (tb_of_thRep (hI r (lt_of_lt_of_le hr hfix))), fun e he => ?_,
    fun f hf => ?_, fun l hl => ?_⟩
  ·
    have h := hcardK e he
    rw [getElem!_pos D.enums e he] at h
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, h, (hgl e he).2, getElem!_pos D.enums e he]
  ·
    obtain ⟨wd, h⟩ := facts_get _ _ hfacts f hf
    cases f with
    | eqP l₁ l₂ =>
      dsimp only [factK] at h
      obtain ⟨h1, h⟩ := bA h
      obtain ⟨h2, h3⟩ := bA h
      obtain ⟨P1, M1⟩ := prodAt_eq hRg l₁ h1
      obtain ⟨P2, M2⟩ := prodAt_eq hRg l₂ h2
      have e3 := Nat.eq_of_beq_eq_true h3
      rw [keyF_eq P1, keyF_eq P2] at e3
      exact eq_of_key hB M1 M2 e3
    | neP l₁ l₂ =>
      dsimp only [factK] at h
      obtain ⟨h1, h⟩ := bA h
      obtain ⟨h2, h3⟩ := bA h
      obtain ⟨P1, M1⟩ := prodAt_eq hRg l₁ h1
      obtain ⟨P2, M2⟩ := prodAt_eq hRg l₂ h2
      intro heq
      have hb : Nat.beq (keyF (prodAt RT l₁)) (keyF (prodAt RT l₂)) = true := by
        rw [keyF_eq P1, keyF_eq P2, heq]
        exact Nat.beq_refl _
      rw [hb] at h3
      exact fne h3
    | memE e l =>
      dsimp only [factK] at h
      obtain ⟨h1, h2⟩ := bA h
      obtain ⟨P1, M1⟩ := prodAt_eq hRg l h1
      have he : e < D.enums.length := by
        unfold memE at h2
        exact hlen' e (bA h2).1
      rw [keyF_eq P1] at h2
      exact (hmemE e he _ M1).1 h2
    | inP l =>
      dsimp only [factK] at h
      obtain ⟨h1, h⟩ := bA h
      obtain ⟨h2, h3⟩ := bA h
      obtain ⟨P1, M1⟩ := prodAt_eq hRg l h1
      obtain ⟨w, hw, hwp⟩ := wordAt_eq (fun h hh => ⟨tb_of_rep (hS h hh).1, tb_of_rep (hS h hh).2⟩)
        hSP wd h2
      have e3 := Nat.eq_of_beq_eq_true h3
      rw [keyF_eq P1, keyF_eq hwp] at e3
      change prodG Rg l ∈ j3P
      rw [eq_of_key hB M1 (hPR hw) e3]
      exact hw
    | notInP l =>
      exact fne h
    | ordEq i m =>
      dsimp only [factK] at h
      obtain ⟨h1, h⟩ := bA h
      obtain ⟨h2, h⟩ := bA h
      obtain ⟨h3, h4⟩ := bA h
      have hr := hRg i (nLt h1)
      have e3 := Nat.eq_of_beq_eq_true h3
      rw [keyF_eq (powAt_eq hr.1 m), key1_eq] at e3
      have hpow : Rg i ^ m = 1 := eq_of_key hB (pow_mem hr.2 m) (one_mem _) e3
      have hne : Rg i ≠ 1 := by
        intro h1'
        have hb : Nat.beq (keyF (RT i |> ap)) key1 = true := by
          rw [keyF_eq hr.1, h1', key1_eq]
          exact Nat.beq_refl _
        rw [hb] at h4
        exact fne h4
      have : Fact m.Prime := ⟨prime_of h2⟩
      exact orderOf_eq_prime hpow hne
  ·
    have hk := hloops l hl
    have hw := hwf l hl
    cases l with
    | allE e c =>
      dsimp only [loopK] at hk
      obtain ⟨h1, h2⟩ := bA hk
      have he := hlen' e h1
      have hc := hloopKey e c he hw
      rw [Nat.eq_of_beq_eq_true h2, ← hcardK e he] at hc
      have hsub : {y | y ∈ Ksub Rg (D.enums[e]!).1 ∧
          c.sem Rg (fun e => Ksub Rg (D.enums[e]!).1) y} = (Ksub Rg (D.enums[e]!).1 : Set Gp) :=
        Set.eq_of_subset_of_ncard_le (fun y hy => hy.1) hc.ge (Set.toFinite _)
      intro y hy
      have : y ∈ {y | y ∈ Ksub Rg (D.enums[e]!).1 ∧
          c.sem Rg (fun e => Ksub Rg (D.enums[e]!).1) y} := by
        rw [hsub]
        exact hy
      exact this.2
    | countEq e c b =>
      dsimp only [loopK] at hk
      obtain ⟨h1, h2⟩ := bA hk
      have he := hlen' e h1
      have hc := hloopKey e c he hw
      rw [Nat.eq_of_beq_eq_true h2] at hc
      exact hc
    | countLe e c b =>
      dsimp only [loopK] at hk
      obtain ⟨h1, h2⟩ := bA hk
      have he := hlen' e h1
      have hc := hloopKey e c he hw
      change Set.ncard _ ≤ b
      rw [hc]
      exact Nat.le_of_ble_eq_true h2
    | exE e c =>
      dsimp only [loopK] at hk
      obtain ⟨h1, h2⟩ := bA hk
      have he := hlen' e h1
      have hc := hloopKey e c he hw
      have hpos : 0 < Set.ncard {y | y ∈ Ksub Rg (D.enums[e]!).1 ∧
          c.sem Rg (fun e => Ksub Rg (D.enums[e]!).1) y} := by
        rw [hc]
        exact nLt h2
      obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
      exact ⟨y, hy.1, hy.2⟩

end CFSG.KC.J3Tk
