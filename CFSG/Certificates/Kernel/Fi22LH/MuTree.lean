module

public import CFSG.Certificates.Kernel.Fi22LH.Defs
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.Certificates.Kernel.Fi22LH.EdgeWit
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.Pop
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.RowPhi
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KC.Enum CFSG.KS

variable {D : LHData}

private theorem nland_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

private theorem muW_root (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hb : (bs D.lb0).testBit f = true) : fd (D.P f) 14 4095 = 3510 := by
  have hs := h.mu (f / 880) (by omega)
  unfold muSlW muSl at hs
  rw [strictB_eq, strictB_eq, strictB_eq] at hs
  have := allN_iff.1 hs (f % 880) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 880) (f / 880)) (f % 880) = f := by
    change 880 * (f / 880) + f % 880 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at this
  unfold muK at this
  rw [strictB_eq, strictB_eq, bIf_eq, memB_eq, if_pos hb] at this
  exact Nat.eq_of_beq_eq_true this

private noncomputable def mPos (mq f : Nat) : Nat := fld(mq, Nat.mul (nat_lit 10) f, nat_lit 1023)

private theorem fd_zero_of_shift {x : Nat} (hx : Nat.shiftRight x 12 = 0) :
    fd x 12 1023 = 0 ∧ fd x 22 4095 = 0 := by
  have h1 : x / 2 ^ 12 = 0 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact hx
  have h2 : x / 2 ^ 22 = 0 := by
    rw [show (22 : Nat) = 12 + 10 from rfl, pow_add, ← Nat.div_div_eq_div_mul, h1, Nat.zero_div]
  refine ⟨?_, ?_⟩
  · rw [show (1023 : Nat) = 2 ^ 10 - 1 from rfl, fd_eq, h1, Nat.zero_mod]
  · rw [show (4095 : Nat) = 2 ^ 12 - 1 from rfl, fd_eq, h2, Nat.zero_mod]

private theorem posK_spec {pts pos : Nat → Nat} {none n N : Nat}
    (h : posK pts pos none n N = true) :
    (∀ k < N, pos (pts k) = k) ∧ ∀ x < n, pos x = none ∨ (pos x < N ∧ pts (pos x) = x) := by
  unfold posK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun k hk => Nat.eq_of_beq_eq_true (allN_iff.1 h.1 k hk), fun x hx => ?_⟩
  have := allN_iff.1 h.2 x hx
  rw [strictB_eq, bIf_eq] at this
  by_cases e : pos x = none
  · exact Or.inl e
  · right
    rw [beq_false e, if_neg (by decide), bAnd_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at this
    exact this

private theorem muTree_spec (h : LHChecks D) :
    fd (D.M 0) 12 1023 = 0 ∧ fd (D.M 0) 22 4095 = 0 ∧ fd (D.M 0) 0 4095 < 3510 ∧
      fd (D.P (fd (D.M 0) 0 4095)) 14 4095 < 3510 ∧
      (∀ f < fd (D.M 0) 0 4095, ¬ fd (D.P f) 14 4095 < 3510) ∧
      (∀ k < fd D.mt 70 1023, fd (D.P (fd (D.M k) 0 4095)) 14 4095 < 3510 ∧
        D.G k = sb (rowSet D.P D.QA (fd (D.M k) 0 4095))) ∧
      (∀ k < fd D.mt 70 1023, mPos D.mq (fd (D.M k) 0 4095) = k) ∧
      (∀ x < 3510, mPos D.mq x = 1023 ∨
        (mPos D.mq x < fd D.mt 70 1023 ∧ fd (D.M (mPos D.mq x)) 0 4095 = x)) ∧
      (∀ f < 3510, fd (D.P f) 14 4095 < 3510 → mPos D.mq f < fd D.mt 70 1023) ∧
      (List.range (fd D.mt 70 1023)).foldl (fun n hh => if hh < n then
        (List.range 3510).foldl (fun m f => muHit D.R D.Z D.M D.G masks D.mq
          (rowSet D.P D.QA (fd (D.M hh) 0 4095)) (D.G hh) hh f m) n else 0) 1 =
        fd D.mt 70 1023 := by
  have hT := h.muTree
  unfold muTreeW muTreeK at hT
  rw [strictB_eq, strictB_eq] at hT
  simp only [bAnd_eq, Bool.and_eq_true] at hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hT
  rw [Nat.beq_eq] at h1
  rw [Nat.blt_eq] at h2 h3
  obtain ⟨z1, z2⟩ := fd_zero_of_shift h1
  refine ⟨z1, z2, h2, h3, fun f hf => ?_, fun k hk => ?_, ?_, ?_, fun f hf hw => ?_, ?_⟩
  · have := allN_iff.1 h4 f hf
    rw [notB_eq, Bool.not_eq_true'] at this
    intro hlt
    rw [blt_true hlt] at this
    exact absurd this (by decide)
  · have := allN_iff.1 h5 k hk
    rw [strictB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · exact (posK_spec (pos := mPos D.mq) (pts := fun k => fd (D.M k) 0 4095) h6).1
  · exact (posK_spec (pos := mPos D.mq) (pts := fun k => fd (D.M k) 0 4095) h6).2
  · have := allN_iff.1 h7 f hf
    rw [bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hw), Nat.blt_eq] at this
    exact this
  · rw [Nat.beq_eq] at h8
    simp only [foldUp_eq, nIf_eq, Nat.blt_eq, strictN_eq] at h8
    exact h8

private theorem ml_spec (h : LHChecks D) :
    fd D.mt 70 1023 = 648 ∧ (∀ i < 647, ent D.ml i < ent D.ml (i + 1)) ∧ ent D.ml 647 < 3510 ∧
      ∀ i < 648, mPos D.mq (ent D.ml i) < fd D.mt 70 1023 := by
  have hm := h.ml
  unfold mlK at hm
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at hm
  obtain ⟨h1, h2, h3, h4⟩ := hm
  refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · have := allN_iff.1 h2 i hi
    rw [Nat.blt_eq] at this
    exact this
  · rw [Nat.blt_eq] at h3
    exact h3
  · have := allN_iff.1 h4 i hi
    rw [Nat.blt_eq] at this
    exact this

private theorem muHit_eq (R Z M G : Nat → Nat) (mk mq q a h f n : Nat) :
    muHit R Z M G mk mq q a h f n =
      if n = 0 then 0 else
      if mPos mq f = 1023 then n else
      if mPos mq f < n then n else
      if popK mk (Nat.land a (G (mPos mq f))) = 63 then
        (if mPos mq f = n then
          (if fd (M n) 0 4095 = f ∧ fd (M n) 12 1023 = h ∧
              edgeK R Z q a (G (mPos mq f)) (fd (M n) 22 4095) = true then n + 1 else 0)
        else 0)
      else n := by
  unfold muHit mPos
  simp only [nIf_eq, strictN_eq, Nat.beq_eq, Nat.blt_eq, bAnd_eq, Bool.and_eq_true]

private theorem muHit_zero (R Z M G : Nat → Nat) (mk mq q a h f : Nat) :
    muHit R Z M G mk mq q a h f 0 = 0 := by
  rw [muHit_eq, if_pos rfl]

private theorem muHit_spec {R Z M G : Nat → Nat} {mk mq q a h f n : Nat}
    (hne : muHit R Z M G mk mq q a h f n ≠ 0) :
    (mPos mq f = 1023 ∧ muHit R Z M G mk mq q a h f n = n) ∨
      (mPos mq f < n ∧ muHit R Z M G mk mq q a h f n = n) ∨
      (n ≤ mPos mq f ∧ popK mk (Nat.land a (G (mPos mq f))) ≠ 63 ∧
        muHit R Z M G mk mq q a h f n = n) ∨
      (mPos mq f = n ∧ popK mk (Nat.land a (G n)) = 63 ∧ fd (M n) 0 4095 = f ∧
        fd (M n) 12 1023 = h ∧ edgeK R Z q a (G n) (fd (M n) 22 4095) = true ∧
        muHit R Z M G mk mq q a h f n = n + 1) := by
  rw [muHit_eq] at hne ⊢
  split_ifs at hne ⊢ with h1 h2 h3 h4 h5 h6
  · exact absurd rfl hne
  · exact Or.inl ⟨h2, rfl⟩
  · exact Or.inr (Or.inl ⟨h3, rfl⟩)
  · subst h5
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h4, h6.1, h6.2.1, h6.2.2, rfl⟩))
  · exact absurd rfl hne
  · exact absurd rfl hne
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h4, rfl⟩))

private theorem pts_lt (h : LHChecks D) : ∀ k < fd D.mt 70 1023, fd (D.M k) 0 4095 < 3510 := by
  obtain ⟨-, -, -, -, -, -, -, hP5, -, -⟩ := muTree_spec h
  obtain ⟨hnm, hinc, hlast, hpos⟩ := ml_spec h
  have hle : ∀ i j, i ≤ j → j < 648 → ent D.ml i ≤ ent D.ml j := by
    intro i j hij hj
    induction j with
    | zero =>
      rw [show i = 0 by omega]
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h1 | h1
      · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (hinc j (by omega)))
      · rw [show i = j + 1 by omega]
  have hlt : ∀ i < 648, ent D.ml i < 3510 := fun i hi =>
    Nat.lt_of_le_of_lt (hle i 647 (by omega) (by decide)) hlast
  have hinj : ∀ i < 648, ∀ j < 648, ent D.ml i = ent D.ml j → i = j := by
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := Nat.lt_of_lt_of_le (hinc i (by omega)) (hle (i + 1) j (by omega) hj)
      omega
    · have := Nat.lt_of_lt_of_le (hinc j (by omega)) (hle (j + 1) i (by omega) hi)
      omega
  have hpt : ∀ i < 648, fd (D.M (mPos D.mq (ent D.ml i))) 0 4095 = ent D.ml i := by
    intro i hi
    rcases hP5 _ (hlt i hi) with e | ⟨-, e⟩
    · have := hpos i hi
      rw [hnm] at this
      omega
    · exact e
  let g : Fin 648 → Fin 648 := fun i => ⟨mPos D.mq (ent D.ml i), by
    have := hpos i i.2
    rw [hnm] at this
    exact this⟩
  have hg : Function.Injective g := by
    intro a b e
    have e' : mPos D.mq (ent D.ml a) = mPos D.mq (ent D.ml b) := congrArg Fin.val e
    apply Fin.ext
    apply hinj a a.2 b b.2
    rw [← hpt a a.2, ← hpt b b.2, e']
  have hsurj := Finite.surjective_of_injective hg
  intro k hk
  rw [hnm] at hk
  obtain ⟨i, hi⟩ := hsurj ⟨k, hk⟩
  have hk' : mPos D.mq (ent D.ml i) = k := congrArg Fin.val hi
  rw [← hk', hpt i i.2]
  exact hlt i i.2

private theorem muW_get {f : Nat} (hf : f < 3510) : (muWD D)[f]! = fd (D.P f) 14 4095 := by
  unfold muWD
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem mem_muList (h : LHChecks D) (x : Nat) :
    x ∈ (List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510)) ↔
      ∃ k < fd D.mt 70 1023, fd (D.M k) 0 4095 = x := by
  obtain ⟨-, -, -, -, -, hP3, hP4, hP5, hP6, -⟩ := muTree_spec h
  have hnm := (ml_spec h).1
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, hw⟩
    rw [muW_get hx] at hw
    have hp := hP6 x hx hw
    rcases hP5 x hx with e | ⟨-, e⟩
    · rw [hnm] at hp
      omega
    · exact ⟨_, hp, e⟩
  · rintro ⟨k, hk, rfl⟩
    have hx := pts_lt h k hk
    refine ⟨hx, ?_⟩
    rw [muW_get hx]
    exact (hP3 k hk).1

private theorem muList_length (h : LHChecks D) :
    ((List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510))).length =
      fd D.mt 70 1023 := by
  classical
  obtain ⟨-, -, -, -, -, -, hP4, -, -, -⟩ := muTree_spec h
  have hnd : ((List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510))).Nodup :=
    List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have e : ((List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510))).toFinset =
      (Finset.range (fd D.mt 70 1023)).image fun k => fd (D.M k) 0 4095 := by
    ext x
    rw [List.mem_toFinset, mem_muList h, Finset.mem_image]
    simp only [Finset.mem_range]
  rw [e, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj e'
  have h1 := hP4 i (by simpa using hi)
  have h2 := hP4 j (by simpa using hj)
  rw [← h1, ← h2]
  exact congrArg (mPos D.mq) e'

private theorem andPop_bitsOfNat {a b : Nat} (ha : a < 2 ^ 3510) :
    andPop (bitsOfNat a) (bitsOfNat b) = popK masks (Nat.land a b) := by
  have hab : Nat.land a b < 2 ^ 3510 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  have hpop : Nat.land a b < 2 ^ 3584 :=
    lt_of_lt_of_le hab (Nat.pow_le_pow_right (by decide) (by decide))
  rw [andPop_eq (bitsIs_bitsOfNat a).1 (bitsIs_bitsOfNat b).1, popK_eq hpop]
  have hbit : (List.range 3520).countP
      (fun y => bitAt (bitsOfNat a) y && bitAt (bitsOfNat b) y) =
      (List.range 3520).countP fun y => (Nat.land a b).testBit y := by
    refine List.countP_congr fun y hy => ?_
    have hy' := List.mem_range.1 hy
    rw [Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat a).2 y hy'),
      Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat b).2 y hy'), nland_eq, Nat.testBit_and]
  rw [hbit]
  have hzero : ∀ i < 64, (Nat.land a b).testBit (3520 + i) = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hab (Nat.pow_le_pow_right (by decide) (by omega)))
  have htail : ((List.range 64).map (3520 + ·)).countP
      (fun y => (Nat.land a b).testBit y) = 0 := by
    rw [List.countP_map]
    exact List.countP_eq_zero.2 fun i hi => Bool.eq_false_iff.mp (hzero i (List.mem_range.1 hi))
  rw [show 3584 = 3520 + 64 by decide, List.range_add, List.countP_append, htail, Nat.add_zero]

private theorem rowR_lt (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hw : fd (D.P f) 14 4095 < 3510) : fd (D.P f) 0 16383 < 14080 := by
  have hb : (bs D.lb0).testBit f = false := by
    rw [Bool.eq_false_iff]
    intro hb
    have := muW_root h hf hb
    omega
  exact ((rowF_spec h hf).2 hb).1

private theorem muHit_le {R Z M G : Nat → Nat} {mk mq q a h f n : Nat}
    (hne : muHit R Z M G mk mq q a h f n ≠ 0) : n ≤ muHit R Z M G mk mq q a h f n := by
  rcases muHit_spec hne with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, _, _, he⟩ <;> omega

private def mStep (T : Array Table) (CB : Array Bits) (O0 : LHOrb) (rowR : Array Nat) (h : Nat)
    (A : Bits) (f : Nat) (s : Array Nat × Array Nat × Array Nat × Bits) :
    Array Nat × Array Nat × Array Nat × Bits :=
  if (!bitAt s.2.2.2 f) = true then
    if (andPop A O0.sets[rowR[f]!]! == 63) = true then
      if edgeWit T CB A O0.sets[rowR[f]!]! < 3510 then
        (s.1.push f, s.2.1.push h, s.2.2.1.push (edgeWit T CB A O0.sets[rowR[f]!]!),
          setBit s.2.2.2 f)
      else s
    else s
  else s

private def NInv (D : LHData) (m : Nat) (s : Array Nat × Array Nat × Array Nat × Bits) : Prop :=
  s.1.size = m ∧ (∀ k < m, s.1[k]! = fd (D.M k) 0 4095) ∧ s.2.1.size = m ∧
    (∀ k < m, s.2.1[k]! = fd (D.M k) 12 1023) ∧ s.2.2.1.size = m ∧
    (∀ k < m, s.2.2.1[k]! = fd (D.M k) 22 4095) ∧
    BitsIs s.2.2.2 fun y => ∃ k < m, fd (D.M k) 0 4095 = y

private theorem ninv_eta {m : Nat} {a : Array Nat × Array Nat × Array Nat × Bits}
    (h : NInv D m a) : NInv D m (a.1, a.2.1, a.2.2.1, a.2.2.2) := h

private theorem mStep_inv (hO : OrbOK) (h : LHChecks D) {hh f m : Nat}
    (hhn : hh < fd D.mt 70 1023) (hf : f < 3510) (hw : fd (D.P f) 14 4095 < 3510)
    {s : Array Nat × Array Nat × Array Nat × Bits} (hs : NInv D m s)
    (hne : muHit D.R D.Z D.M D.G masks D.mq (rowSet D.P D.QA (fd (D.M hh) 0 4095)) (D.G hh) hh
      f m ≠ 0)
    (hle : muHit D.R D.Z D.M D.G masks D.mq (rowSet D.P D.QA (fd (D.M hh) 0 4095)) (D.G hh) hh
      f m ≤ fd D.mt 70 1023) :
    NInv D (muHit D.R D.Z D.M D.G masks D.mq (rowSet D.P D.QA (fd (D.M hh) 0 4095)) (D.G hh) hh
      f m) (mStep (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D) hh
        (bitsOfNat (sb (D.QA (fd (D.P (fd (D.M hh) 0 4095)) 0 16383)))) f s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hs
  obtain ⟨-, -, -, -, -, hP3, hP4, hP5, hP6, -⟩ := muTree_spec h
  have hnm := (ml_spec h).1
  have hph := pts_lt h hh hhn
  have hrh := rowR_lt h hph (hP3 hh hhn).1
  have hrf := rowR_lt h hf hw
  have hpn : mPos D.mq f < fd D.mt 70 1023 := hP6 f hf hw
  have hpf : fd (D.M (mPos D.mq f)) 0 4095 = f := by
    rcases hP5 f hf with e | ⟨-, e⟩
    · omega
    · exact e
  have hGh : D.G hh = sb (D.QA (fd (D.P (fd (D.M hh) 0 4095)) 0 16383)) := (hP3 hh hhn).2
  have hGp : D.G (mPos D.mq f) = sb (D.QA (fd (D.P f) 0 16383)) := by
    rw [(hP3 _ hpn).2, hpf]
    rfl
  have hC : (orbDec D.QA).sets[(rowRD D)[f]!]! = bitsOfNat (sb (D.QA (fd (D.P f) 0 16383))) := by
    rw [rowR_get hf, orbDec_sets _ hrf]
  have hand : andPop (bitsOfNat (sb (D.QA (fd (D.P (fd (D.M hh) 0 4095)) 0 16383))))
      (bitsOfNat (sb (D.QA (fd (D.P f) 0 16383)))) =
      popK masks (Nat.land (D.G hh) (D.G (mPos D.mq f))) := by
    rw [hGh, hGp]
    exact andPop_bitsOfNat (sb_lt _)
  have hm : m ≤ fd D.mt 70 1023 := le_trans (muHit_le hne) hle
  have hseen : bitAt s.2.2.2 f = true ↔ mPos D.mq f < m := by
    refine (h7.2 f (by omega)).trans ⟨?_, fun hp => ⟨_, hp, hpf⟩⟩
    rintro ⟨k, hk, e⟩
    rw [← e, hP4 k (by omega)]
    exact hk
  rcases muHit_spec hne with ⟨hc, -⟩ | ⟨hc, he⟩ | ⟨hc, hpop, he⟩ |
      ⟨hc, hpop, ho, hpa, hed, he⟩
  · omega
  · rw [he]
    unfold mStep
    rw [if_neg (by rw [hseen.2 hc]; decide)]
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rw [he]
    have hs' : bitAt s.2.2.2 f = false :=
      Bool.eq_false_iff.2 fun e => by have := hseen.1 e; omega
    unfold mStep
    rw [if_pos (by rw [hs']; decide), hC, hand, if_neg (by simpa using hpop)]
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rw [he]
    have hs' : bitAt s.2.2.2 f = false :=
      Bool.eq_false_iff.2 fun e => by have := hseen.1 e; omega
    rw [hc] at hGp hand
    rw [hGh, hGp] at hed
    obtain ⟨hwl, -, hwe⟩ := edgeWit_eq_of_edgeK hO h hrh hrf hed
    unfold mStep
    rw [if_pos (by rw [hs']; decide), hC, hand, if_pos (by rw [hpop]; decide), hwe, if_pos hwl]
    refine ⟨by rw [Array.size_push, h1], fun k hk => ?_, by rw [Array.size_push, h3],
      fun k hk => ?_, by rw [Array.size_push, h5], fun k hk => ?_,
      (bitsIs_setBit h7 (by omega)).congr fun y _ => ?_⟩
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h1]; exact hk'), h2 k hk']
      · have : k = s.1.size := by omega
        rw [this, get!_push_eq, h1, ho]
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h3]; exact hk'), h4 k hk']
      · have : k = s.2.1.size := by omega
        rw [this, get!_push_eq, h3, hpa]
    · dsimp only
      rcases Nat.lt_or_ge k m with hk' | hk'
      · rw [get!_push_lt _ _ (by rw [h5]; exact hk'), h6 k hk']
      · have : k = s.2.2.1.size := by omega
        rw [this, get!_push_eq, h5]
    · constructor
      · rintro (⟨k, hk, e⟩ | e)
        · exact ⟨k, by omega, e⟩
        · exact ⟨m, by omega, by rw [ho, e]⟩
      · rintro ⟨k, hk, e⟩
        rcases Nat.lt_or_ge k m with hk' | hk'
        · exact Or.inl ⟨k, hk', e⟩
        · right
          rw [← e, show k = m by omega, ho]

private theorem foldl_filter_of {F : Nat → Nat → Nat} {p : Nat → Bool} : ∀ (l : List Nat),
    (∀ a ∈ l, p a = false → ∀ b, F b a = b) → ∀ b, l.foldl F b = (l.filter p).foldl F b
  | [], _, b => rfl
  | a :: l, hF, b => by
    have hF' : ∀ x ∈ l, p x = false → ∀ b, F b x = b := fun x hx => hF x (List.mem_cons_of_mem _ hx)
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.foldl_cons, List.foldl_cons,
        foldl_filter_of l hF' (F b a)]
    · rw [List.filter_cons_of_neg ha, List.foldl_cons,
        hF a List.mem_cons_self (by simpa using ha) b, foldl_filter_of l hF' b]

private theorem filter_range_head {p : Nat → Bool} {n w : Nat} (hw : w < n) (hp : p w = true)
    (hlt : ∀ k < w, p k = false) : ∃ tail, (List.range n).filter p = w :: tail := by
  obtain ⟨r, rfl⟩ : ∃ r, n = w + 1 + r := ⟨n - w - 1, by omega⟩
  rw [List.range_add, List.range_succ, List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 fun k hk => by rw [hlt k (List.mem_range.1 hk)]; simp,
    List.filter_singleton, hp, cond_true]
  exact ⟨_, rfl⟩

theorem muTree_eq_of (hO : OrbOK) (h : LHChecks D) :
    mkMuTree (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D) (muWD D) =
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 0 4095,
        Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 12 1023,
        Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 22 4095) := by
  obtain ⟨z1, z2, hf0, hw0, hlt0, hP3, -, hP5, -, hfold⟩ := muTree_spec h
  have hnm := (ml_spec h).1
  let H : Nat → Nat → Nat → Nat := fun q f m =>
    muHit D.R D.Z D.M D.G masks D.mq (rowSet D.P D.QA (fd (D.M q) 0 4095)) (D.G q) q f m
  let Sf : Nat → Nat → Nat := fun q n =>
    if q < n then (List.range 3510).foldl (fun m f => H q f m) n else 0
  let C : Nat → Nat := fun q => (List.range q).foldl (fun n q => Sf q n) 1
  have hCN : C (fd D.mt 70 1023) = fd D.mt 70 1023 := by
    simp only [C, Sf, H]
    exact hfold
  have hC_succ : ∀ q, C (q + 1) = Sf q (C q) := fun q => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hH0 : ∀ q f, H q f 0 = 0 := fun q f => muHit_zero _ _ _ _ _ _ _ _ _ _
  have hHm : ∀ q f m, H q f m ≠ 0 → m ≤ H q f m := fun q f m hne => muHit_le hne
  have hS0 : ∀ q, Sf q 0 = 0 := fun q => by simp [Sf]
  have hSm : ∀ q m, Sf q m ≠ 0 → m ≤ Sf q m := fun q m hne => by
    simp only [Sf] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun f m => H q f m) (fun f => hH0 q f) (fun f m => hHm q f m) _ _
        hne).2
    · exact absurd rfl hne
  have hC : ∀ q ≤ fd D.mt 70 1023, C q ≠ 0 ∧ C q ≤ fd D.mt 70 1023 := by
    intro q hq
    have e : (List.range (fd D.mt 70 1023)).foldl (fun n q => Sf q n) 1 =
        ((List.range (fd D.mt 70 1023 - q)).map (q + ·)).foldl (fun n q => Sf q n) (C q) := by
      have eN : fd D.mt 70 1023 = q + (fd D.mt 70 1023 - q) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have h2 : ((List.range (fd D.mt 70 1023 - q)).map (q + ·)).foldl (fun n q => Sf q n) (C q) ≠
        0 := by
      rw [← e]
      change C (fd D.mt 70 1023) ≠ 0
      omega
    have := fold_nonzero Sf hS0 hSm _ _ h2
    rw [← e] at this
    change C q ≠ 0 ∧ C q ≤ C (fd D.mt 70 1023) at this
    rw [hCN] at this
    exact this
  have hCh : ∀ q < fd D.mt 70 1023, q < C q := by
    intro q hq
    have := (hC (q + 1) hq).1
    rw [hC_succ] at this
    simp only [Sf] at this
    split at this
    · assumption
    · exact absurd rfl this
  have hLmem : ∀ f ∈ (List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510)),
      f < 3510 ∧ fd (D.P f) 14 4095 < 3510 := by
    intro f hf
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq] at hf
    exact ⟨hf.1, by rw [← muW_get hf.1]; exact hf.2⟩
  have hskip : ∀ q, ∀ a ∈ List.range 3510, decide ((muWD D)[a]! < 3510) = false →
      ∀ b, H q a b = b := by
    intro q a ha hp b
    have ha' := List.mem_range.1 ha
    rw [decide_eq_false_iff_not, muW_get ha'] at hp
    have hpos : mPos D.mq a = 1023 := by
      rcases hP5 a ha' with e | ⟨hk, e⟩
      · exact e
      · exfalso
        apply hp
        rw [← e]
        exact (hP3 _ hk).1
    show muHit _ _ _ _ _ _ _ _ _ _ _ = b
    rw [muHit_eq]
    by_cases hb : b = 0
    · rw [if_pos hb, hb]
    · rw [if_neg hb, if_pos hpos]
  have hinner : ∀ q < fd D.mt 70 1023, ∀ (l : List Nat),
      (∀ f ∈ l, f < 3510 ∧ fd (D.P f) 14 4095 < 3510) →
      ∀ m s, NInv D m s → l.foldl (fun m f => H q f m) m ≠ 0 →
        l.foldl (fun m f => H q f m) m ≤ fd D.mt 70 1023 →
        NInv D (l.foldl (fun m f => H q f m) m)
          (l.foldl (fun s f => mStep (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D)
            q (bitsOfNat (sb (D.QA (fd (D.P (fd (D.M q) 0 4095)) 0 16383)))) f s) s) := by
    intro q hq l
    induction l with
    | nil => intro _ m s hs _ _; exact hs
    | cons f l ih =>
      intro hl m s hs hne hle
      rw [List.foldl_cons] at hne hle ⊢
      rw [List.foldl_cons]
      obtain ⟨hne1, hle1⟩ := fold_nonzero (fun f m => H q f m) (fun f => hH0 q f)
        (fun f m => hHm q f m) l _ hne
      have hf := hl f List.mem_cons_self
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ _
        (mStep_inv hO h hq hf.1 hf.2 hs hne1 (le_trans hle1 hle)) hne hle
  obtain ⟨tail, hL⟩ := filter_range_head (p := fun f => decide ((muWD D)[f]! < 3510)) hf0
    (by
      show decide ((muWD D)[fd (D.M 0) 0 4095]! < 3510) = true
      rw [decide_eq_true_eq, muW_get hf0]
      exact hw0)
    (fun k hk => by
      show decide ((muWD D)[k]! < 3510) = false
      rw [decide_eq_false_iff_not, muW_get (by omega)]
      exact hlt0 k hk)
  obtain ⟨s, hs, hI⟩ : ∃ s : Array Nat × Array Nat × Array Nat × Bits,
      mkMuTree (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D) (muWD D) =
        (s.1, s.2.1, s.2.2.1) ∧ NInv D (fd D.mt 70 1023) s := by
    unfold mkMuTree
    rw [hL]
    refine ⟨_, rfl, ?_⟩
    rw [← hL, muList_length h]
    refine range_loop (fun q s => q ≤ fd D.mt 70 1023 ∧ NInv D (C q) s)
      (NInv D (fd D.mt 70 1023)) _ (fd D.mt 70 1023) _ ?_ ?_ ?_
    · intro q s hq hIq
      obtain ⟨-, hIq⟩ := hIq
      have hqs : q < s.1.size := by rw [hIq.1]; exact hCh q hq
      have hx : s.1[q]! = fd (D.M q) 0 4095 := hIq.2.1 q (hCh q hq)
      have hpq := pts_lt h q hq
      have hA : (orbDec D.QA).sets[(rowRD D)[fd (D.M q) 0 4095]!]! =
          bitsOfNat (sb (D.QA (fd (D.P (fd (D.M q) 0 4095)) 0 16383))) := by
        rw [rowR_get hpq, orbDec_sets _ (rowR_lt h hpq (hP3 q hq).1)]
      simp only [hqs, ↓reduceIte, hx]
      rw [hA, forIn_yield _ (fun f s => mStep (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA)
        (rowRD D) q (bitsOfNat (sb (D.QA (fd (D.P (fd (D.M q) 0 4095)) 0 16383)))) f s)
        (fun a b => by dsimp only [mStep]; split_ifs <;> rfl)]
      have hfin : C (q + 1) = ((List.range 3510).filter
          (fun f => decide ((muWD D)[f]! < 3510))).foldl (fun m f => H q f m) (C q) := by
        rw [hC_succ]
        simp only [Sf, if_pos (hCh q hq)]
        exact foldl_filter_of _ (hskip q) _
      have hne : ((List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510))).foldl
          (fun m f => H q f m) (C q) ≠ 0 := by
        rw [← hfin]
        exact (hC (q + 1) hq).1
      have hle : ((List.range 3510).filter (fun f => decide ((muWD D)[f]! < 3510))).foldl
          (fun m f => H q f m) (C q) ≤ fd D.mt 70 1023 := by
        rw [← hfin]
        exact (hC (q + 1) hq).2
      have := hinner q hq _ hLmem (C q) (s.1, s.2.1, s.2.2.1, s.2.2.2) hIq hne hle
      rw [← hfin] at this
      exact ⟨by omega, ninv_eta this⟩
    · intro s hs
      have := hs.2
      rw [hCN] at this
      exact this
    · refine ⟨Nat.zero_le _, ?_⟩
      change NInv D 1 _
      refine ⟨rfl, fun k hk => ?_, rfl, fun k hk => ?_, rfl, fun k hk => ?_,
        (bitsIs_setBit bitsIs_empty (by omega)).congr fun y _ => ?_⟩
      · have : k = 0 := by omega
        subst this
        rfl
      · have : k = 0 := by omega
        subst this
        rw [z1]
        rfl
      · have : k = 0 := by omega
        subst this
        rw [z2]
        rfl
      · constructor
        · rintro (h | h)
          · exact h.elim
          · exact ⟨0, by omega, h.symm⟩
        · rintro ⟨k, hk, e⟩
          right
          rw [← e, show k = 0 by omega]
  rw [hs]
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hI
  have hof : ∀ (a : Array Nat) (g : Nat → Nat), a.size = fd D.mt 70 1023 →
      (∀ k < fd D.mt 70 1023, a[k]! = g k) →
      a = Array.ofFn (n := fd D.mt 70 1023) fun k => g k.val := by
    intro a g hs hg
    apply Array.ext (by rw [hs, Array.size_ofFn])
    intro i hi1 hi2
    rw [Array.getElem_ofFn, ← getElem!_pos a i hi1, hg i (by omega)]
  rw [hof _ _ h1 h2, hof _ _ h3 h4, hof _ _ h5 h6]

private theorem muK_out (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hb : (bs D.lb0).testBit f = false) :
    (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383))) (sb (D.QA (fd D.mt 0 16383)))) = 63 →
      edgeK D.R D.Z (D.QA (fd (D.P f) 0 16383)) (sb (D.QA (fd (D.P f) 0 16383)))
        (sb (D.QA (fd D.mt 0 16383))) (fd (D.P f) 14 4095) = true) ∧
    (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383))) (sb (D.QA (fd D.mt 0 16383)))) ≠ 63 →
      fd (D.P f) 14 4095 = 3510) := by
  have hs := h.mu (f / 880) (by omega)
  unfold muSlW muSl at hs
  rw [strictB_eq, strictB_eq, strictB_eq] at hs
  have := allN_iff.1 hs (f % 880) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 880) (f / 880)) (f % 880) = f := by
    change 880 * (f / 880) + f % 880 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at this
  unfold muK at this
  rw [strictB_eq, strictB_eq, bIf_eq, memB_eq, hb, if_neg (by decide), strictB_eq, strictB_eq,
    bIf_eq] at this
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · rw [if_pos (by rw [Nat.beq_eq]; exact hp)] at this
    exact this
  · rw [if_neg (by rw [Nat.beq_eq]; exact hp)] at this
    exact Nat.eq_of_beq_eq_true this

private theorem edgeK_not_mem {R Z : Nat → Nat} {q bA bB w : Nat}
    (he : edgeK R Z q bA bB w = true) : bA.testBit w = false := by
  unfold edgeK at he
  rw [bAnd_eq, Bool.and_eq_true] at he
  have hmin := he.1
  unfold minWitK at hmin
  rw [strictB_eq] at hmin
  simp only [bAnd_eq, Bool.and_eq_true, memB_eq, notB_eq, Bool.not_eq_true'] at hmin
  exact hmin.2.2.1

private theorem commonCount_bitsOfNat {a b : Nat} (ha : a < 2 ^ 3510) :
    commonCount (bitsOfNat a) (bitsOfNat b) = popK masks (Nat.land a b) := by
  have hab : Nat.land a b < 2 ^ 3510 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  have hpop : Nat.land a b < 2 ^ 3584 :=
    lt_of_lt_of_le hab (Nat.pow_le_pow_right (by decide) (by decide))
  unfold commonCount
  rw [popK_eq hpop]
  have hbit : (List.range 3510).countP
      (fun y => bitAt (bitsOfNat a) y && bitAt (bitsOfNat b) y) =
      (List.range 3510).countP fun y => (Nat.land a b).testBit y := by
    refine List.countP_congr fun y hy => ?_
    have hy' : y < 3520 := by have := List.mem_range.1 hy; omega
    rw [Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat a).2 y hy'),
      Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat b).2 y hy'), nland_eq, Nat.testBit_and]
  rw [hbit]
  have hzero : ∀ i < 74, (Nat.land a b).testBit (3510 + i) = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hab (Nat.pow_le_pow_right (by decide) (by omega)))
  have htail : ((List.range 74).map (3510 + ·)).countP
      (fun y => (Nat.land a b).testBit y) = 0 := by
    rw [List.countP_map]
    exact List.countP_eq_zero.2 fun i hi => Bool.eq_false_iff.mp (hzero i (List.mem_range.1 hi))
  rw [show 3584 = 3510 + 74 by decide, List.range_add, List.countP_append, htail, Nat.add_zero]

private theorem muTree_facts (h : LHChecks D) : ∀ k, 0 < k → k < fd D.mt 70 1023 →
    fd (D.M k) 12 1023 < k ∧
      edgeK D.R D.Z (rowSet D.P D.QA (fd (D.M (fd (D.M k) 12 1023)) 0 4095))
        (D.G (fd (D.M k) 12 1023)) (D.G k) (fd (D.M k) 22 4095) = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hfold⟩ := muTree_spec h
  have hnm := (ml_spec h).1
  let H : Nat → Nat → Nat → Nat := fun q f m =>
    muHit D.R D.Z D.M D.G masks D.mq (rowSet D.P D.QA (fd (D.M q) 0 4095)) (D.G q) q f m
  let Sf : Nat → Nat → Nat := fun q n =>
    if q < n then (List.range 3510).foldl (fun m f => H q f m) n else 0
  let C : Nat → Nat := fun q => (List.range q).foldl (fun n q => Sf q n) 1
  have hCN : C (fd D.mt 70 1023) = fd D.mt 70 1023 := by
    simp only [C, Sf, H]
    exact hfold
  have hC_succ : ∀ q, C (q + 1) = Sf q (C q) := fun q => by
    simp only [C, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hH0 : ∀ q f, H q f 0 = 0 := fun q f => muHit_zero _ _ _ _ _ _ _ _ _ _
  have hHm : ∀ q f m, H q f m ≠ 0 → m ≤ H q f m := fun q f m hne => muHit_le hne
  have hS0 : ∀ q, Sf q 0 = 0 := fun q => by simp [Sf]
  have hSm : ∀ q m, Sf q m ≠ 0 → m ≤ Sf q m := fun q m hne => by
    simp only [Sf] at hne ⊢
    split at hne
    · rw [if_pos ‹_›]
      exact (fold_nonzero (fun f m => H q f m) (fun f => hH0 q f) (fun f m => hHm q f m) _ _
        hne).2
    · exact absurd rfl hne
  have hC : ∀ q ≤ fd D.mt 70 1023, C q ≠ 0 ∧ C q ≤ fd D.mt 70 1023 := by
    intro q hq
    have e : (List.range (fd D.mt 70 1023)).foldl (fun n q => Sf q n) 1 =
        ((List.range (fd D.mt 70 1023 - q)).map (q + ·)).foldl (fun n q => Sf q n) (C q) := by
      have eN : fd D.mt 70 1023 = q + (fd D.mt 70 1023 - q) := by omega
      conv_lhs => rw [eN]
      rw [List.range_add, List.foldl_append]
    have h2 : ((List.range (fd D.mt 70 1023 - q)).map (q + ·)).foldl (fun n q => Sf q n) (C q) ≠
        0 := by
      rw [← e]
      change C (fd D.mt 70 1023) ≠ 0
      omega
    have := fold_nonzero Sf hS0 hSm _ _ h2
    rw [← e] at this
    change C q ≠ 0 ∧ C q ≤ C (fd D.mt 70 1023) at this
    rw [hCN] at this
    exact this
  have hCh : ∀ q < fd D.mt 70 1023, q < C q := by
    intro q hq
    have := (hC (q + 1) hq).1
    rw [hC_succ] at this
    simp only [Sf] at this
    split at this
    · assumption
    · exact absurd rfl this
  let M : Nat → Nat → Nat := fun q j => (List.range j).foldl (fun m f => H q f m) (C q)
  have hM : ∀ q < fd D.mt 70 1023, ∀ j < 3510, H q j (M q j) ≠ 0 ∧ C q ≤ M q j := by
    intro q hq j hj
    have hfin : C (q + 1) = (List.range 3510).foldl (fun m f => H q f m) (C q) := by
      rw [hC_succ]
      simp only [Sf, if_pos (hCh q hq)]
    have e : (List.range 3510).foldl (fun m f => H q f m) (C q) =
        ((List.range (3510 - (j + 1))).map ((j + 1) + ·)).foldl (fun m f => H q f m)
          (H q j (M q j)) := by
      have enl : 3510 = j + 1 + (3510 - (j + 1)) := by omega
      conv_lhs => rw [enl]
      rw [List.range_add, List.foldl_append, List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    have hne : ((List.range (3510 - (j + 1))).map ((j + 1) + ·)).foldl (fun m f => H q f m)
        (H q j (M q j)) ≠ 0 := by
      rw [← e, ← hfin]
      exact (hC (q + 1) hq).1
    obtain ⟨hne1, -⟩ := fold_nonzero (fun f m => H q f m) (fun f => hH0 q f)
      (fun f m => hHm q f m) _ _ hne
    have hne2 : (List.range j).foldl (fun m f => H q f m) (C q) ≠ 0 := by
      intro e0
      have : H q j (M q j) = 0 := by
        change H q j ((List.range j).foldl (fun m f => H q f m) (C q)) = 0
        rw [e0]
        exact hH0 q j
      exact hne1 this
    exact ⟨hne1, (fold_nonzero (fun f m => H q f m) (fun f => hH0 q f) (fun f m => hHm q f m) _ _
      hne2).2⟩
  have hM_succ : ∀ q j, M q (j + 1) = H q j (M q j) := fun q j => by
    simp only [M, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hP : ∀ q ≤ fd D.mt 70 1023, ∀ k, 0 < k → k < C q → fd (D.M k) 12 1023 < k ∧
      edgeK D.R D.Z (rowSet D.P D.QA (fd (D.M (fd (D.M k) 12 1023)) 0 4095))
        (D.G (fd (D.M k) 12 1023)) (D.G k) (fd (D.M k) 22 4095) = true := by
    intro q
    induction q with
    | zero =>
      intro _ k hk0 hk
      have : C 0 = 1 := rfl
      omega
    | succ q ih =>
      intro hq k hk0 hk
      have hQ : ∀ j ≤ 3510, ∀ k, 0 < k → k < M q j → fd (D.M k) 12 1023 < k ∧
          edgeK D.R D.Z (rowSet D.P D.QA (fd (D.M (fd (D.M k) 12 1023)) 0 4095))
            (D.G (fd (D.M k) 12 1023)) (D.G k) (fd (D.M k) 22 4095) = true := by
        intro j
        induction j with
        | zero => intro _ k hk0 hk; exact ih (by omega) k hk0 hk
        | succ j ihj =>
          intro hj k hk0 hk
          rw [hM_succ] at hk
          obtain ⟨hne, hpre⟩ := hM q (by omega) j (by omega)
          rcases muHit_spec hne with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, _, he⟩ | ⟨_, _, _, hpa, hed, he⟩
          · rw [show H q j (M q j) = M q j from he] at hk
            exact ihj (by omega) k hk0 hk
          · rw [show H q j (M q j) = M q j from he] at hk
            exact ihj (by omega) k hk0 hk
          · rw [show H q j (M q j) = M q j from he] at hk
            exact ihj (by omega) k hk0 hk
          · rw [show H q j (M q j) = M q j + 1 from he] at hk
            rcases Nat.lt_or_ge k (M q j) with h1 | h1
            · exact ihj (by omega) k hk0 h1
            · have hk' : k = M q j := by omega
              subst hk'
              have := hCh q (by omega)
              refine ⟨by rw [hpa]; omega, ?_⟩
              rw [hpa]
              exact hed
      have hfin : C (q + 1) = M q 3510 := by
        rw [hC_succ]
        simp only [Sf, M, if_pos (hCh q (by omega))]
      rw [hfin] at hk
      exact hQ 3510 (Nat.le_refl _) k hk0 hk
  intro k hk0 hk
  exact hP _ (Nat.le_refl _) k hk0 (by rw [hCN]; exact hk)

theorem c_mu_of (hO : OrbOK) (h : LHChecks D) :
    muOK (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) (rowRD D) (muWD D)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 0 4095)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 12 1023)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 22 4095) (fd D.mt 0 16383) =
      true := by
  obtain ⟨-, -, -, -, -, hP3, -, hP5, hP6, -⟩ := muTree_spec h
  have hnm := (ml_spec h).1
  have hv0 : fd D.mt 0 16383 < 14080 := (farK_spec h).1
  have hV : (orbDec D.QA).sets[fd D.mt 0 16383]! = bitsOfNat (sb (D.QA (fd D.mt 0 16383))) :=
    orbDec_sets _ hv0
  have hget : ∀ (g : Nat → Nat) (k : Nat), k < fd D.mt 70 1023 →
      (Array.ofFn (n := fd D.mt 70 1023) fun i => g i.val)[k]! = g k := fun g k hk => by
    rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  have hbit : ∀ (a y : Nat), y < 3520 → bitAt (bitsOfNat a) y = a.testBit y :=
    fun a y hy => Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat a).2 y hy)
  have hout : ∀ k < fd D.mt 70 1023, (bs D.lb0).testBit (fd (D.M k) 0 4095) = false := by
    intro k hk
    rw [Bool.eq_false_iff]
    intro hb
    have h1 := muW_root h (pts_lt h k hk) hb
    have h2 := (hP3 k hk).1
    omega
  have hA : ∀ k < fd D.mt 70 1023, (orbDec D.QA).sets[(rowRD D)[fd (D.M k) 0 4095]!]! =
      bitsOfNat (sb (D.QA (fd (D.P (fd (D.M k) 0 4095)) 0 16383))) := fun k hk => by
    rw [rowR_get (pts_lt h k hk), orbDec_sets _ (rowR_lt h (pts_lt h k hk) (hP3 k hk).1)]
  unfold muOK
  dsimp only
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by simp [muWD], ?_⟩, by simp [hnm]⟩, by simp⟩, by simp⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    refine allIn_lo.2 fun f _ hf => ?_
    rw [B0_at h hf, muW_get hf]
    cases hb : (bs D.lb0).testBit f
    · rw [Bool.false_or]
      have hrf := ((rowF_spec h hf).2 hb).1
      have hAf : (orbDec D.QA).sets[(rowRD D)[f]!]! =
          bitsOfNat (sb (D.QA (fd (D.P f) 0 16383))) := by
        rw [rowR_get hf, orbDec_sets _ hrf]
      rw [hAf, hV]
      obtain ⟨hpos, hneg⟩ := muK_out h hf hb
      by_cases hp : popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
          (sb (D.QA (fd D.mt 0 16383)))) = 63
      · have he := hpos hp
        obtain ⟨hwl, hmaps, -⟩ := edgeWit_eq_of_edgeK hO h hrf hv0 he
        rw [if_pos hwl, hbit _ _ (by omega), edgeK_not_mem he, hmaps]
        rfl
      · rw [hneg hp, if_neg (by decide), commonCount_bitsOfNat (sb_lt _)]
        simpa using hp
    · rfl
  ·
    refine allIn_lo.2 fun k _ hk => ?_
    rw [Array.size_ofFn] at hk
    rw [hget (fun i => fd (D.M i) 0 4095) k hk, B0_at h (pts_lt h k hk), hout k hk,
      muW_get (pts_lt h k hk), decide_eq_true (pts_lt h k hk), decide_eq_true (hP3 k hk).1]
    rfl
  ·
    refine allIn_lo.2 fun k hk1 hk => ?_
    rw [Array.size_ofFn] at hk
    obtain ⟨hpar, hed⟩ := muTree_facts h k (by omega) hk
    have hpn : fd (D.M k) 12 1023 < fd D.mt 70 1023 := by omega
    rw [hget (fun i => fd (D.M i) 12 1023) k hk, hget (fun i => fd (D.M i) 22 4095) k hk,
      hget (fun i => fd (D.M i) 0 4095) _ hpn, hget (fun i => fd (D.M i) 0 4095) k hk,
      hA _ hpn, hA k hk]
    rw [(hP3 _ hpn).2, (hP3 k hk).2] at hed
    have hrp := rowR_lt h (pts_lt h _ hpn) (hP3 _ hpn).1
    have hrk := rowR_lt h (pts_lt h k hk) (hP3 k hk).1
    obtain ⟨hwl, hmaps, -⟩ := edgeWit_eq_of_edgeK hO h hrp hrk hed
    have hni : (sb (D.QA (fd (D.P (fd (D.M (fd (D.M k) 12 1023)) 0 4095)) 0 16383))).testBit
        (fd (D.M k) 22 4095) = false := edgeK_not_mem hed
    rw [decide_eq_true hpar, decide_eq_true hwl, hbit _ _ (by omega), hni, hmaps]
    rfl
  ·
    refine allIn_lo.2 fun f _ hf => ?_
    rw [B0_at h hf, muW_get hf]
    cases hb : (bs D.lb0).testBit f
    · rw [Bool.false_or]
      by_cases hw : fd (D.P f) 14 4095 < 3510
      · have hpn := hP6 f hf hw
        have hpf : fd (D.M (mPos D.mq f)) 0 4095 = f := by
          rcases hP5 f hf with e | ⟨-, e⟩
          · omega
          · exact e
        have hmem : f ∈ (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 0 4095) :=
          Array.mem_ofFn.2 ⟨⟨mPos D.mq f, hpn⟩, hpf⟩
        rw [Array.contains_iff_mem.2 hmem, Bool.or_true]
      · have hrf := ((rowF_spec h hf).2 hb).1
        obtain ⟨hpos, hneg⟩ := muK_out h hf hb
        have hw' : fd (D.P f) 14 4095 = 3510 := by
          by_cases hp : popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
              (sb (D.QA (fd D.mt 0 16383)))) = 63
          · exact absurd (edgeWit_eq_of_edgeK hO h hrf hv0 (hpos hp)).1 hw
          · exact hneg hp
        rw [hw']
        rfl
    · rfl

end CFSG.KS.Fi22LH
