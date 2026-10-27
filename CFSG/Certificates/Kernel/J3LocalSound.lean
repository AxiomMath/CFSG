module

public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsKSound
public import CFSG.Certificates.Kernel.OpsF2FrMcert
public import CFSG.Certificates.Kernel.J3LocalLanes
import all CFSG.Certificates.Kernel.OpsF2KMcertSound
import CFSG.Certificates.Kernel.Co1BTrSound

public section

namespace CFSG.KC.J3Loc

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2
open CFSG.Sporadic.SmallF2.Native (transposeRows ofBits)
open CFSG.KC.Co1F2 (unpackR)

theorem strictB_eqL (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem testBit_orN_pw (c : Nat → Bool) (k : Nat) : ∀ n,
    (orN n fun i => Bool.rec (motive := fun _ => Nat) 0 (pw2 i) (c i)).testBit k =
      (decide (k < n) && c k)
  | 0 => by simp [orN]
  | n + 1 => by
    rw [CFSG.KC.F2W.orN_succ, Nat.testBit_or, testBit_orN_pw c k n, nIf_eq, pw2_eqP]
    by_cases hk : k = n
    · subst hk
      cases c k <;> simp
    · have : k < n + 1 ↔ k < n := by omega
      cases c n <;> simp [Nat.testBit_two_pow, Ne.symm hk, this]

theorem testBit_tcol (X j k : Nat) :
    (tcol X j).testBit k = (decide (k < 80) && X.testBit (80 * k + j)) := by
  unfold tcol
  rw [testBit_orN_pw, CFSG.KC.F2W.bit_eq]
  rfl

theorem tcol_lt (X j : Nat) : tcol X j < 2 ^ 80 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_tcol]
    simp [show ¬ k < 80 by omega]

theorem tF_eq (X : Nat) : unpackR 80 (tF X) = transposeRows 80 (unpackR 80 X) := by
  unfold transposeRows
  conv_lhs => rw [unpackR]
  congr 1
  funext j
  rw [← CFSG.KC.F2W.rowF_eq]
  have e : rowF 80 (tF X) j.val = tcol X j.val :=
    CFSG.KC.F2W.rowF_orN 80 (f := tcol X) (fun i _ => tcol_lt X i) j.isLt
  rw [e]
  unfold ofBits
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_tcol, CFSG.KC.F2W.testBit_ofBitsFold]
  by_cases hk : k < 80
  · have hg : (unpackR 80 X)[k]?.getD 0 = X / 2 ^ (80 * k) % 2 ^ 80 := by simp [unpackR, hk]
    rw [hg, testBit_field]
    simp [hk, j.isLt]
  · simp [hk]

theorem nbeq (x y : Nat) : Nat.beq x y = decide (x = y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem beqN (x y : Nat) : (x == y) = Nat.beq x y := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem vmF_unit_aux (d M t : Nat) : ∀ k, Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => if (2 ^ t).testBit k then rowF d M k ^^^ acc else acc) k =
      if t < k then rowF d M t else 0
  | 0 => by simp
  | k + 1 => by
    change (if (2 ^ t).testBit k then rowF d M k ^^^ _ else _) = _
    rw [vmF_unit_aux d M t k, Nat.testBit_two_pow]
    by_cases htk : t = k
    · subst htk
      simp
    · have : t < k + 1 ↔ t < k := by omega
      simp [htk, this]

theorem vmF_unit {d t : Nat} (M : Nat) (ht : t < d) : vmF d M (2 ^ t) = rowF d M t := by
  rw [CFSG.KC.F2W.vmF_rec, vmF_unit_aux, if_pos ht]

theorem vne_fr (u w : Nat) : (ops2fr 80).vne u w = !Nat.beq (u % 2 ^ 80) (w % 2 ^ 80) :=
  vne_eq 80 u w

theorem vne_T {u w : Nat} (hu : u < 2 ^ 80) (hw : w < 2 ^ 80) (h : u ≠ w) :
    (ops2fr 80).vne u w = true := by
  rw [vne_fr, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw, nbeq]
  simp [h]

theorem matNe_eq (a b : Nat) :
    matNe (unpackR 80 a) (unpackR 80 b) = !(opsF2K 80).eq a b := by
  have hvm : ∀ (v : Nat) (X : Array Nat), (ops2fr 80).vmul v X =
      CFSG.Sporadic.SmallF2.Native.vecMulN 80 X v := fun _ _ => rfl
  have hu : ∀ t, (ops2fr 80).unit t = 2 ^ t := fun t => Nat.one_shiftLeft t
  have hrow : ∀ t ∈ List.range 80, (ops2fr 80).vne ((ops2fr 80).vmul ((ops2fr 80).unit t)
      (unpackR 80 a)) ((ops2fr 80).vmul ((ops2fr 80).unit t) (unpackR 80 b)) =
      !decide (rowF 80 a t = rowF 80 b t) := by
    intro t ht
    have ht' := List.mem_range.1 ht
    rw [hvm, hvm, hu, CFSG.KC.F2W.vecMulN_unpackR, CFSG.KC.F2W.vecMulN_unpackR,
      vmF_unit a ht', vmF_unit b ht', vne_fr, Nat.mod_eq_of_lt (CFSG.KC.F2W.rowF_lt _ _ _),
      Nat.mod_eq_of_lt (CFSG.KC.F2W.rowF_lt _ _ _), nbeq]
  have hK : (opsF2K 80).eq a b = Nat.beq (a % 2 ^ (80 * 80)) (b % 2 ^ (80 * 80)) :=
    ((hom2 80 (by norm_num)).eq trivial trivial).symm.trans (beq_unpackR (by norm_num) a b)
  have hf := fields_eq_iff (w := 80) (by norm_num) 80 a b
  unfold matNe
  rw [hK, nbeq]
  by_cases hP : a % 2 ^ (80 * 80) = b % 2 ^ (80 * 80)
  · rw [decide_eq_true hP, Bool.not_true, List.any_eq_false]
    intro t ht
    rw [hrow t ht, CFSG.KC.F2W.rowF_eq, CFSG.KC.F2W.rowF_eq, hf.2 hP t (List.mem_range.1 ht)]
    simp
  · rw [decide_eq_false hP, Bool.not_false, List.any_eq_true]
    by_contra hc
    push Not at hc
    apply hP
    apply hf.1
    intro i hi
    have h3 := hc i (List.mem_range.2 hi)
    rw [hrow i (List.mem_range.2 hi)] at h3
    simpa [CFSG.KC.F2W.rowF_eq] using h3

theorem colAct_eq (x v : Nat) : colAct (unpackR 80 x) v = colK x v := by
  unfold colAct colK
  rw [← tF_eq, CFSG.KC.F2W.vecMulN_unpackR]

theorem size_unpackR (x : Nat) : (unpackR 80 x).size ≤ 80 := by
  simp [unpackR]

theorem pow_eqF (x e : Nat) :
    (ops2fr 80).pow (unpackR 80 x) e = unpackR 80 ((opsF2K 80).pow x e) := by
  rw [(CFSG.KC.OpsF2K.pow_fr e _ (size_unpackR x)).1]
  exact ((hom2 80 (by norm_num)).pow_U e trivial).1

theorem one_eqF : (ops2fr 80).one = unpackR 80 (opsF2K 80).one :=
  (hom2 80 (by norm_num)).one.1

theorem getElem!_toArrayL {l : List (Array Nat)} {k : Nat} (hk : k < l.length) :
    l.toArray[k]! = l[k] := by
  rw [getElem!_pos l.toArray k (by simpa using hk)]
  simp

theorem extra_of_K {J : J3Cert} {Ra : Array (Array Nat)} {Rl : List Nat}
    (hR : Rel (hom2 80 (by norm_num)) Ra Rl) (hl : Rl.length = J.nregs)
    (hsz : ∀ x ∈ Ra, x.size ≤ 80) {pts : Array Nat} {n : Nat} {P : Nat → Nat} (h1 : 1 ≤ n)
    (h2 : n ≤ 65536) (hpts : ∀ i < n, pts[i]! = P i) (hP : ∀ i < n, P i < 2 ^ 80)
    (h : extraK J (P 0) (lanesP P n) (onesL n) Rl = true) : j3Extra Ra pts n J = true := by
  have hget : ∀ r < J.nregs, Ra[r]! = unpackR 80 (getN Rl r) := fun r hr =>
    (hR.2 r (by rw [hl]; exact hr)).1
  have hev : ∀ w, wordLt J.nregs w = true →
      evalW (ops2fr 80) Ra w = unpackR 80 (evalWN (opsF2K 80) Rl w) := fun w hw => by
    rw [(CFSG.KC.OpsF2K.evalW_fr hsz w).1]
    exact (evalW_U (hom2 80 (by norm_num)) hR w (by rw [hl]; exact hw)).1
  have hvne : ∀ u w, (ops2fr 80).vne u w = (opsF2K 80).vne u w := fun u w =>
    (hom2 80 (by norm_num)).vne trivial trivial
  have hroot : pts[0]! = P 0 := hpts 0 h1
  unfold extraK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hr, hm⟩, hrt⟩, hmv⟩, hne⟩, hss⟩, hconj⟩, hcube⟩, hlen⟩ := h
  unfold rangeK at hr
  simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨r0, r1⟩, r2⟩, s0⟩, s1⟩, hsr⟩, hcr⟩ := hr
  have hwb : ∀ k, wordLt J.nregs (basisW J.rb k) = true := fun k => by
    simp [wordLt, basisW, r0, r1, r2]
  have hbw : ∀ k, evalW (ops2fr 80) Ra (basisW J.rb k) =
      unpackR 80 (evalWN (opsF2K 80) Rl (basisW J.rb k)) := fun k => hev _ (hwb k)
  unfold j3Extra
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold movedOK
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [Bool.or_eq_true]
    by_cases hc : J.xs.contains i = true
    · exact Or.inl hc
    · refine Or.inr (List.all_eq_true.2 fun T hT => ?_)
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hT
      rw [hbw, ← tF_eq, CFSG.KC.F2W.vecMulN_unpackR, hpts i hi]
      rcases moved_of_K h1 h2 hP (List.all_eq_true.1 hm k hk) i hi with h | h
      · exact absurd h hc
      · exact vne_T (CFSG.KC.F2W.vmF_lt _ _ _) (hP i hi) h
  · rw [hget _ r0, colAct_eq, hroot, beqN]
    exact hrt
  · refine List.all_eq_true.2 fun k hk => ?_
    rw [hbw, colAct_eq, hroot, hvne]
    exact List.all_eq_true.1 hmv k hk
  · refine List.all_eq_true.2 fun k hk => ?_
    rw [hbw, one_eqF, matNe_eq]
    exact List.all_eq_true.1 hne k hk
  · refine List.all_eq_true.2 fun s hs => ?_
    rw [hget _ (hsr s hs), colAct_eq, hroot, beqN]
    exact List.all_eq_true.1 hss s hs
  · have hC : (J.cs.map fun c => Ra[c]!) = (J.cs.map (getN Rl)).map (unpackR 80) := by
      rw [List.map_map]
      exact List.map_congr_left fun c hc => hget c (hcr c hc)
    rw [hC]
    generalize hK : J.cs.map (getN Rl) = CK at hconj
    unfold conjOK
    simp only [List.all_eq_true, List.mem_range, List.size_toArray, List.length_map]
    intro k hk l hl'
    have hq := List.all_eq_true.1 (List.all_eq_true.1 hconj (CK[k], k)
      (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hk)))
      ((CK.zip (CK.map fun X => powN (opsF2K 80) 3 X 2))[l]'(by simpa using hl'), l)
      (List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem _))
    rw [List.getElem_zip, List.getElem_map] at hq
    have e1 : ((CK.map (unpackR 80)).toArray)[k]! = unpackR 80 CK[k] := by
      rw [getElem!_toArrayL (by simpa using hk), List.getElem_map]
    have e2 : ((CK.map (unpackR 80)).toArray)[l]! = unpackR 80 CK[l] := by
      rw [getElem!_toArrayL (by simpa using hl'), List.getElem_map]
    have e3 : (((CK.map (unpackR 80)).toArray).map fun X => (ops2fr 80).pow X 2)[l]! =
        unpackR 80 ((opsF2K 80).pow CK[l] 2) := by
      rw [List.map_toArray, getElem!_toArrayL (by simpa using hl'), List.getElem_map,
        List.getElem_map, pow_eqF]
    rw [e1, e2, e3, matNe_eq, matNe_eq, beqN, ← powN_eq (opsF2K 80) 3 _ 2 (by norm_num)]
    simpa using hq
  · refine List.all_eq_true.2 fun k _ => List.all_eq_true.2 fun m hm' => ?_
    have hw : wordLt J.nregs (basisW J.rb k ++ hW J.rh (m + 1)) = true := by
      simp [wordLt, basisW, hW, r0, r1, r2, s0, s1]
    rw [hev _ hw, pow_eqF, one_eqF, matNe_eq, ← powN_eq (opsF2K 80) 4 _ 3 (by norm_num)]
    exact List.all_eq_true.1 (List.all_eq_true.1 hcube k (by assumption)) m hm'
  · rw [beqN]
    exact hlen

theorem j3Check_of_K {sA sB : String} {A B : Nat} (eA : (ops2 80).decode sA = unpackR 80 A)
    (eB : (ops2 80).decode sB = unpackR 80 B) {pts : Array Nat} {n : Nat} {P : Nat → Nat}
    {J : J3Cert} (h1 : 1 ≤ n) (h2 : n ≤ 65536) (hpts : ∀ i < n, pts[i]! = P i)
    (hP : ∀ i < n, P i < 2 ^ 80) (h : fullK A B P n J = true) :
    j3Check sA sB pts n J = true := by
  unfold fullK at h
  rw [strictB_eqL, strictB_eqL, regsN_eq, Bool.and_eq_true] at h
  obtain ⟨hc, hx⟩ := h
  have hp : J.prog.all (Op.lt J.nregs) = true := by
    unfold certN at hc
    simp only [Bool.and_eq_true] at hc
    exact hc.1.2
  obtain ⟨hregs, hsz⟩ := CFSG.KC.OpsF2K.regsOf_fr (d := 80) sA sB J.nregs J.prog
  unfold j3Check
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [CFSG.KC.OpsF2K.mcertCheck_fr_eq, mcertCheck_eq (hom2 80 (by norm_num)) eA eB trivial trivial]
    unfold mcertN
    rw [regsN_eq]
    exact hc
  · rw [hregs]
    exact extra_of_K (rel_regsOf (hom2 80 (by norm_num)) eA eB trivial trivial hp)
      (by rw [length_run, length_initN]) hsz h1 h2 hpts hP hx

end CFSG.KC.J3Loc

end
