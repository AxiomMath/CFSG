module

public import CFSG.Certificates.Kernel.U43Pk.CoverSound
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.U43Pk

open CFSG.KD.U43Pk CFSG.KC.Enum CFSG.KC.Pack
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check

@[expose] noncomputable def powK (G n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) IDK (fun _ acc => strictN acc fun a => mulK G a) n

@[expose] noncomputable def selK (X X1 X2 i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) X2 X1 (Nat.beq i 1)) X (Nat.beq i 0)

@[expose] noncomputable def wordK (X X1 X2 : ℕ) (w : List (ℕ × ℕ)) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun l _ ih acc => strictN (strictN (selK X X1 X2 l.1) fun L => powK L l.2) fun Q =>
      strictN (mulK acc Q) ih) w

@[expose] noncomputable def tailK (X G1 G1I G2 G2I : ℕ) (wa wb : List (ℕ × ℕ)) (ma mb j : ℕ) :
    Bool :=
  strictB (mulK G1 X) fun a => strictB (mulK a G1I) fun X1 =>
  strictB (mulK G2 X) fun b => strictB (mulK b G2I) fun X2 =>
  strictB (wordK X X1 X2 wa IDK) fun A => strictB (wordK X X1 X2 wb IDK) fun B =>
  strictB (mulK A B) fun C => strictB (powK C j) fun Cj =>
  isZK (powK A ma) && isZK (powK B mb) && isZK (powK Cj 2) && !isZK Cj

@[expose] noncomputable def packA (x : Array ℕ) : ℕ :=
  Nat.add (packK fun k => x[k]!) (Nat.shiftLeft x[16]! 64)

@[expose] def okA (x : Array ℕ) : Bool :=
  x.size == 17 && (List.range 17).all fun k => decide (x[k]! < 16)

@[expose] noncomputable def repOKK (r : Rep) : Bool :=
  okA r.x && okA r.t && okA r.g1 && okA r.g1i && okA r.g2 && okA r.g2i &&
  strictB (packA r.x) fun X => strictB (packA r.t) fun T => strictB (packA r.g1) fun G1 =>
  strictB (packA r.g1i) fun G1I => strictB (packA r.g2) fun G2 => strictB (packA r.g2i) fun G2I =>
    rawValidK X && rawValidK T && rawValidK G1 && rawValidK G1I && rawValidK G2 && rawValidK G2I &&
    r.g1[16]! == 0 && r.g2[16]! == 0 && detC r.g1 == 3 && detC r.g2 == 3 &&
    isZK (mulK G1 G1I) && isZK (mulK G2 G2I) &&
    Nat.beq (nrmK (mulK G1 T)) (nrmK (mulK T G1)) && Nat.beq (nrmK (mulK G2 T)) (nrmK (mulK T G2)) &&
    r.wa.all (fun l => decide (l.1 < 3)) && r.wb.all (fun l => decide (l.1 < 3)) &&
    decide (r.ma % 2 = 1) && decide (r.mb % 2 = 1) && tailK X G1 G1I G2 G2I r.wa r.wb r.ma r.mb r.j

@[expose] noncomputable def repsK (D : Data) : Bool := D.reps.toList.all repOKK

theorem idK_dig : Dig IDK := by
  unfold Dig
  decide +kernel

theorem powK_succ (G n : ℕ) : powK G (n + 1) = mulK G (powK G n) := by
  change strictN (powK G n) (fun a => mulK G a) = _
  rw [strictN_eq]

theorem powK_lt (G : ℕ) : ∀ n, powK G n < 16 ^ 17
  | 0 => (by decide +kernel : IDK < 16 ^ 17)
  | n + 1 => by
    rw [powK_succ]
    exact mulK_lt _ _

theorem powRaw_dec {G : ℕ} (hG : Dig G) : ∀ n, powRaw (dec G) n = dec (powK G n) ∧ Dig (powK G n)
  | 0 => ⟨by rw [powRaw]; exact idCode_eq.symm, idK_dig⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := powRaw_dec hG n
    rw [powK_succ]
    exact ⟨by rw [powRaw, h1, mulRaw_dec hG h2], mulK_dig hG h2⟩

theorem sel_dec {X X1 X2 i : ℕ} (hi : i < 3) :
    (#[dec X, dec X1, dec X2] : Array (Array ℕ))[i]! = dec (selK X X1 X2 i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl

theorem sel_dig {X X1 X2 : ℕ} (hX : Dig X) (hX1 : Dig X1) (hX2 : Dig X2) (i : ℕ) :
    Dig (selK X X1 X2 i) := by
  unfold selK
  cases Nat.beq i 0 <;> cases Nat.beq i 1 <;> assumption

theorem wordK_cons (X X1 X2 : ℕ) (l : ℕ × ℕ) (w : List (ℕ × ℕ)) (acc : ℕ) :
    wordK X X1 X2 (l :: w) acc = wordK X X1 X2 w (mulK acc (powK (selK X X1 X2 l.1) l.2)) := by
  change strictN (strictN (selK X X1 X2 l.1) fun L => powK L l.2)
    (fun Q => strictN (mulK acc Q) (wordK X X1 X2 w)) = _
  rw [strictN_eq, strictN_eq, strictN_eq]

theorem foldl_dec {X X1 X2 : ℕ} (hX : Dig X) (hX1 : Dig X1) (hX2 : Dig X2) :
    ∀ (w : List (ℕ × ℕ)) (acc : ℕ), Dig acc → w.all (fun l => decide (l.1 < 3)) = true →
      w.foldl (fun a l => mulRaw a (powRaw (#[dec X, dec X1, dec X2] : Array (Array ℕ))[l.1]! l.2))
        (dec acc) = dec (wordK X X1 X2 w acc) ∧ Dig (wordK X X1 X2 w acc)
  | [], acc, h, _ => ⟨rfl, h⟩
  | l :: w, acc, h, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨hp1, hp2⟩ := powRaw_dec (sel_dig hX hX1 hX2 l.1) l.2
    rw [List.foldl_cons, sel_dec hw.1, hp1, mulRaw_dec h hp2, wordK_cons]
    exact foldl_dec hX hX1 hX2 w _ (mulK_dig h hp2) hw.2

theorem okA_dec {x : Array ℕ} (h : okA x = true) : x = dec (packA x) := by
  simp only [okA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hs, hl⟩ := h
  have hf : ∀ k, (fun k => x[k]!) k < 16 := fun k => by
    by_cases hk : k < 17
    · exact hl k hk
    · change x[k]! < 16
      rw [getElem!_neg x k (by omega)]
      decide
  apply eq_dec hs
  intro k hk
  unfold packA
  rw [dg_pack16 hf (hl 16 (by omega))]
  split_ifs with h1 h2
  · rfl
  · rw [h2]
  · omega

theorem repOK_of {r : Rep} (h : repOKK r = true) : repOK r = true := by
  unfold repOKK at h
  simp only [Bool.and_eq_true, strictB_eq, and_assoc] at h
  obtain ⟨hx, ht, hg1, hg1i, hg2, hg2i, h⟩ := h
  have ex := okA_dec hx
  have et := okA_dec ht
  have eg1 := okA_dec hg1
  have eg1i := okA_dec hg1i
  have eg2 := okA_dec hg2
  have eg2i := okA_dec hg2i
  generalize packA r.x = X at ex h
  generalize packA r.t = T at et h
  generalize packA r.g1 = G1 at eg1 h
  generalize packA r.g1i = G1I at eg1i h
  generalize packA r.g2 = G2 at eg2 h
  generalize packA r.g2i = G2I at eg2i h
  obtain ⟨vx, vt, vg1, vg1i, vg2, vg2i, h16a, h16b, hda, hdb, hz1, hz2, hc1, hc2, hwa, hwb, hma,
    hmb, hk⟩ := h
  have dX := (rawValidK_spec vx).2.1
  have dT := (rawValidK_spec vt).2.1
  have dG1 := (rawValidK_spec vg1).2.1
  have dG1I := (rawValidK_spec vg1i).2.1
  have dG2 := (rawValidK_spec vg2).2.1
  have dG2I := (rawValidK_spec vg2i).2.1
  have dX1 := mulK_dig (mulK_dig dG1 dX) dG1I
  have dX2 := mulK_dig (mulK_dig dG2 dX) dG2I
  have hX1 : repX1 r = dec (mulK (mulK G1 X) G1I) := by
    rw [repX1, eg1, ex, eg1i, mulRaw_dec dG1 dX, mulRaw_dec (mulK_dig dG1 dX) dG1I]
  have hX2 : repX2 r = dec (mulK (mulK G2 X) G2I) := by
    rw [repX2, eg2, ex, eg2i, mulRaw_dec dG2 dX, mulRaw_dec (mulK_dig dG2 dX) dG2I]
  have hW : ∀ w : List (ℕ × ℕ), w.all (fun l => decide (l.1 < 3)) = true →
      evalWord (repLetters r) w = dec (wordK X (mulK (mulK G1 X) G1I) (mulK (mulK G2 X) G2I) w IDK)
        ∧ Dig (wordK X (mulK (mulK G1 X) G1I) (mulK (mulK G2 X) G2I) w IDK) := fun w hw => by
    unfold evalWord repLetters
    rw [hX1, hX2, ex, ← idCode_eq]
    exact foldl_dec dX dX1 dX2 w IDK idK_dig hw
  obtain ⟨hA, dA⟩ := hW r.wa hwa
  obtain ⟨hB, dB⟩ := hW r.wb hwb
  unfold tailK at hk
  simp only [strictB_eq, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at hk
  obtain ⟨k1, k2, k3, k4⟩ := hk
  have hC : repC r = dec (mulK (wordK X (mulK (mulK G1 X) G1I) (mulK (mulK G2 X) G2I) r.wa IDK)
      (wordK X (mulK (mulK G1 X) G1I) (mulK (mulK G2 X) G2I) r.wb IDK)) := by
    rw [repC, repA, repB, hA, hB, mulRaw_dec dA dB]
  have dC := mulK_dig dA dB
  obtain ⟨hCj, dCj⟩ := powRaw_dec dC r.j
  unfold repOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h16a, h16b, hda, hdb, ?_, ?_, ?_, ?_, hwa, hwb, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [ex]
    exact rawValid_dec vx
  · rw [et]
    exact rawValid_dec vt
  · rw [eg1]
    exact rawValid_dec vg1
  · rw [eg1i]
    exact rawValid_dec vg1i
  · rw [eg2]
    exact rawValid_dec vg2
  · rw [eg2i]
    exact rawValid_dec vg2i
  · rw [eg1, eg1i, mulRaw_dec dG1 dG1I, isZ_dec (mulK_lt _ _)]
    exact hz1
  · rw [eg2, eg2i, mulRaw_dec dG2 dG2I, isZ_dec (mulK_lt _ _)]
    exact hz2
  · rw [eg1, et, mulRaw_dec dG1 dT, mulRaw_dec dT dG1, eqZ_dec (mulK_dig dG1 dT) (mulK_dig dT dG1)]
    exact hc1
  · rw [eg2, et, mulRaw_dec dG2 dT, mulRaw_dec dT dG2, eqZ_dec (mulK_dig dG2 dT) (mulK_dig dT dG2)]
    exact hc2
  · simpa using hma
  · rw [repA, hA, (powRaw_dec dA r.ma).1, isZ_dec (powK_lt _ _)]
    exact k1
  · simpa using hmb
  · rw [repB, hB, (powRaw_dec dB r.mb).1, isZ_dec (powK_lt _ _)]
    exact k2
  · rw [hC, hCj, (powRaw_dec dCj 2).1, isZ_dec (powK_lt _ _)]
    exact k3
  · rw [hC, hCj, isZ_dec (powK_lt _ _)]
    exact k4

theorem repsOK_of {D : Data} (h : repsK D = true) : repsOK D = true := by
  unfold repsK at h
  unfold repsOK
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => repOK_of (h r hr)

end CFSG.KS.U43Pk

end
