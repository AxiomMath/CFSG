module

public import Certificates.Data.Kernel.W4Row.E25K
public import Certificates.Data.W4RowJ2E25
public import CFSG.Certificates.Kernel.LocalQTTcPSound
public import CFSG.Certificates.Kernel.LocalQTTcPProved
public import Certificates.Data.Kernel.SporSch.IntLines
import CFSG.Certificates.Kernel.SporSch.IntLinesSound

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.LQT.TCK
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CFSG.Sporadic.RuSchreier

theorem parseInts_str {s : String}
    (h : (CFSG.KC.IntLines.intsSK (CFSG.KC.LQT.Cov.tokK s.toList)).isSome = true) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = CFSG.KC.IntLines.lineInts s.toList := by
  obtain ⟨xs, hx⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨h1, h2⟩ := CFSG.KC.IntLines.line_parse hx
  rw [String.ofList_toList] at h1
  unfold CFSG.Quasithin.B45Exc.Tab.parseInts
  rw [h1, h2]

variable {n w : ℕ}

@[expose] def RR (n w : ℕ) (a : Array ℕ) (P : ℕ) : Prop :=
  ∃ g : Equiv.Perm (Fin n), Rep n a g ∧ RS n w P g

theorem RR.comp (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {a b : Array ℕ} {P Q : ℕ}
    (ha : RR n w a P) (hb : RR n w b Q) : RR n w (compA n a b) (pcomp n w (mask w) P Q) := by
  obtain ⟨g, h1, h2⟩ := ha
  obtain ⟨h, h3, h4⟩ := hb
  exact ⟨g * h, rep_compA h1 h3, rs_pcomp hn hnw h2 h4⟩

theorem RR.id {idn : ℕ} (hid : RS n w idn 1) : RR n w (idA n) idn := ⟨1, rep_idA, hid⟩

theorem ppow_succ (idn P e : ℕ) :
    ppow n w (mask w) idn P (e + 1) = pcomp n w (mask w) P (ppow n w (mask w) idn P e) := by
  change strictN (ppow n w (mask w) idn P e) (fun q => pcomp n w (mask w) P q) = _
  generalize ppow n w (mask w) idn P e = y
  cases y <;> rfl

theorem RR.pow (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1) {a : Array ℕ}
    {P : ℕ} (ha : RR n w a P) : ∀ e, RR n w (powA n a e) (ppow n w (mask w) idn P e)
  | 0 => RR.id hid
  | e + 1 => by
    rw [ppow_succ]
    exact ha.comp hn hnw (RR.pow hn hnw hid ha e)

theorem RR.eqA {a b : Array ℕ} {P Q : ℕ} (ha : RR n w a P) (hb : RR n w b Q) :
    eqA n a b = Nat.beq P Q := by
  obtain ⟨g, h1, h2⟩ := ha
  obtain ⟨h, h3, h4⟩ := hb
  apply Bool.eq_iff_iff.2
  rw [eqA_iff h1 h3]
  constructor
  · rintro rfl
    rw [eq_of_rs h2 h4]
    exact Nat.beq_refl Q
  · intro e
    rw [Nat.eq_of_beq_eq_true e] at h2
    exact rp_unique h2.1 h4.1

theorem rr_of_prp {r : PArr} {A AI : ℕ} (h : PrP n w r A AI) : RR n w r.1 A ∧ RR n w r.2 AI := by
  obtain ⟨g, h1, h2, h3⟩ := h
  exact ⟨⟨g, h1.1, h2⟩, ⟨g⁻¹, h1.2, h3⟩⟩

section Checks

variable (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)
  {x y : Array ℕ} {X Y : ℕ} (hx : RR n w x X) (hy : RR n w y Y)

include hn hnw hid hx hy

theorem ep2Line_rr : ∀ i, RR n w (ep2LineA n x y i) (ep2LineK n w idn X Y i)
  | 0 => hy
  | i + 1 => hx.comp hn hnw (hy.pow hn hnw hid i)

theorem ep2Base_eq (p : ℕ) : ep2BaseCheck n p x y = ep2BaseK n w idn p X Y := by
  unfold ep2BaseCheck ep2BaseK
  rw [(hx.pow hn hnw hid p).eqA (RR.id hid), (hy.pow hn hnw hid p).eqA (RR.id hid),
    hx.eqA (RR.id hid), (hx.comp hn hnw hy).eqA (hy.comp hn hnw hx)]
  congr 1
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [hy.eqA (hx.pow hn hnw hid j)]

theorem ep2Part_eq (idx : List (ℕ × ℕ × ℕ)) {ms : List PArr} {MS : List (ℕ × ℕ)}
    (hm : List.Forall₂ (fun r P => PrP n w r P.1 P.2) ms MS) :
    ep2PartCheck n x y idx ms = ep2PartK n w idn X Y idx MS := by
  unfold ep2PartCheck ep2PartK
  rw [hm.length_eq]
  congr 1
  induction idx generalizing ms MS with
  | nil => rfl
  | cons q idx ih =>
    cases hm with
    | nil => rfl
    | cons hr hm' =>
      rw [List.zip_cons_cons, List.zip_cons_cons, List.all_cons, List.all_cons, ih hm']
      obtain ⟨r1, r2⟩ := rr_of_prp hr
      rw [(((r1.comp hn hnw (ep2Line_rr hn hnw hid hx hy q.1)).comp hn hnw r2)).eqA
        ((ep2Line_rr hn hnw hid hx hy q.2.1).pow hn hnw hid q.2.2)]

end Checks

theorem conjInv_eq (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {t h x : PArr} {T TI H HI X XI : ℕ}
    (ht : PrP n w t T TI) (hh : PrP n w h H HI) (hx : PrP n w x X XI) :
    conjInvCheck n t h x = conjInvK n w T TI H HI X XI := by
  obtain ⟨t1, t2⟩ := rr_of_prp ht
  obtain ⟨h1, h2⟩ := rr_of_prp hh
  obtain ⟨x1, x2⟩ := rr_of_prp hx
  unfold conjInvCheck conjInvK
  exact RR.eqA ((t1.comp hn hnw ((h1.comp hn hnw x1).comp hn hnw h2)).comp hn hnw t2)
    ((h1.comp hn hnw x2).comp hn hnw h2)

section Words

variable {idn : ℕ} {G GI : List ℕ} (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) (hid : RS n w idn 1)
  (hl : G.length = GI.length) (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true)

include hn hnw hid hl hz in
theorem wordsP_sound : ∀ (ws : List (List ℤ)) (k : List (ℕ × ℕ) → Bool),
    wordsP n w idn G GI ws k = true → ∃ L, k L = true ∧
      List.Forall₂ (fun r P => PrP n w r P.1 P.2) (ws.map (pWord n (unpackP n w G GI))) L
  | [], _, h => ⟨[], h, List.Forall₂.nil⟩
  | wd :: ws, k, h => by
    change wordP n w idn G GI wd (fun A AI => wordsP n w idn G GI ws fun L => k ((A, AI) :: L)) =
      true at h
    obtain ⟨A, AI, h1, hA⟩ := wordP_sound hn hnw hid hl hz wd _ h
    obtain ⟨L, h2, hL⟩ := wordsP_sound ws _ h1
    exact ⟨(A, AI) :: L, h2, List.Forall₂.cons hA hL⟩

end Words

theorem ep2Pack_of {p : ℕ} {G GI : List ℕ} {TB TA : ℕ} {idx : List (ℕ × ℕ × ℕ)}
    {wx wy whb wha : List ℤ} {wms : List (List ℤ)}
    (h : ep2PackK n w p G GI TB TA idx wx wy whb wha wms = true) :
    (ep2BaseCheck n p (pWord n (unpackP n w G GI) wx).1 (pWord n (unpackP n w G GI) wy).1 &&
      ep2PartCheck n (pWord n (unpackP n w G GI) wx).1 (pWord n (unpackP n w G GI) wy).1 idx
        (wms.map (pWord n (unpackP n w G GI))) &&
      conjInvCheck n (unpack n w TB, unpack n w TB) (pWord n (unpackP n w G GI) whb)
        (pWord n (unpackP n w G GI) wx) &&
      conjInvCheck n (unpack n w TA, unpack n w TA) (pWord n (unpackP n w G GI) wha)
        (pWord n (unpackP n w G GI) wx)) = true := by
  unfold ep2PackK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨ht, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨-, tz⟩ := gensTc_sound [TB, TA] [TB, TA] ht
  have hTB := prp_of_permOK (tz (TB, TB) (by simp))
  have hTA := prp_of_permOK (tz (TA, TA) (by simp))
  obtain ⟨X, XI, h, hX⟩ := wordP_sound hn hnw hidn hl hz wx _ h
  obtain ⟨Y, YI, h, hY⟩ := wordP_sound hn hnw hidn hl hz wy _ h
  obtain ⟨B, BI, h, hB⟩ := wordP_sound hn hnw hidn hl hz whb _ h
  obtain ⟨A, AI, h, hA⟩ := wordP_sound hn hnw hidn hl hz wha _ h
  obtain ⟨MS, h, hM⟩ := wordsP_sound hn hnw hidn hl hz wms _ h
  replace hX : PrP n w (pWord n (unpackP n w G GI) wx) X XI := hX
  replace hY : PrP n w (pWord n (unpackP n w G GI) wy) Y YI := hY
  replace hB : PrP n w (pWord n (unpackP n w G GI) whb) B BI := hB
  replace hA : PrP n w (pWord n (unpackP n w G GI) wha) A AI := hA
  rw [ep2Base_eq hn hnw hidn (rr_of_prp hX).1 (rr_of_prp hY).1,
    ep2Part_eq hn hnw hidn (rr_of_prp hX).1 (rr_of_prp hY).1 idx hM,
    conjInv_eq hn hnw hTB hB hX, conjInv_eq hn hnw hTA hA hX]
  exact h

end CFSG.KC.W4E

end
