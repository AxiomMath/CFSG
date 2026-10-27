module

public import Certificates.Data.Kernel.W4Row.EPackK
public import Certificates.Data.W4RowHSE9
public import Certificates.Data.W4RowHeE25
public import CFSG.Certificates.Kernel.W4Row.E25KSound

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.LQT.TCK
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CFSG.Sporadic.RuSchreier

variable {n w : ℕ}

theorem mem_zip_self {α : Type} {l : List α} {a : α} (h : a ∈ l) : (a, a) ∈ l.zip l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.zip_cons_cons]
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

section Checks

variable (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)

include hn hnw hid

theorem allLt_pow_eq {x y : Array ℕ} {X Y : ℕ} (hx : RR n w x X) (hy : RR n w y Y) (p : ℕ) :
    allLt p (fun j => !eqA n y (powA n x j)) =
      allN p (fun j => !Nat.beq Y (ppow n w (mask w) idn X j)) := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [hy.eqA (hx.pow hn hnw hid j)]

theorem e9Pack_eq {x y m₁ m₂ m₃ k : PArr} {X Y M1 M1I M2 M2I M3 M3I K KI : ℕ}
    (hx : RR n w x.1 X) (hy : RR n w y.1 Y) (h1 : PrP n w m₁ M1 M1I) (h2 : PrP n w m₂ M2 M2I)
    (h3 : PrP n w m₃ M3 M3I) (hk : PrP n w k K KI) :
    e9PackCheck n x y m₁ m₂ m₃ k = e9PackK n w idn X Y M1 M1I M2 M2I M3 M3I K KI := by
  obtain ⟨a1, b1⟩ := rr_of_prp h1
  obtain ⟨a2, b2⟩ := rr_of_prp h2
  obtain ⟨a3, b3⟩ := rr_of_prp h3
  obtain ⟨ak, bk⟩ := rr_of_prp hk
  have hb := hx.comp hn hnw ((ak.comp hn hnw hx).comp hn hnw bk)
  unfold e9PackCheck e9PackK
  dsimp only
  rw [(hx.pow hn hnw hid 3).eqA (RR.id hid), (hy.pow hn hnw hid 3).eqA (RR.id hid),
    hx.eqA (RR.id hid), (hx.comp hn hnw hy).eqA (hy.comp hn hnw hx),
    allLt_pow_eq hn hnw hid hx hy, ((a1.comp hn hnw hx).comp hn hnw b1).eqA hy,
    ((a2.comp hn hnw hx).comp hn hnw b2).eqA (hx.comp hn hnw hy),
    ((a3.comp hn hnw hx).comp hn hnw b3).eqA (hx.comp hn hnw (hy.pow hn hnw hid 2)),
    (hb.pow hn hnw hid 5).eqA (RR.id hid), hb.eqA (RR.id hid)]

theorem e25Pack_eq {x y m₁ m₂ m₃ m₄ m₅ : PArr} {X Y M1 M1I M2 M2I M3 M3I M4 M4I M5 M5I : ℕ}
    (hx : RR n w x.1 X) (hy : RR n w y.1 Y) (h1 : PrP n w m₁ M1 M1I) (h2 : PrP n w m₂ M2 M2I)
    (h3 : PrP n w m₃ M3 M3I) (h4 : PrP n w m₄ M4 M4I) (h5 : PrP n w m₅ M5 M5I) :
    e25PackCheck n x y m₁ m₂ m₃ m₄ m₅ =
      e25PackK n w idn X Y M1 M1I M2 M2I M3 M3I M4 M4I M5 M5I := by
  obtain ⟨a1, b1⟩ := rr_of_prp h1
  obtain ⟨a2, b2⟩ := rr_of_prp h2
  obtain ⟨a3, b3⟩ := rr_of_prp h3
  obtain ⟨a4, b4⟩ := rr_of_prp h4
  obtain ⟨a5, b5⟩ := rr_of_prp h5
  unfold e25PackCheck e25PackK
  dsimp only
  rw [(hx.pow hn hnw hid 5).eqA (RR.id hid), (hy.pow hn hnw hid 5).eqA (RR.id hid),
    hx.eqA (RR.id hid), (hx.comp hn hnw hy).eqA (hy.comp hn hnw hx),
    allLt_pow_eq hn hnw hid hx hy, ((a1.comp hn hnw hx).comp hn hnw b1).eqA hy,
    ((a2.comp hn hnw hx).comp hn hnw b2).eqA (hx.comp hn hnw hy),
    ((a3.comp hn hnw hx).comp hn hnw b3).eqA (hx.comp hn hnw (hy.pow hn hnw hid 2)),
    ((a4.comp hn hnw hx).comp hn hnw b4).eqA (hx.comp hn hnw (hy.pow hn hnw hid 3)),
    ((a5.comp hn hnw hx).comp hn hnw b5).eqA (hx.comp hn hnw (hy.pow hn hnw hid 4))]

end Checks

theorem conjInvs_of (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {TS : List ℕ}
    (ht : ∀ t ∈ TS, PrP n w (unpack n w t, unpack n w t) t t) :
    ∀ {hs : List PArr} {HS : List (ℕ × ℕ)}, List.Forall₂ (fun r P => PrP n w r P.1 P.2) hs HS →
      ∀ {x : PArr} {X XI : ℕ}, PrP n w x X XI →
      ((TS.zip HS).all fun q => conjInvK n w q.1 q.1 q.2.1 q.2.2 X XI) = true →
      ((TS.zip hs).all fun q => conjInvCheck n (unpack n w q.1, unpack n w q.1) q.2 x) = true := by
  induction TS with
  | nil => intros; rfl
  | cons t TS ih =>
    intro hs HS hm x X XI hx h
    cases hm with
    | nil => rfl
    | cons hr hm' =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h ⊢
      exact ⟨(conjInv_eq hn hnw (ht t (by simp)) hr hx).trans h.1,
        ih (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht')) hm' hx h.2⟩

theorem e9Full_of {G GI TS : List ℕ} {wx wy wm1 wm2 wm3 wk : List ℤ} {whs : List (List ℤ)}
    (h : e9FullK n w G GI TS wx wy wm1 wm2 wm3 wk whs = true) :
    e9PackCheck n (pWord n (unpackP n w G GI) wx) (pWord n (unpackP n w G GI) wy)
        (pWord n (unpackP n w G GI) wm1) (pWord n (unpackP n w G GI) wm2)
        (pWord n (unpackP n w G GI) wm3) (pWord n (unpackP n w G GI) wk) = true ∧
      ((TS.zip (whs.map (pWord n (unpackP n w G GI)))).all fun q =>
        conjInvCheck n (unpack n w q.1, unpack n w q.1) q.2 (pWord n (unpackP n w G GI) wx)) =
        true := by
  unfold e9FullK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨ht, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨-, tz⟩ := gensTc_sound TS TS ht
  have hT : ∀ t ∈ TS, PrP n w (unpack n w t, unpack n w t) t t := fun t ht' =>
    prp_of_permOK (tz (t, t) (mem_zip_self ht'))
  obtain ⟨X, XI, h, hX⟩ := wordP_sound hn hnw hidn hl hz wx _ h
  obtain ⟨Y, YI, h, hY⟩ := wordP_sound hn hnw hidn hl hz wy _ h
  obtain ⟨M1, M1I, h, h1⟩ := wordP_sound hn hnw hidn hl hz wm1 _ h
  obtain ⟨M2, M2I, h, h2⟩ := wordP_sound hn hnw hidn hl hz wm2 _ h
  obtain ⟨M3, M3I, h, h3⟩ := wordP_sound hn hnw hidn hl hz wm3 _ h
  obtain ⟨K, KI, h, hK⟩ := wordP_sound hn hnw hidn hl hz wk _ h
  obtain ⟨HS, h, hH⟩ := wordsP_sound hn hnw hidn hl hz whs _ h
  replace hX : PrP n w (pWord n (unpackP n w G GI) wx) X XI := hX
  replace hY : PrP n w (pWord n (unpackP n w G GI) wy) Y YI := hY
  replace h1 : PrP n w (pWord n (unpackP n w G GI) wm1) M1 M1I := h1
  replace h2 : PrP n w (pWord n (unpackP n w G GI) wm2) M2 M2I := h2
  replace h3 : PrP n w (pWord n (unpackP n w G GI) wm3) M3 M3I := h3
  replace hK : PrP n w (pWord n (unpackP n w G GI) wk) K KI := hK
  rw [Bool.and_eq_true] at h
  obtain ⟨he, hc⟩ := h
  unfold conjInvsK at hc
  rw [Bool.and_eq_true] at hc
  refine ⟨?_, conjInvs_of hn hnw hT hH hX hc.2⟩
  rw [e9Pack_eq hn hnw hidn (rr_of_prp hX).1 (rr_of_prp hY).1 h1 h2 h3 hK]
  exact he

end CFSG.KC.W4E

end
