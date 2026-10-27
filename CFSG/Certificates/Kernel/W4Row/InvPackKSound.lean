module

public import Certificates.Data.Kernel.W4Row.InvPackK
public import Certificates.Data.W4RowRuE25
public import CFSG.Certificates.Kernel.W4Row.EPackKSound

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.TCP CFSG.KC.LQT.TCK
  CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row CFSG.Sporadic.RuSchreier

variable {n w : ℕ}

theorem allLt_allN {p : ℕ} {f g : ℕ → Bool} (h : ∀ j < p, f j = g j) : allLt p f = allN p g := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact forall_congr' fun j => forall_congr' fun hj => by rw [h j hj]

theorem invPack_eq (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)
    {τ y v h : PArr} {T TI Y YI W WI H HI : ℕ} (ht1 : RR n w τ.1 T) (ht2 : RR n w τ.2 TI)
    (hy : PrP n w y Y YI) (hv : PrP n w v W WI) (hh : PrP n w h H HI) (p m : ℕ)
    (cs : List (ℕ × ℕ)) :
    invPackCheck n p m τ y v h cs = invPackK n w idn p m T TI Y YI W WI H HI cs := by
  obtain ⟨y1, y2⟩ := rr_of_prp hy
  obtain ⟨v1, v2⟩ := rr_of_prp hv
  obtain ⟨h1, h2⟩ := rr_of_prp hh
  have hpr : ∀ ab : ℕ × ℕ,
      RR n w (compA n (powA n y.1 ab.1) (powA n v.1 ab.2)) (prK n w idn Y W ab) := fun ab =>
    (y1.pow hn hnw hid ab.1).comp hn hnw (v1.pow hn hnw hid ab.2)
  unfold invPackCheck invPackK
  dsimp only
  congr 1
  · rw [(y1.pow hn hnw hid p).eqA (RR.id hid), (v1.pow hn hnw hid p).eqA (RR.id hid),
      (y1.comp hn hnw v1).eqA (v1.comp hn hnw y1), y1.eqA (RR.id hid),
      allLt_pow_eq hn hnw hid y1 v1 p, ((ht1.comp hn hnw y1).comp hn hnw ht2).eqA y2,
      ((ht1.comp hn hnw v1).comp hn hnw ht2).eqA v2,
      ((h1.comp hn hnw y1).comp hn hnw h2).eqA (hpr (cs.getD 0 (0, 0))),
      ((h1.comp hn hnw v1).comp hn hnw h2).eqA (hpr (cs.getD 1 (0, 0))),
      ((h2.comp hn hnw y1).comp hn hnw h1).eqA (hpr (cs.getD 2 (0, 0))),
      ((h2.comp hn hnw v1).comp hn hnw h1).eqA (hpr (cs.getD 3 (0, 0)))]
  · refine allLt_allN fun a _ => allLt_allN fun b _ => ?_
    congr 1
    refine allLt_allN fun k _ => ?_
    congr 1
    refine allLt_allN fun j _ => ?_
    rw [(((h1.pow hn hnw hid k).comp hn hnw (hpr (a, b))).comp hn hnw
      (h2.pow hn hnw hid k)).eqA ((hpr (a, b)).pow hn hnw hid j)]

theorem invFull_of {p m : ℕ} {G GI : List ℕ} {T TI : ℕ} {wy ww wh : List ℤ}
    {cs : List (ℕ × ℕ)} {τ : PArr} (ht1 : RR n w τ.1 T) (ht2 : RR n w τ.2 TI)
    (h : invFullK n w p m G GI T TI wy ww wh cs = true) :
    invPackCheck n p m τ (pWord n (unpackP n w G GI) wy) (pWord n (unpackP n w G GI) ww)
      (pWord n (unpackP n w G GI) wh) cs = true := by
  unfold invFullK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  obtain ⟨Y, YI, h, hY⟩ := wordP_sound hn hnw hidn hl hz wy _ h
  obtain ⟨W, WI, h, hW⟩ := wordP_sound hn hnw hidn hl hz ww _ h
  obtain ⟨H, HI, h, hH⟩ := wordP_sound hn hnw hidn hl hz wh _ h
  replace hY : PrP n w (pWord n (unpackP n w G GI) wy) Y YI := hY
  replace hW : PrP n w (pWord n (unpackP n w G GI) ww) W WI := hW
  replace hH : PrP n w (pWord n (unpackP n w G GI) wh) H HI := hH
  rw [invPack_eq hn hnw hidn ht1 ht2 hY hW hH]
  exact h

end CFSG.KC.W4E

end
