module

public import Certificates.Data.Kernel.W4Row.InvPackK
public import Certificates.Data.W4RowRuE25
public import CFSG.Certificates.Kernel.W4Row.EPackKSound
public import CFSG.Certificates.Kernel.CF23L34.SlpSound

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

@[expose] noncomputable def e25LinesK (p m : ℕ) (cs : List (ℕ × ℕ)) : Bool :=
  allN p (fun a => allN p (fun b => (a == 0 && b == 0) ||
    allN m (fun k => k == 0 ||
      allN p (fun j => !((e25Step p cs)^[k] (a, b) == (j * a % p, j * b % p))))))

theorem e25Lines_eq (p m : ℕ) (cs : List (ℕ × ℕ)) : e25Lines p m cs = e25LinesK p m cs := by
  unfold e25Lines e25LinesK
  refine allLt_allN fun a _ => allLt_allN fun b _ => ?_
  congr 1
  refine allLt_allN fun k _ => ?_
  congr 1
  exact allLt_allN fun j _ => rfl

theorem invPack_eq (hn : n < 2 ^ 32) (hnw : n ≤ 2 ^ w) {idn : ℕ} (hid : RS n w idn 1)
    {τ y v h : PArr} {T TI Y YI W WI H HI : ℕ} (ht1 : RR n w τ.1 T) (ht2 : RR n w τ.2 TI)
    (hy : PrP n w y Y YI) (hv : PrP n w v W WI) (hh : PrP n w h H HI) (p m : ℕ)
    (cs : List (ℕ × ℕ)) :
    invPackCheck n p m τ y v h cs =
      (invPackK n w idn p T TI Y YI W WI H HI cs && e25Lines p m cs) := by
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

theorem rep_unique {a : Array ℕ} {g h : Equiv.Perm (Fin n)} (hg : Rep n a g) (hh : Rep n a h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prp_transfer {r r' : PArr} {A AI : ℕ} {g : Equiv.Perm (Fin n)} (h : PrP n w r A AI)
    (hr : PRep n r g) (hr' : PRep n r' g) : PrP n w r' A AI := by
  obtain ⟨g', h1, h2, h3⟩ := h
  obtain rfl := rep_unique h1.1 hr.1
  exact ⟨g', hr', h2, h3⟩

theorem pWord_rep {gens : List PArr} {R : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (PRep n) gens R) :
    ∀ wd : List ℤ, PRep n (pWord n gens wd) ((wd.map (CFSG.KC.CF23L34.gLetter R)).prod)
  | [] => pRep_id
  | z :: wd => by
    rw [pWord, List.map_cons, List.prod_cons]
    exact (CFSG.KC.CF23L34.pLetter_rel h z).mul (pWord_rep h wd)

theorem exists_rep_list {regs : List PArr} {Ps : List (ℕ × ℕ)} (h : RelP n w regs Ps) :
    ∃ R : List (Equiv.Perm (Fin n)), List.Forall₂ (PRep n) regs R ∧ R.length = regs.length := by
  unfold RelP at h
  induction h with
  | nil => exact ⟨[], .nil, rfl⟩
  | cons h _ ih =>
    obtain ⟨g, hg, -⟩ := h
    obtain ⟨R, hR, hl⟩ := ih
    exact ⟨g :: R, .cons hg hR, by simp [hl]⟩

theorem relP_gens {G GI : List ℕ}
    (hz : ∀ p ∈ G.zip GI, permOK n w (mask w) (n * w) p.1 p.2 = true) :
    RelP n w (unpackP n w G GI) (G.zip GI) := by
  unfold RelP unpackP
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun p hp => prp_of_permOK (hz p hp)

theorem invSlp_of {p m : ℕ} {G GI : List ℕ} {T TI : ℕ} {prog : List (ℤ × ℤ)} {ky kw kh f : ℕ}
    {wy ww wh : List ℤ} {cs : List (ℕ × ℕ)} {τ : PArr} (ht1 : RR n w τ.1 T) (ht2 : RR n w τ.2 TI)
    (hG : G.length = 2)
    (hwf : ∀ k (hk : k < prog.length), (prog[k].1).natAbs ≤ k + 2 ∧ (prog[k].2).natAbs ≤ k + 2)
    (hy : CFSG.KC.CF23L34.slpX prog [] f ((ky + 1 : ℕ) : ℤ) = wy)
    (hw : CFSG.KC.CF23L34.slpX prog [] f ((kw + 1 : ℕ) : ℤ) = ww)
    (hh : CFSG.KC.CF23L34.slpX prog [] f ((kh + 1 : ℕ) : ℤ) = wh)
    (hby : ∀ z ∈ wy, z.natAbs ≤ 2) (hbw : ∀ z ∈ ww, z.natAbs ≤ 2) (hbh : ∀ z ∈ wh, z.natAbs ≤ 2)
    (h : invSlpK n w p G GI T TI prog ky kw kh cs = true) (hlines : e25LinesK p m cs = true) :
    invPackCheck n p m τ (pWord n (unpackP n w G GI) wy) (pWord n (unpackP n w G GI) ww)
      (pWord n (unpackP n w G GI) wh) cs = true := by
  unfold invSlpK at h
  obtain ⟨hid, h⟩ := bAnd_true h
  obtain ⟨hg, h⟩ := bAnd_true h
  obtain ⟨hn, hnw, -⟩ := idK_facts hid
  have hidn := rs_idn hid
  obtain ⟨hl, hz⟩ := gensTc_sound G GI hg
  have hR0 := relP_gens (n := n) (w := w) hz
  have e1 : R1 (G.zip GI) = G.reverse := by
    unfold R1
    rw [List.map_fst_zip (by omega)]
  have e2 : R2 (G.zip GI) = GI.reverse := by
    unfold R2
    rw [List.map_snd_zip (by omega)]
  have e3 : (G.zip GI).length = G.length := by simp [hl]
  rw [← e1, ← e2, ← e3] at h
  obtain ⟨Ps, hR, hk⟩ := runP_sound hn hnw hidn _ prog _ _ hR0 h
  obtain ⟨R, hRr, hRl⟩ := exists_rep_list hR0
  have hpr := CFSG.KC.CF23L34.pRun_rel prog hRr
  obtain ⟨Tl, hT⟩ := CFSG.KC.CF23L34.gRun_append R prog
  have hR2 : R.length = 2 := by
    rw [hRl]
    simp [unpackP, ← hl, hG]
  have key : ∀ (k : ℕ) (wd : List ℤ), CFSG.KC.CF23L34.slpX prog [] f ((k + 1 : ℕ) : ℤ) = wd →
      (∀ z ∈ wd, z.natAbs ≤ 2) →
      PrP n w (pWord n (unpackP n w G GI) wd) (regTc (pidn n w) (R1 Ps) Ps.length k)
        (regTc (pidn n w) (R2 Ps) Ps.length k) := by
    intro k wd hx hb
    have h1 := relP_getD hR hidn k
    rw [← pLetter_pos] at h1
    refine prp_transfer h1 (CFSG.KC.CF23L34.pLetter_rel hpr _) ?_
    have hs := CFSG.KC.CF23L34.slpX_prod (keep := [])
      (L := CFSG.KC.CF23L34.gLetter (CFSG.KC.CF23L34.gRun R prog))
      (CFSG.KC.CF23L34.gLetter_neg _) (CFSG.KC.CF23L34.gLetter_zero _)
      (CFSG.KC.CF23L34.gRun_reg prog R hR2 hwf) f ((k + 1 : ℕ) : ℤ)
    rw [hx] at hs
    have e : (wd.map (CFSG.KC.CF23L34.gLetter R)).prod =
        CFSG.KC.CF23L34.gLetter (CFSG.KC.CF23L34.gRun R prog) (Int.ofNat (k + 1)) := by
      rw [Int.ofNat_eq_natCast, ← hs]
      congr 1
      refine List.map_congr_left fun z hz => ?_
      rw [hT]
      exact (CFSG.KC.CF23L34.gLetter_append R Tl (by rw [hR2]; exact hb z hz)).symm
    rw [← e]
    exact pWord_rep hRr wd
  rw [invPack_eq hn hnw hidn ht1 ht2 (key ky wy hy hby) (key kw ww hw hbw) (key kh wh hh hbh), hk,
    e25Lines_eq, hlines]
  rfl

theorem runP_append (n w idn : ℕ) (p1 p2 : List (ℤ × ℤ)) (k : List ℕ → List ℕ → ℕ → Bool) :
    runP n w idn (p1 ++ p2) k = runP n w idn p1 (runP n w idn p2 k) := by
  induction p1 with
  | nil => rfl
  | cons pq p1 ih =>
    funext r1 r2 len
    rw [List.cons_append, runP_cons, runP_cons, ih]

theorem letRP_out (idn : ℕ) (r1 r2 : List ℕ) (len : ℕ) (z : ℤ) :
    ∃ ab : ℕ × ℕ, ∀ f : ℕ → ℕ → Bool, letRP idn r1 r2 len z f = f ab.1 ab.2 := by
  rcases z with (_ | j) | j
  · exact ⟨(idn, idn), fun f => letRP_eq_zero idn r1 r2 len f⟩
  · exact ⟨(regTc idn r1 len j, regTc idn r2 len j), fun f => letRP_eq_pos idn r1 r2 len j f⟩
  · exact ⟨(regTc idn r2 len j, regTc idn r1 len j), fun f => letRP_eq_neg idn r1 r2 len j f⟩

theorem runP_out (n w idn : ℕ) : ∀ (p : List (ℤ × ℤ)) (r1 r2 : List ℕ) (len : ℕ),
    ∃ s : List ℕ × List ℕ × ℕ, ∀ k, runP n w idn p k r1 r2 len = k s.1 s.2.1 s.2.2
  | [], r1, r2, len => ⟨(r1, r2, len), fun _ => rfl⟩
  | pq :: p, r1, r2, len => by
    obtain ⟨⟨A, AI⟩, hA⟩ := letRP_out idn r1 r2 len pq.1
    obtain ⟨⟨B, BI⟩, hB⟩ := letRP_out idn r1 r2 len pq.2
    obtain ⟨s, hs⟩ := runP_out n w idn p (pcomp n w (mask w) A B :: r1)
      (pcomp n w (mask w) BI AI :: r2) (len + 1)
    refine ⟨s, fun k => ?_⟩
    rw [runP_cons, hA]
    dsimp only
    rw [hB]
    dsimp only
    rw [sB, sB]
    exact hs k

theorem runP_ckpt {n w idn : ℕ} {p : List (ℤ × ℤ)} {r1 r2 S1 S2 : List ℕ} {len L : ℕ}
    (h : runP n w idn p (fun a b c => (a == S1 && b == S2) && Nat.beq c L) r1 r2 len = true)
    (k : List ℕ → List ℕ → ℕ → Bool) : runP n w idn p k r1 r2 len = k S1 S2 L := by
  obtain ⟨s, hs⟩ := runP_out n w idn p r1 r2 len
  rw [hs] at h
  rw [hs]
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  rw [h1, h2, h3]

end CFSG.KC.W4E

end
