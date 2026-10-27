module

public import Certificates.Data.Kernel.Q8Wit
public import Certificates.Data.TwinPerpSmSp1Wit
public import CFSG.Certificates.Kernel.E81KSound

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.E81K
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (Q16Data qGens qCert)
open Certificates.TwinPerpSmSp1
open CFSG.Monster.B.Co2 (allLt_iff)

variable {n w : ℕ}

@[expose] def Fp (n w p : ℕ) : Prop := PP n w p

theorem Fp.mul {p q : ℕ} (hp : Fp n w p) (hq : Fp n w q) : Fp n w (pcomp n w (mask w) p q) :=
  PP.mul hp hq

theorem Fp.inv {p : ℕ} (hp : Fp n w p) : Fp n w (pinvS n w (mask w) p) := PP.inv hp

theorem compA_F {p q : ℕ} (hp : Fp n w p) (hq : Fp n w q) :
    compA n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  compA_PP hp hq

theorem invCand_F {p : ℕ} (hp : Fp n w p) :
    invCand n (unpack n w p) = unpack n w (pinvS n w (mask w) p) :=
  invCand_PP hp

theorem eqA_F {p q : ℕ} (hp : Fp n w p) (hq : Fp n w q) :
    eqA n (unpack n w p) (unpack n w q) = Nat.beq p q :=
  eqA_PP hp hq

theorem allLt_eq (m : ℕ) (f : ℕ → Bool) : allLt m f = (List.range m).all f := by
  apply Bool.eq_iff_iff.2
  rw [allLt_iff, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.1 hi), fun h i hi => h i (List.mem_range.2 hi)⟩

theorem q8Elt_F {x y : ℕ} (hx : Fp n w x) (hy : Fp n w y) (j : ℕ) :
    q8Elt n (unpack n w x) (unpack n w y) j =
        unpack n w (q8EltK n w x y (pcomp n w (mask w) x x) j) ∧
      Fp n w (q8EltK n w x y (pcomp n w (mask w) x x) j) := by
  have hsz : szOK n w = true := PP.sz hx
  have hs : Fp n w (pcomp n w (mask w) x x) := hx.mul hx
  match j with
  | 0 => exact ⟨idA_eq hsz, PP.id hsz⟩
  | 1 => exact ⟨rfl, hx⟩
  | 2 => exact ⟨compA_F hx hx, hs⟩
  | 3 => exact ⟨by rw [q8Elt, compA_F hx hx, compA_F hs hx]; rfl, hs.mul hx⟩
  | 4 => exact ⟨rfl, hy⟩
  | 5 => exact ⟨by rw [q8Elt, compA_F hy hx]; rfl, hy.mul hx⟩
  | 6 => exact ⟨by rw [q8Elt, compA_F hx hx, compA_F hy hs]; rfl, hy.mul hs⟩
  | 7 => exact ⟨by rw [q8Elt, compA_F hx hx, compA_F hs hx, compA_F hy (hs.mul hx)] <;>
      first | rfl | omega, hy.mul (hs.mul hx)⟩
  | j + 8 =>
    refine ⟨?_, hy.mul (hs.mul hx)⟩
    have hb : ∀ m, m < 8 → Nat.beq (j + 8) m = false := fun m hm =>
      Bool.eq_false_iff.2 fun h => by
        have := Nat.eq_of_beq_eq_true h
        omega
    have e : q8EltK n w x y (pcomp n w (mask w) x x) (j + 8) =
        pcomp n w (mask w) y (pcomp n w (mask w) (pcomp n w (mask w) x x) x) := by
      simp only [q8EltK, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
        hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), cond_false]
    rw [e, q8Elt, compA_F hx hx, compA_F hs hx, compA_F hy (hs.mul hx)] <;> omega

theorem wit4_eq {x y c : ℕ} (hx : Fp n w x) (hy : Fp n w y) (hc : Fp n w c) :
    wit4 n (unpack n w x) (unpack n w y) (unpack n w c) =
      wit4K n w x y (pcomp n w (mask w) x x) c (pinvS n w (mask w) c) := by
  unfold wit4 wit4K Certificates.TwinPerpSmSp1.commA commK outsideA outsideK
  simp (maxDischargeDepth := 12) only [compA_F, invCand_F, eqA_F, Fp.mul, Fp.inv, hx, hy, hc,
    fun j => (q8Elt_F hx hy j).1, fun j => (q8Elt_F hx hy j).2, allLt_eq, allNP_eq]

theorem wit5_eq {x y g : ℕ} (hx : Fp n w x) (hy : Fp n w y) (hg : Fp n w g) :
    wit5 n (unpack n w x) (unpack n w y) (unpack n w g) =
      wit5K n w x y (pcomp n w (mask w) x x) g (pinvS n w (mask w) g) := by
  unfold wit5 wit5K Certificates.TwinPerpSmSp1.commA commK outsideA outsideK
  simp (maxDischargeDepth := 12) only [compA_F, invCand_F, eqA_F, Fp.mul, Fp.inv, hx, hy, hg,
    fun j => (q8Elt_F hx hy j).1, fun j => (q8Elt_F hx hy j).2, allLt_eq, allNP_eq, anyNP_eq]

theorem q8WitFree_of {N nc : ℕ} {T SQ I C CI : ℕ → ℕ} {pts cs : Array (Array ℕ)}
    (hsz : szOK n w = true) (hps : pts.size = N) (hpt : ∀ i < N, pts[i]! = unpack n w (T i))
    (hpT : ∀ i < N, Fp n w (T i)) (hcs : cs.size = nc)
    (hct : ∀ k < nc, cs[k]! = unpack n w (C k)) (hcC : ∀ k < nc, Fp n w (C k))
    (htabs : tabsK n w N T SQ I = true) (hinv : invsK n w nc C CI = true)
    (h : q8WitFreeK n w N T SQ I nc C CI = true) :
    q8WitFree n pts (pts.map fun y => compA n y y) cs = true := by
  have ht : ∀ i < N, SQ i = pcomp n w (mask w) (T i) (T i) ∧ I i = pinvS n w (mask w) (T i) :=
    fun i hi => by
      have e := allNP_iff.1 htabs i hi
      simp only [Bool.and_eq_true] at e
      exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩
  have hci : ∀ k < nc, CI k = pinvS n w (mask w) (C k) := fun k hk =>
    Nat.eq_of_beq_eq_true (allNP_iff.1 hinv k hk)
  have hid : idA n = unpack n w (pidn n w) := idA_eq hsz
  have hF1 : Fp n w (pidn n w) := PP.id hsz
  have hsq : ∀ i < N, (pts.map fun y => compA n y y)[i]! = unpack n w (SQ i) := fun i hi => by
    rw [getMap pts _ (by rw [hps]; exact hi), hpt i hi, compA_F (hpT i hi) (hpT i hi), (ht i hi).1]
  have hFs : ∀ i < N, Fp n w (SQ i) := fun i hi => by
    rw [(ht i hi).1]
    exact (hpT i hi).mul (hpT i hi)
  unfold q8WitFree
  rw [allLt_iff, hps]
  intro i hi
  have hi' := allNP_iff.1 h i hi
  rw [hsq i hi, hid, eqA_F (hFs i hi) hF1, compA_F (hFs i hi) (hFs i hi),
    eqA_F ((hFs i hi).mul (hFs i hi)) hF1]
  simp only [Bool.or_eq_true] at hi' ⊢
  rcases hi' with hi' | hi'
  · exact Or.inl hi'
  right
  rw [allLt_iff]
  intro j hj
  have hj' := allNP_iff.1 hi' j hj
  rw [hsq j hj, eqA_F (hFs j hj) (hFs i hi), hpt j hj, hpt i hi,
    invCand_F (hpT i hi), compA_F (hpT j hj) (hpT i hi),
    compA_F (hpT i hi).inv (hpT j hj),
    eqA_F ((hpT j hj).mul (hpT i hi)) ((hpT i hi).inv.mul (hpT j hj)), ← (ht i hi).2]
  simp only [Bool.or_eq_true] at hj' ⊢
  rcases hj' with hj' | hj'
  · exact Or.inl hj'
  right
  rw [anyNP_eq, List.any_eq_true] at hj'
  obtain ⟨k, hk, hk'⟩ := hj'
  have hk1 : k < nc := List.mem_range.1 hk
  rw [Array.any_eq_true]
  refine ⟨k, by rw [hcs]; exact hk1, ?_⟩
  have e : cs[k] = unpack n w (C k) := by
    rw [← getElem!_pos cs k (by rw [hcs]; exact hk1)]
    exact hct k hk1
  rw [e, wit4_eq (hpT i hi) (hpT j hj) (hcC k hk1), wit5_eq (hpT i hi) (hpT j hj) (hcC k hk1),
    ← (ht i hi).1, ← hci k hk1]
  exact hk'

theorem q8WitCheck_of_pins (D : Q8WitData) (hn : D.syl.n = n) (hw : szOK n w = true) {mp : ℕ}
    (PG : ℕ → ℕ) (hpg : D.syl.pg.size = mp) (hpgE : ∀ j < mp, D.syl.pg[j]! = unpack n w (PG j))
    (hpgP : ∀ j < mp, permB n w (PG j) = true)
    (hkeys : D.syl.qKeys.all (fun p => decide (p < n)) = true)
    (hlq : (D.syl.qW.toList.all fun wd => wd.all fun l => decide (l < mp)) = true)
    (Q : Pin n w D.syl.qKeys)
    (hwQ : D.syl.qW.toList.map (posWordK n w PG) = (List.range Q.ng).map Q.G)
    (hQN : D.syl.qOrd = Q.N) (hQf : Q.N ≤ D.syl.qFuel) {mx : ℕ} (XG : ℕ → ℕ)
    (hxg : D.xg.size = mx) (hxgE : ∀ j < mx, D.xg[j]! = unpack n w (XG j))
    (hxgP : ∀ j < mx, permB n w (XG j) = true)
    (hlc : (D.cW.toList.all fun wd => wd.all fun l => decide (l < mx)) = true) {nc : ℕ}
    (C : ℕ → ℕ) (hwC : D.cW.toList.map (posWordK n w XG) = (List.range nc).map C)
    (SQ I CI : ℕ → ℕ) (htabs : tabsK n w Q.N Q.T SQ I = true) (hinv : invsK n w nc C CI = true)
    (h : q8WitFreeK n w Q.N Q.T SQ I nc C CI = true) : q8WitCheck D = true := by
  have hk' := hkeys
  simp only [List.all_eq_true, decide_eq_true_eq] at hk'
  have hq := words hw hpgE hpgP hwQ hlq
  have hqE := pin_facts Q (fuel := D.syl.qFuel) hq.1 hq.2 hk' hQf
  have hc := words hw hxgE hxgP hwC hlc
  unfold q8WitCheck q8WitCheck' qCert qGens cands
  rw [hn]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, hkeys⟩, ?_⟩, hqE.2.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff, hpg]
    intro k hk
    rw [hpgE k hk]
    exact BfsPin.validA_unpack (hpgP k hk)
  · rw [← Array.all_toList, hpg]
    exact hlq
  · rw [hqE.1, Array.size_ofFn, hQN]
    exact beq_self_eq_true _
  · rw [allLt_iff, hxg]
    intro k hk
    rw [hxgE k hk]
    exact BfsPin.validA_unpack (hxgP k hk)
  · rw [← Array.all_toList, hxg]
    exact hlc
  · rw [allLt_iff, hc.1]
    intro k hk
    rw [(hc.2 k hk).1]
    exact BfsPin.validA_unpack (hc.2 k hk).2
  · rw [hqE.1]
    refine q8WitFree_of hw (by rw [Array.size_ofFn]) (fun i hi => ?_)
      (fun i hi => pp_of_permB hw (hqE.2.2 i hi).2) hc.1 (fun k hk => (hc.2 k hk).1)
      (fun k hk => pp_of_permB hw (hc.2 k hk).2) htabs hinv h
    rw [← hqE.1]
    exact (hqE.2.2 i hi).1

end CFSG.KC.Q8Wit

end
