module

public import Certificates.Data.Kernel.Misc.ChainTail
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.RankThree.Native.ChainCentralizer
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.KC.BfsPin (PP)

theorem relOK_eq {n w nb BP : ℕ} {base : Array ℕ} {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    {rels : List (ℕ × ℕ × ℕ)} {i : ℕ} {acc : Array ℕ} {ACC q : ℕ}
    (hbs : ∀ t < nb, base[t]! = pg w (mask w) BP t) (hbn : ∀ t < nb, pg w (mask w) BP t < n)
    (hxs : ∀ e < xs.size, xs[e]! = unpack n w (XP e)) (hrels : ∀ r ∈ rels, r.2.2 < xs.size)
    (hi : i < nb) (hacc : Ag n w acc ACC) (hA : ∀ x < n, pg w (mask w) ACC x < n) (hq : q < n) :
    relOK base xs rels i acc q = relOKK w (mask w) BP XP rels i ACC q := by
  have himg : ∀ m ≤ i, relImg base i acc q m = relImgK w (mask w) BP ACC i q m := by
    intro m hm
    unfold relImg relImgK
    rw [Orb.nIf_eq, Orb.blt_dec]
    by_cases h : m < i
    · simp only [h, decide_true, ↓reduceIte]
      rw [hbs m (by omega), hacc _ (hbn m (by omega))]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hacc q hq
  have himgl : ∀ m ≤ i, relImgK w (mask w) BP ACC i q m < n := by
    intro m hm
    unfold relImgK
    rw [Orb.nIf_eq]
    split
    · exact hA _ (hbn m (by omega))
    · exact hA q hq
  have key : ∀ r ∈ rels, (!(decide (max r.1 r.2.1 = i)) ||
      relImg base i acc q r.2.1 == (xs[r.2.2]!)[relImg base i acc q r.1]!) =
      (!(Nat.beq (Nat.max r.1 r.2.1) i) || Nat.beq (relImgK w (mask w) BP ACC i q r.2.1)
        (pg w (mask w) (XP r.2.2) (relImgK w (mask w) BP ACC i q r.1))) := by
    intro r hr
    have hmx : Nat.max r.1 r.2.1 = max r.1 r.2.1 := rfl
    rw [hmx, Orb.beq_dec (max r.1 r.2.1) i]
    by_cases hm : max r.1 r.2.1 = i
    · have h1 : r.1 ≤ i := by omega
      have h2 : r.2.1 ≤ i := by omega
      rw [decide_eq_true hm, himg _ h1, himg _ h2, hxs _ (hrels r hr),
        Orb.unpack_get (himgl _ h1), Orb.beq_dec]
      rfl
    · rw [decide_eq_false hm]
      rfl
  unfold relOK relOKK
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact forall_congr' fun r => imp_congr_right fun hr => by rw [key r hr]

theorem ptailK_sound {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)}
    {base : Array ℕ} (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {x : Array ℕ} {X : ℕ}
    (hx : x = unpack n w X) (hX : permB n w X = true) {xs : Array (Array ℕ)} {XP : ℕ → ℕ}
    (hxs : ∀ e < xs.size, xs[e]! = unpack n w (XP e)) {rels : List (ℕ × ℕ × ℕ)}
    (hrels : ∀ r ∈ rels, r.2.2 < xs.size) {E : List (Array ℕ)} {NE : ℕ} {EP : ℕ → ℕ}
    (hE : E = (List.range NE).map fun e => unpack n w (EP e))
    (hEp : ∀ e < NE, permB n w (EP e) = true) (hnb : 0 < nb)
    (h : ∀ k < rcnt (LR 0), ptailBranchK n w LR TR BP X XP rels NE EP nb k = true) :
    ptailOK n (rawLevels n S base) base x xs rels E nb 0 (idA n) = true := by
  have hn : n < 2 ^ 32 := by have := hb.2.2.1; omega
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hw2 : n + 1 < 2 ^ w := hb.2.1
  have hsz : szOK n w = true := (Orb.levelK_facts (hl 0 hnb)).1
  have hbl := Orb.base_lt_of_levels hb hl
  have hbase : ∀ t < nb, base[t]! = pg w (mask w) BP t := hb.2.2.2.2.2.2
  have hbn : ∀ t < nb, pg w (mask w) BP t < n := fun t ht => by
    rw [← hbase t ht]
    exact hbl t ht
  have hXP : PP n w X := pp_of_permB hsz hX
  have hxa : Ag n w x X := by
    rw [hx]
    exact ag_unpack n w X
  have hlev : ∀ i < nb, ((rawLevels n S base)[i]!).pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), ((rawLevels n S base)[i]!).pts[k]! = rpt w (mask w) (LR i) k ∧
        rpt w (mask w) (LR i) k < n ∧ PP n w (TR (roff n (n * w) (LR i) + k)) ∧
        Ag n w (((rawLevels n S base)[i]!).tr[k]!) (TR (roff n (n * w) (LR i) + k)) := by
    intro i hi
    obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    obtain ⟨-, -, hR, -, -, hperm⟩ := Orb.levelK_facts (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨(A.pt k (by rw [← A.cnt]; exact hk)).symm, (hR.pt k hk).1,
      pp_of_permOK hsz (hperm k hk), fun y hy => ?_⟩⟩
    have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨y, hy⟩
    rw [(P k hk).1 ⟨y, hy⟩]
    exact R
  have key : ∀ fuel i, i + fuel = nb → ∀ (acc : Array ℕ) (ACC : ℕ), PP n w ACC →
      Ag n w acc ACC → ptailK n w LR TR BP X XP rels NE EP fuel i ACC = true →
      ptailOK n (rawLevels n S base) base x xs rels E fuel i acc = true := by
    intro fuel
    induction fuel with
    | zero =>
      intro i _ acc ACC hA hacc hk
      have hc : commA n acc x =
          Nat.beq (pcomp n w (mask w) ACC X) (pcomp n w (mask w) X ACC) :=
        eqA_ag (ag_compA hn hacc hxa hXP.2.1) (ag_compA hn hxa hacc hA.2.1) (hA.mul hXP)
          (hXP.mul hA)
      have he : E.any (eqA n acc) = CFSG.KC.LQT.P.anyN NE fun e => Nat.beq ACC (EP e) := by
        rw [hE, anyNP_eq]
        apply Bool.eq_iff_iff.2
        simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
        constructor
        · rintro ⟨e, he, h⟩
          exact ⟨e, he, by
            rwa [eqA_ag hacc (ag_unpack n w (EP e)) hA (pp_of_permB hsz (hEp e he))] at h⟩
        · rintro ⟨e, he, h⟩
          exact ⟨e, he, by
            rwa [eqA_ag hacc (ag_unpack n w (EP e)) hA (pp_of_permB hsz (hEp e he))]⟩
      rw [ptailOK, hc, he]
      exact hk
    | succ fuel ih =>
      intro i hif acc ACC hA hacc hk
      have hi : i < nb := by omega
      obtain ⟨hsz', hpt⟩ := hlev i hi
      have e : ptailK n w LR TR BP X XP rels NE EP (fuel + 1) i ACC = strictB (LR i) fun R =>
          allN (rcnt R) fun k => !(relOKK w (mask w) BP XP rels i ACC (rpt w (mask w) R k)) ||
            ptailK n w LR TR BP X XP rels NE EP fuel (i + 1)
              (pcomp n w (mask w) ACC (TR (roff n (n * w) R + k))) := rfl
      rw [e, Orb.strictB_eq] at hk
      rw [ptailOK, allLt_iff]
      intro k hkc
      rw [hsz'] at hkc
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hpt k hkc
      have hk' := Orb.allN_iff.1 hk k hkc
      rw [hp1, relOK_eq hbase hbn hxs hrels hi hacc hA.2.1 hp2]
      cases hr : relOKK w (mask w) BP XP rels i ACC (rpt w (mask w) (LR i) k)
      · rfl
      · rw [hr, Bool.not_true, Bool.false_or] at hk'
        rw [Bool.not_true, Bool.false_or]
        exact ih (i + 1) (by omega) _ _ (hA.mul hp3) (ag_compA hn hacc hp4 hp3.2.1) hk'
  obtain ⟨m, rfl⟩ : ∃ m, nb = m + 1 := ⟨nb - 1, by omega⟩
  obtain ⟨hsz0, hpt0⟩ := hlev 0 (by omega)
  have hI : PP n w (pidn n w) := CFSG.KC.BfsPin.PP.id hsz
  have hacc0 : Ag n w (idA n) (pidn n w) := fun y hy => by rw [idA_get hy, PF.pg_pidn hn24 hw2 hy]
  rw [ptailOK, allLt_iff]
  intro k hk
  rw [hsz0] at hk
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hpt0 k hk
  have hk' := h k hk
  unfold ptailBranchK at hk'
  rw [hp1, relOK_eq hbase hbn hxs hrels (by omega) hacc0 hI.2.1 hp2]
  cases hr : relOKK w (mask w) BP XP rels 0 (pidn n w) (rpt w (mask w) (LR 0) k)
  · rfl
  · rw [hr, Bool.not_true, Bool.false_or] at hk'
    rw [Bool.not_true, Bool.false_or]
    have hag : Ag n w (compA n (idA n) (((rawLevels n S base)[0]!).tr[k]!))
        (TR (roff n (n * w) (LR 0) + k)) := fun y hy => by
      rw [compA_get hy, hp4 y hy, idA_get (hp3.2.1 y hy)]
    have e : Nat.sub (m + 1) 1 = m := Nat.add_sub_cancel m 1
    rw [e] at hk'
    exact key m 1 (by omega) _ _ hp3 hag hk'

end CFSG.KC.Misc.ChainTail

end
