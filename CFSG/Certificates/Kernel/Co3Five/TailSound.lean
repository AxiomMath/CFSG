module

public import CFSG.Certificates.Kernel.Misc.PermWitSound
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.RankThree.Native.ChainCentralizer
public import Certificates.Data.Kernel.Misc.ChainTail

public section

namespace CFSG.KC.Misc.ChainTail

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.RankThree.Native
open CFSG.KC.BfsPin (PP)

variable {n w kS nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {S : Array (Array ℕ)} {base : Array ℕ}

theorem tailOK_of_ptailK (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hsz : szOK n w = true) {x : Array ℕ} {X : ℕ}
    (hx : x = unpack n w X) (hX : permB n w X = true) (XP : ℕ → ℕ) {E : List (Array ℕ)}
    {NE : ℕ} {EP : ℕ → ℕ} (hE : E = (List.range NE).map fun e => unpack n w (EP e))
    (hEp : ∀ e < NE, permB n w (EP e) = true) :
    ∀ fuel i, i + fuel = nb → ∀ (acc : Array ℕ) (ACC : ℕ), PP n w ACC → Ag n w acc ACC →
      ptailK n w LR TR BP X XP [] NE EP fuel i ACC = true →
      tailOK n (rawLevels n S base) x E fuel i acc = true := by
  have hn : n < 2 ^ 32 := by have := hb.2.2.1; omega
  have hbl := Orb.base_lt_of_levels hb hl
  have hXP : PP n w X := pp_of_permB hsz hX
  have hxa : Ag n w x X := by
    rw [hx]
    exact ag_unpack n w X
  have hlev : ∀ i < nb, ((rawLevels n S base)[i]!).pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), PP n w (TR (roff n (n * w) (LR i) + k)) ∧
        Ag n w (((rawLevels n S base)[i]!).tr[k]!) (TR (roff n (n * w) (LR i) + k)) := by
    intro i hi
    obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
    obtain ⟨-, -, -, -, -, hperm⟩ := Orb.levelK_facts (hl i hi)
    refine ⟨A.cnt.symm, fun k hk => ⟨pp_of_permOK hsz (hperm k hk), fun y hy => ?_⟩⟩
    have R := (A.tr k (by rw [← A.cnt]; exact hk)).1 ⟨y, hy⟩
    rw [(P k hk).1 ⟨y, hy⟩]
    exact R
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
    rw [tailOK, hc, he]
    exact hk
  | succ fuel ih =>
    intro i hif acc ACC hA hacc hk
    have hi : i < nb := by omega
    obtain ⟨hsz', hpt⟩ := hlev i hi
    have e : ptailK n w LR TR BP X XP [] NE EP (fuel + 1) i ACC = strictB (LR i) fun R =>
        allN (rcnt R) fun k => !(relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) R k)) ||
          ptailK n w LR TR BP X XP [] NE EP fuel (i + 1)
            (pcomp n w (mask w) ACC (TR (roff n (n * w) R + k))) := rfl
    rw [e, Orb.strictB_eq] at hk
    rw [tailOK, allLt_iff]
    intro k hkc
    rw [hsz'] at hkc
    obtain ⟨hp3, hp4⟩ := hpt k hkc
    have hk' := Orb.allN_iff.1 hk k hkc
    have hr : relOKK w (mask w) BP XP [] i ACC (rpt w (mask w) (LR i) k) = true := rfl
    rw [hr, Bool.not_true, Bool.false_or] at hk'
    exact ih (i + 1) (by omega) _ _ (hA.mul hp3) (ag_compA hn hacc hp4 hp3.2.1) hk'

theorem fixLevCount_eq (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {i : ℕ} (hi : i < nb) (X : ℕ) :
    fixLevCount n (rawLevels n S base) (unpack n w X) i =
      CFSG.KC.PermWit.cntK n (fun q => Nat.beq (pg w (mask w) X q) q &&
        Nat.blt (rpos w (mask w) (n * w) (LR i) q) (rcnt (LR i))) := by
  have hbl := Orb.base_lt_of_levels hb hl
  obtain ⟨A, -⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  rw [CFSG.KC.PermWit.cntK_eq, fixLevCount, fixLevList, ← List.countP_eq_length_filter,
    ← List.map_coe_finRange_eq_range, List.countP_map]
  apply List.countP_congr
  intro q _
  have hqn := q.2
  simp only [Function.comp_apply]
  rw [Orb.unpack_get hqn]
  have hpos := A.pos q hqn
  have e1 : (pg w (mask w) X q == q) = Nat.beq (pg w (mask w) X q) q := rfl
  have e2 : decide (((rawLevels n S base)[i]!).pos[(q : ℕ)]! <
      ((rawLevels n S base)[i]!).pts.size) =
      Nat.blt (rpos w (mask w) (n * w) (LR i) q) (rcnt (LR i)) := by
    apply Bool.eq_iff_iff.2
    rw [decide_eq_true_iff, Nat.blt_eq]
    exact hpos.symm
  rw [e1, e2]
