module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporFi22
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporFive
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)

macro "kd264_sq_list" : tactic =>
  `(tactic| (
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderJ3,
      CFSG.Open.orderJ4, CFSG.Open.orderRu, CFSG.Open.orderON, CFSG.Open.orderCo1,
      CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh, CFSG.Open.orderBabyMonster]
    norm_num only
    simp only [Nat.primeFactorsList_ofNat]
    decide +kernel))

theorem kd264SporAt_of_carrier
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable) {s : TauCeti.SporadicName}
    (hfs : Finite (Carrier s) ∧ IsSimpleGroup (Carrier s)) (h2 : 2 ∣ sporOrd s) (h2' : sporOrd s ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrow : ¬ k2Spor p s → ¬ (p = 3 ∧ (s = .M12 ∨ s = .M22)) → p ^ 2 ∣ sporOrd s →
      KD264RowData p (Carrier s)) :
    KD264SporAt p s := by
  obtain ⟨hfin, hs⟩ := hfs
  have b : Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group := (hbr s).some
  have hcard : Nat.card (Carrier s) = sporOrd s := (Nat.card_congr b.toEquiv).trans (hOrd s)
  have hnp : ¬ (Nat.card (Carrier s)).Prime := by
    rw [hcard]
    intro hpr
    rcases hpr.eq_one_or_self_of_dvd 2 h2 with h | h
    · omega
    · exact h2' h.symm
  have hnc := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_not_comm_of_simple_not_prime hnp
  exact kd264SporAt_of_model hOut hp hp2 hnc b fun hk2 hk3 hsq => hrow hk2 hk3 (hcard ▸ hsq)

theorem kd264SporAt_of_list
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable) {s : TauCeti.SporadicName}
    (hfs : Finite (Carrier s) ∧ IsSimpleGroup (Carrier s)) (h2 : 2 ∣ sporOrd s) (h2' : sporOrd s ≠ 2)
    (h0 : sporOrd s ≠ 0) (L : List ℕ)
    (hL : ∀ q ∈ (sporOrd s).primeFactorsList.filter (fun q => q ^ 2 ∣ sporOrd s), q ∈ L)
    (hres : ∀ p ∈ L, p.Prime → p ≠ 2 → ¬ k2Spor p s → ¬ (p = 3 ∧ (s = .M12 ∨ s = .M22)) →
      KD264SporAt p s) :
    ∀ p, p.Prime → p ≠ 2 → KD264SporAt p s := by
  intro p hp hp2
  by_cases hpL : p ∈ L ∧ ¬ k2Spor p s ∧ ¬ (p = 3 ∧ (s = .M12 ∨ s = .M22))
  · exact hres p hpL.1 hp hp2 hpL.2.1 hpL.2.2
  · refine kd264SporAt_of_carrier hOut hbr hOrd hfs h2 h2' hp hp2 fun hk2 hk3 hsq => ?_
    exact absurd ⟨hL p (prime_sq_dvd_mem hp h0 hsq), hk2, hk3⟩ hpL

@[expose] def KD264SporResidual : Prop :=
  (∀ p, p.Prime → p ≠ 2 → KD264SporAt p .M) ∧ KD264SporAt 7 .B ∧
    KD264SporAt 3 .Co1 ∧ KD264SporAt 5 .Co1 ∧ KD264SporAt 7 .Co1 ∧ KD264SporAt 3 .HN ∧
    KD264SporAt 7 .Th ∧ KD264SporAt 3 .M23 ∧ KD264SporAt 3 .HS ∧
    KD264SporAt 3 .M24 ∧ KD264SporAt 3 .J4 ∧ KD264SporAt 3 .Ru ∧
    KD264RowData 3 ↥CFSG.Sporadic.Schreier.j2P ∧ KD264RowData 3 ↥CFSG.Sporadic.HeldB.heP


theorem kd264SporS_of_residual
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : SporadicOrdersTable)
    (hsimple : ∀ s : TauCeti.SporadicName, s ≠ .M → Finite (Carrier s) ∧ IsSimpleGroup (Carrier s))
    (hres : KD264SporResidual) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264SporS p := by
  obtain ⟨hM, hB7, hCo13, hCo15, hCo17, hHN3, hTh7, hM233, hHS3, hM243, hJ43, hRu3, hJ23, hHe3⟩ :=
    hres
  have h2 : ∀ s : TauCeti.SporadicName, 2 ∣ sporOrd s ∧ sporOrd s ≠ 2 ∧ sporOrd s ≠ 0 := by
    intro s
    cases s <;> (simp only [sporOrd, CFSG.Open.orderJ3, CFSG.Open.orderJ4, CFSG.Open.orderRu,
      CFSG.Open.orderON, CFSG.Open.orderCo1, CFSG.Open.orderHN, CFSG.Open.orderLy, CFSG.Open.orderTh,
      CFSG.Open.orderBabyMonster, CFSG.Open.orderMonster, CFSG.Open.orderFi23,
      CFSG.Open.orderFi24Prime]; norm_num)
  refine kd264SporS_of_at fun s => ?_
  cases s with
  | M => exact hM p hp hp2
  | Fi24Prime => exact CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.kd264SporAt_Fi24 hOut hbr hp hp2
  | Fi23 =>
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.kd264SporAt_Fi23 hOut hbr hp hp2
  | Fi22 => exact CFSG.RankThree.Native.kd264SporAt_Fi22 hOut hbr hp hp2
  | Suz => exact CFSG.RankThree.Native.kd264SporAt_Suz hOut hbr hp hp2
  | Co2 => exact CFSG.RankThree.Native.kd264SporAt_Co2 hOut hbr hp hp2
  | Co3 => exact CFSG.RankThree.Native.kd264SporAt_Co3 hOut hbr hp hp2
  | J2 => exact CFSG.RankThree.PartOne.kd264SporAt_J2 hOut hbr hJ23 hp hp2
  | He => exact CFSG.RankThree.PartOne.kd264SporAt_He hOut hbr hHe3 hp hp2
  | M11 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .M11 (by decide)) (h2 .M11).1 (h2 .M11).2.1
      (h2 .M11).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
  | M12 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .M12 (by decide)) (h2 .M12).1 (h2 .M12).2.1
      (h2 .M12).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact absurd ⟨rfl, by decide⟩ hk3
  | M22 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .M22 (by decide)) (h2 .M22).1 (h2 .M22).2.1
      (h2 .M22).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact absurd ⟨rfl, by decide⟩ hk3
  | M23 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .M23 (by decide)) (h2 .M23).1 (h2 .M23).2.1
      (h2 .M23).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact hM233
  | M24 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .M24 (by decide)) (h2 .M24).1 (h2 .M24).2.1
      (h2 .M24).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact hM243
  | J1 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .J1 (by decide)) (h2 .J1).1 (h2 .J1).2.1
      (h2 .J1).2.2 [2] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq; exact absurd rfl hq2
  | J3 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .J3 (by decide)) (h2 .J3).1 (h2 .J3).2.1
      (h2 .J3).2.2 [2, 3] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
  | J4 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .J4 (by decide)) (h2 .J4).1 (h2 .J4).2.1
      (h2 .J4).2.2 [2, 3, 11] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact hJ43
    · exact absurd (by simp [k2Spor]) hk2
  | HS =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .HS (by decide)) (h2 .HS).1 (h2 .HS).2.1
      (h2 .HS).2.2 [2, 3, 5] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact hHS3
    · exact absurd (by simp [k2Spor]) hk2
  | McL =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .McL (by decide)) (h2 .McL).1 (h2 .McL).2.1
      (h2 .McL).2.2 [2, 3, 5] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
    · exact absurd (by simp [k2Spor]) hk2
  | Ru =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .Ru (by decide)) (h2 .Ru).1 (h2 .Ru).2.1
      (h2 .Ru).2.2 [2, 3, 5] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact hRu3
    · exact absurd (by simp [k2Spor]) hk2
  | ONan =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .ONan (by decide)) (h2 .ONan).1 (h2 .ONan).2.1
      (h2 .ONan).2.2 [2, 3, 7] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
    · exact absurd (by simp [k2Spor]) hk2
  | Co1 =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .Co1 (by decide)) (h2 .Co1).1 (h2 .Co1).2.1
      (h2 .Co1).2.2 [2, 3, 5, 7] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact hCo13
    · exact hCo15
    · exact hCo17
  | HN =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .HN (by decide)) (h2 .HN).1 (h2 .HN).2.1
      (h2 .HN).2.2 [2, 3, 5] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact hHN3
    · exact absurd (by simp [k2Spor]) hk2
  | Ly =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .Ly (by decide)) (h2 .Ly).1 (h2 .Ly).2.1
      (h2 .Ly).2.2 [2, 3, 5] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
    · exact absurd (by simp [k2Spor]) hk2
  | Th =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .Th (by decide)) (h2 .Th).1 (h2 .Th).2.1
      (h2 .Th).2.2 [2, 3, 5, 7] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
    · exact absurd (by simp [k2Spor]) hk2
    · exact hTh7
  | B =>
    refine kd264SporAt_of_list hOut hbr hOrd (hsimple .B (by decide)) (h2 .B).1 (h2 .B).2.1
      (h2 .B).2.2 [2, 3, 5, 7] (by kd264_sq_list)
      (fun q hq _ hq2 hk2 hk3 => ?_) p hp hp2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact absurd (by simp [k2Spor]) hk2
    · exact absurd (by simp [k2Spor]) hk2
    · exact hB7

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
