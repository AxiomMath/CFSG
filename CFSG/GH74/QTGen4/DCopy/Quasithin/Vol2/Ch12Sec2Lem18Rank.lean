module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18Rank
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem18Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

open Lem18R

theorem lem12218TwoRank_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h323 : Stmt3_2_3) (h1227 : Stmt12_2_7_F4) : Lem12218TwoRank_F4 := by
  classical
  intro G _ _ T L V H hH hCZ hHs E hEH hE hEC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hred, -, hO2, -⟩ := stmt12_2_7_one_F4 h331 h1222 (stmt12_2_6_of_F4 h1222 h323) hH hCZ hHs
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le T).mpr fun z hz => hz.1.1
  have hWH : VZ T H ≤ H := conjClosure_le fun h hh z hz =>
    H.mul_mem (H.mul_mem hh (hHs.1.1 (hZT hz))) (H.inv_mem hh)
  have hHW : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  have hO2' : pCoreOf 2 H ≤ Subgroup.centralizer (VZ T H : Set G) := fun x hx => (hO2 hx).2
  by_cases hsolv : Group.IsSolvable ↥H
  · obtain ⟨p, hp, hp2, hX⟩ :=
      (Lem7.minParabolic_F4 h331 hH hHs).subgroupOf.exists_odd_prime_of_solvable hsolv
    have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ 2 :=
      CFSG.SectionRank.isStronglyQuasithin_iff.mp
        (isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank hH.qtke.2.2 hHs.1.2) p hp hp2
    have hrank : ∀ S : Subgroup ↥H, IsElemAbelian p S → ∀ d, Nat.card S = p ^ d → d ≤ 2 :=
      fun S hS d hd => (CFSG.Quasithin.le_pRank hp le_top hS hd).trans hrk
    set E' := E.subgroupOf H with hE'
    have hE'c : Nat.card E' = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
    rw [← hE'c]
    refine card_le_four_of_solvable hp hp2 hX hrank (fun e he => ?_) (fun a ha b hb => ?_) ?_
    · apply Subtype.ext
      have h1 := hE.2 _ (Subgroup.mem_subgroupOf.mp he)
      push_cast
      rw [← pow_two]
      exact h1
    · apply Subtype.ext
      push_cast
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
        ⟨b, Subgroup.mem_subgroupOf.mp hb⟩)
    · rw [eq_bot_iff]
      rintro x ⟨hxE, hxO⟩
      rw [CFSG.pCore_eq_open] at hxO
      have h1 : (x : G) ∈ E ⊓ Subgroup.centralizer (VZ T H : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hxE, hO2' ⟨x, hxO, rfl⟩⟩
      rw [hEC, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  · exact card_le_four_of_L24 hWH hHW hred hO2' (Lem7.not_le_centralizer_VZ hCZ hHs)
      ((h1227 G T L V H hH hCZ hHs).2 hsolv).1 hEH hE hEC

end CFSG.Quasithin.H13
