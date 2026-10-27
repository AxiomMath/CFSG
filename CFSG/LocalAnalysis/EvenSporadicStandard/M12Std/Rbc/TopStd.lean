module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NoM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.GLevel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpRankTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.EvenCoverStd

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

section Order

theorem Out.card_centralizer (hO : Out G L t) :
    Nat.card (centralizer ({t} : Set G)) = 380160 := by
  rw [PropA.card_centralizer_singleton hO.std hO.m12 hO.mem hO.inv hO.outer,
    PropA.card_of_isSporadic_m12 hO.m12]

section Exclusion

theorem Out.false_of_noM12List
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hO : Out G L t) (hG : NoM12List G) : False := by
  haveI : IsSimpleGroup G := hO.std.simple
  exact false_of_m12Comp hMcard hO.std.nonabelian hO.inv hO.isCompIn hO.m12
    hO.card_centralizer hG

section Top

theorem stdHyp_of_top
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hP2 : CITPart2) (hO : Out G L t) {X : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hX : IsCompIn X (centralizer ({z} : Set G))) (hXs : StdBare X) : StdHyp G X := by
  haveI : IsSimpleGroup G := hO.std.simple
  have hnonab : ∃ a b : G, a * b ≠ b * a := hO.std.nonabelian
  have hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G := hO.std.kProper
  have hSol : SolStd X := ⟨hXs, z, hz, hX⟩
  have hstd : CFSG.Open.standardComponentIsStandard X :=
    standardComponentIsStandard_of_solStd hSol hX.isQuasisimple
  have hno : ¬ NoM12List G := fun hG => hO.false_of_noM12List hMcard hG
  have hr1 : CFSG.Open.pRank 2 (centralizer (X : Set G)) ≤ 1 := by
    by_contra hr
    exact hno (noM12List_of_rankTwoStdRec
      (HSStd.Zassenhaus.Outer.rankTwoStdRec_proved G hnonab hkp X hstd (by omega)))
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (X : Set G))) := inferInstance
  refine ⟨hO.std.simple, hnonab, hkp, hstd, hO.std.oddCore, ⟨S, ?_⟩,
    isPGroup_center_of_balance hSol hz hX (hO.std.oddCore z hz)⟩
  rcases Hyp.isCyclic_or_genQuaternion_of_pRank_le_one S.isPGroup'
      (HSStd.Zassenhaus.Outer.pRank_sylow_le_one_of_le_one hr1 S) with hc | hq
  · exact hc
  · exfalso
    have hord : ¬ Nat.card ↥(⊤ : Subgroup G) ∣ 95040 :=
      not_card_dvd_95040_of_le_of_lt (le_top : centralizer ({t} : Set G) ≤ ⊤)
        (by rw [hO.card_centralizer]; norm_num)
    obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ :=
      sol78Thm24_1Use_of_citPart2 hP2 G ⊤ hO.std.fStarSimple hord X hSol ⟨S, hq⟩
    exact hno (Or.inr (Or.inl ⟨τ, n, p, f, hp, hp2, hadm, hm.of_mulEquiv Subgroup.topEquiv⟩))

theorem InCG.stdHyp_top
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hP2 : CITPart2) (hO : Out G L t) {n : ℕ} {U T : ℕ → Subgroup G} {s : ℕ → G}
    (hC : InCG G n U T s) : StdHyp G (U (n - 1)) := by
  obtain ⟨hs2, hc⟩ := hC.top_isCompIn hO.std.simple hO.std.nonabelian
  exact stdHyp_of_top hMcard hP2 hO hs2 hc hC.top

end Top

end Exclusion

end Order

end CFSG.EvenSporadicStandard.M12Std.Rbc
