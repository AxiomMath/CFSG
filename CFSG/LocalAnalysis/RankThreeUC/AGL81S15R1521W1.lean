module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PF
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PK
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PL

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open KFactsSmall
open scoped commutatorElement

section CaseTable

variable {X : Type} [Group X] [Finite X]

theorem case_table_1521_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (h15 : Shape1515 L)
    (h20 : CFSG.Open.pRank 3 L < 3) : Case21 T L :=
  case_table_1521_aux_gen hT hKSMAlt hKSMOdd hKSMU4 hl
    (fun hne hL3 hk => isLThreeTwoProd_gnImg_gen hKSML3 hl hne hL3 hk) h15 h20

end CaseTable

section SigmaM

variable {X : Type} [Group X] [Finite X]

theorem dvd_card_normalClosure_of_mem_sigmaM_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hne : L ≠ Subgroup.normalClosure (L : Set ↥M))
    (hsh : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M))) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧
        Set.ncard {L' : Subgroup ↥M | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set ↥M)} ≤ 3))
    {p : ℕ} (hp : p ∈ sigmaM G M) : p ∣ Nat.card (Subgroup.normalClosure (L : Set ↥M)) :=
  dvd_card_normalClosure_of_mem_sigmaM_aux_gen hO1217 hO1521 ctx h11 h21 hLs hL hne
    (exists_E9_of_ne_gen (hR.liftCtxGen ctx.gn ctx.good hLs hL) hne hsh) hp
    (fun hpJ => exists_centralizing_pGroup_gen hR.1 h20 hLs hL hp hpJ (hsh.imp id And.left))

theorem sigmaM_eq_five_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hne : L ≠ Subgroup.normalClosure (L : Set ↥M))
    (hcp : IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set ↥M)))) :
    sigmaM G M = {5} :=
  sigmaM_eq_five_aux_gen ctx h11 hcp fun _ hp =>
    dvd_card_normalClosure_of_mem_sigmaM_gen hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hne
      (Or.inl hcp) hp

theorem sigmaM_eq_seven_gen {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    (hne : L ≠ Subgroup.normalClosure (L : Set ↥M)) (hL3 : IsLThreeOfExp 1 ↥(barO2 L))
    (hk : Set.ncard {L' : Subgroup ↥M | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set ↥M)} ≤ 3) :
    sigmaM G M = {7} :=
  sigmaM_eq_seven_aux_gen ctx h11 hL.1 hL3 fun _ hp =>
    dvd_card_normalClosure_of_mem_sigmaM_gen hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hne
      (Or.inr ⟨hL3, hk⟩) hp

end SigmaM

end CFSG.LocalAnalysis.RankThreeUC.S15
