module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2NonExtremalL34At (P : Sylow 3 G) (M T : Subgroup G) : Prop :=
  ∀ E N : Subgroup G, D2Escape 3 P M E N E → Subgroup.normalizer (T : Set G) ≤ N →
    ∀ (Ebar : Sylow 3 (N ⧸ primeComplementCore (G := N) 3))
      (K' : Subgroup (N ⧸ primeComplementCore (G := N) 3)),
      (Ebar : Subgroup _) = (E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (N ⧸ primeComplementCore (G := N) 3) Ebar
        ((E.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3)))
        (((N ⊓ M).subgroupOf N).map (QuotientGroup.mk' (primeComplementCore 3))) K' →
      ∃ d' : TauCeti.ValidLieTypeIndex, IsL34Index d' ∧
        Nonempty (K' ≃* (TauCeti.CFSGIndex.lie d').Group)

@[expose] def D2NoNonExtremalAt (P : Sylow 3 G) (M T : Subgroup G) : Prop :=
  ∀ E N : Subgroup G, D2Escape 3 P M E N E → Subgroup.normalizer (T : Set G) ≤ N → False

theorem D2NoNonExtremalAt.nonExtremalL34At {P : Sylow 3 G} {M T : Subgroup G}
    (h : D2NoNonExtremalAt P M T) : D2NonExtremalL34At P M T :=
  fun E N hesc hNT => (h E N hesc hNT).elim

theorem D2L34NonExtremalL34.nonExtremalL34At (hIV : D2L34NonExtremalL34 G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hs : Group.IsSolvable M) (h27 : Nat.card R = 27)
    {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) : D2NonExtremalL34At P M T :=
  hIV d P M A H R Rbar K ctx hs h27 T hT

structure D2L34WeakConf3 (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  l34 : IsL34Index d
  esc : D2Escape 3 P M A H R
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))
  almostSimple : D2AlmostSimple 3 (H ⧸ primeComplementCore (G := H) 3) Rbar
    ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) K
  iso : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)
  le_K : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K

theorem D2L34BetaConf3.toWeak {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    D2L34WeakConf3 d P M A H R Rbar K :=
  ⟨hc.l34, hc.esc, hc.rbar, hc.almostSimple, hc.iso, hc.le_K⟩

theorem D2L34BetaConf3.card_le_27 {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (h27 : Nat.card R = 27) :
    ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → Nat.card R' ≤ 27 :=
  fun A' H' R' h => h27 ▸ hc.max A' H' R' h

structure D2L34R27 (G : Type) [Group G] [Finite G] (d : TauCeti.ValidLieTypeIndex)
    (P : Sylow 3 G) (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (T : Subgroup G) : Prop where
  ctx : D2L34SideCtx3 G d P M A H R Rbar K
  solvable : Group.IsSolvable M
  card_R : Nat.card R = 27
  sylow_inf : IsSylowTwoOf T (H ⊓ M)
  noNonExtremal : D2NoNonExtremalAt P M T
  sylow : IsSylowTwoOf T M
  normalizer_le : Subgroup.normalizer (T : Set G) ≤ H
  not_normalizer_le : ¬ Subgroup.normalizer (T : Set G) ≤ M

theorem D2L34R27.amb {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K T) : D2Amb3 G :=
  c.ctx.amb

end CFSG.LocalAnalysis.RankThreeTheoremC
