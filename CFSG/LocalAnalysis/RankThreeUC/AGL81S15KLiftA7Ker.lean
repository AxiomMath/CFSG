module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.GroupTheory.Commutator.JoinNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

private theorem map_barToStar_barO2 {T A : Subgroup X} (hX : GNSetting X T) :
    (barO2 A).map (barToStar T (pCore_le_gnC hX)) = A.map (toStar T) := by
  unfold barO2
  rw [Subgroup.map_map]
  congr 1

private theorem map_barToStar_barO2_gnC {T : Subgroup X} (hX : GNSetting X T) :
    (barO2 (gnC T)).map (barToStar T (pCore_le_gnC hX)) = ⊥ := by
  rw [map_barToStar_barO2 hX, toStar, Subgroup.map_eq_bot_iff]
  exact (QuotientGroup.ker_mk' (gnC T)).ge

private theorem inf_barO2_gnD_barO2_gnC {T : Subgroup X} (hX : GNSetting X T) :
    barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) ⊓ barO2 (gnC T) = ⊥ := by
  have hQleC : CFSG.pCore 2 X ≤ gnC T := pCore_le_gnC hX
  have hcomap : (barO2 (gnC T)).comap (QuotientGroup.mk' (CFSG.pCore 2 X)) = gnC T := by
    rw [barO2]
    exact Subgroup.comap_map_eq_self (by rwa [QuotientGroup.ker_mk'])
  have hmap := Subgroup.map_inf_comap (CFSG.AGLEmbeddingD2.GN.gnD T) (barO2 (gnC T))
    (QuotientGroup.mk' (CFSG.pCore 2 X))
  rw [hcomap] at hmap
  show (CFSG.AGLEmbeddingD2.GN.gnD T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ⊓
      (gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊥
  rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk',
    ← CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore (G := X) 2]
  exact CFSG.AGLEmbeddingD2.GN.centralizer_quot_inf_le hX

private theorem barO2_le_sup_of_le_gnImg {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hL : LiftOf T L Ls)
    (hLsD : Ls ≤ gnImg T (CFSG.AGLEmbeddingD2.GN.gnD T)) :
    barO2 L ≤ barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) ⊔ barO2 (gnC T) := by
  have hpre : L ≤ CFSG.AGLEmbeddingD2.GN.gnD T ⊔ gnC T := by
    have h1 : L ≤ Ls.comap (toStar T) := by
      intro x hx
      exact hL.2 ▸ Subgroup.mem_map_of_mem (toStar T) hx
    have h2 : Ls.comap (toStar T) ≤
        (gnImg T (CFSG.AGLEmbeddingD2.GN.gnD T)).comap (toStar T) :=
      Subgroup.comap_mono hLsD
    have h3 : (gnImg T (CFSG.AGLEmbeddingD2.GN.gnD T)).comap (toStar T) =
        CFSG.AGLEmbeddingD2.GN.gnD T ⊔ gnC T := by
      unfold gnImg
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact h1.trans (h2.trans (le_of_eq h3))
  calc barO2 L ≤ barO2 (CFSG.AGLEmbeddingD2.GN.gnD T ⊔ gnC T) := Subgroup.map_mono hpre
    _ = barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) ⊔ barO2 (gnC T) := Subgroup.map_sup _ _ _

private theorem eq_bot_of_barO2_le_barO2_gnC {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hL : LiftOf T L Ls)
    (hLC : barO2 L ≤ barO2 (gnC T)) : Ls = ⊥ := by
  have h1 : (barO2 L).map (barToStar T (pCore_le_gnC hX)) = Ls := by
    rw [map_barToStar_barO2 hX, hL.2]
  have hbot : (barO2 L).map (barToStar T (pCore_le_gnC hX)) = ⊥ := by
    refine le_bot_iff.1 ?_
    calc (barO2 L).map (barToStar T (pCore_le_gnC hX))
        ≤ (barO2 (gnC T)).map (barToStar T (pCore_le_gnC hX)) := Subgroup.map_mono hLC
      _ = ⊥ := map_barToStar_barO2_gnC hX
  rw [← h1, hbot]

private theorem le_gnImg_gnD_of_not_gnD_le {T : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hZ : Subgroup.center ↥Ls = ⊥)
    (hD : ¬ CFSG.AGLEmbeddingD2.GN.gnD T ⊓
      Ls.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T) :
    Ls ≤ gnImg T (CFSG.AGLEmbeddingD2.GN.gnD T) := by
  let Ds : Subgroup (X ⧸ gnC T) := gnImg T (CFSG.AGLEmbeddingD2.GN.gnD T)
  haveI hDn : Ds.Normal := (CFSG.AGLEmbeddingD2.GN.normal_gnD T).map _
    (QuotientGroup.mk'_surjective (gnC T))
  haveI hNn : (Ds.subgroupOf Ls).Normal := Subgroup.normal_subgroupOf (H := Ls) (N := Ds)
  haveI hsimple : IsSimpleGroup ↥Ls := by
    haveI : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.2.2.2
    let e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* ↥Ls :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact MulEquiv.isSimpleGroup e.symm
  have hne : Ds.subgroupOf Ls ≠ ⊥ := by
    intro hbot
    apply hD
    intro x hx
    obtain ⟨hxD, hxL⟩ := Subgroup.mem_inf.1 hx
    have hxLs : toStar T x ∈ Ls := hxL
    have hxDs : toStar T x ∈ Ds := ⟨x, hxD, rfl⟩
    have hmem : (⟨toStar T x, hxLs⟩ : ↥Ls) ∈ Ds.subgroupOf Ls :=
      Subgroup.mem_subgroupOf.2 hxDs
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : toStar T x = 1 := congrArg Subtype.val hmem
    exact (QuotientGroup.eq_one_iff x).1 h1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ds.subgroupOf Ls) with hbot | htop
  · exact absurd hbot hne
  · intro x hx
    have hmem : (⟨x, hx⟩ : ↥Ls) ∈ Ds.subgroupOf Ls := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 hmem

private theorem false_of_commutator_eq_bot {T L : Subgroup X} (hL : IsC2 L)
    (hLDC : barO2 L ≤ barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) ⊔ barO2 (gnC T))
    (hLD : ⁅barO2 L, barO2 (CFSG.AGLEmbeddingD2.GN.gnD T)⁆ = ⊥)
    (hLC : ⁅barO2 L, barO2 (gnC T)⁆ = ⊥) : False := by
  have hjoin : ⁅barO2 L, barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) ⊔ barO2 (gnC T)⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (Y := barO2 L) (A := barO2 (CFSG.AGLEmbeddingD2.GN.gnD T)) (B := barO2 (gnC T))
      (N := ⊥) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (le_of_eq hLD) (le_of_eq hLC)
  have hself : ⁅barO2 L, barO2 L⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono_right hLDC).trans (le_of_eq hjoin))
  exact liftOf_unique_aux1 hL.component hself

private theorem eq_one_of_barToStar_eq_one {T L : Subgroup X}
    (hX : GNSetting X T) (hLD : barO2 L ≤ barO2 (CFSG.AGLEmbeddingD2.GN.gnD T))
    {k : ↥(barO2 L)}
    (hk : barToStar T (pCore_le_gnC hX) (k : X ⧸ CFSG.pCore 2 X) = 1) : k = 1 := by
  have hDC := inf_barO2_gnD_barO2_gnC hX
  have hkC : (k : X ⧸ CFSG.pCore 2 X) ∈ barO2 (gnC T) := by
    change (k : X ⧸ CFSG.pCore 2 X) ∈
      (gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))
    rw [← ker_barToStar T (pCore_le_gnC hX)]
    exact MonoidHom.mem_ker.2 hk
  have hkbot : (k : X ⧸ CFSG.pCore 2 X) ∈ (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) := by
    rw [← hDC, Subgroup.mem_inf]
    exact ⟨hLD k.2, hkC⟩
  exact Subtype.ext (Subgroup.mem_bot.1 hkbot)

theorem nonempty_barO2_mulEquiv_of_not_gnD_le {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X}
    (hLs : IsComponentOf Ls ⊤) (hZ : Subgroup.center ↥Ls = ⊥) (hL : LiftOf T L Ls)
    (hD : ¬ CFSG.AGLEmbeddingD2.GN.gnD T ⊓
      Ls.comap (QuotientGroup.mk' (gnC T)) ≤ gnC T) :
    Nonempty (↥(barO2 L) ≃* ↥Ls) := by
  obtain ⟨f, hfφ, hfsurj, -⟩ := barO2_centralExt' hX hLs hL
  haveI hnD : (CFSG.AGLEmbeddingD2.GN.gnD T).Normal :=
    CFSG.AGLEmbeddingD2.GN.normal_gnD T
  have hLsD := le_gnImg_gnD_of_not_gnD_le hLs hZ hD
  have hLDC := barO2_le_sup_of_le_gnImg hL hLsD
  have hLCcomm : ⁅barO2 L, barO2 (gnC T)⁆ = ⊥ := by
    rcases isC2_barO2_le_or_commute hL.1 (gnC T) with hLC | hLC
    · exact absurd (eq_bot_of_barO2_le_barO2_gnC hX hL hLC) (liftOf_unique_aux2 hLs)
    · exact hLC
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 ?_
    intro k hk
    have hLD : barO2 L ≤ barO2 (CFSG.AGLEmbeddingD2.GN.gnD T) := by
      rcases isC2_barO2_le_or_commute hL.1
        (CFSG.AGLEmbeddingD2.GN.gnD T) with hLD | hLD
      · exact hLD
      · exact (false_of_commutator_eq_bot hL.1 hLDC hLD hLCcomm).elim
    refine eq_one_of_barToStar_eq_one hX hLD ?_
    have h := congrArg Subtype.val hk
    rwa [hfφ] at h
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hfsurj⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
