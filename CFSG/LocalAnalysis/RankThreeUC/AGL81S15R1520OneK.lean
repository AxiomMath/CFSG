module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneH
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneJCover
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O82
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneI
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0c
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

theorem pRank_yComponent_le_one {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (h19 : Row1519 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) {p : ℕ}
    (hp : p ∈ sigmaM G M) (hpp : p.Prime) (hp2 : p ≠ 2)
    (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M)))
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) : Open.pRank p Ls ≤ 1 := by
  obtain ⟨L, hL⟩ := hLifts Ls hLs
  have h1 := h19 p hp Ls L hLs hL
  have hmem : ∀ x : ↥L, (toStar (T.subgroupOf M)) (x : ↥M) ∈ Ls := fun x =>
    hL.2 ▸ mem_map_of_mem _ x.2
  let f : ↥L →* ↥Ls := ((toStar (T.subgroupOf M)).comp L.subtype).codRestrict Ls hmem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hL.2] at hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have h2 := pRank_le_one_of_section hpp hp2 h1 (le_refl L) f hf
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2

theorem exists_pComponent_of_normal
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h19 : Row1519 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M)
    (hp5 : 5 ≤ p) {L : Subgroup ↥M} [hLn : L.Normal] (hrk : 2 ≤ Open.pRank p (cMBar L)) :
    ∃ I : Subgroup ↥M, I ≤ cMHat L ∧ CFSG.IsPComponent p (I.subgroupOf (cMHat L)) ∧
      Open.pRank p I = 1 ∧ 1 ≤ Open.pRank 3 I := by
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hpp⟩
  have hno : ∀ N : Subgroup ↥M, N.Normal → N.index ≠ p := fun N hN => by
    haveI := hN
    exact no_normal_index_p_of_ctx_gen ctx hp N
  have hN : ∀ T₀ : Subgroup ↥M, T₀ ≠ ⊥ → T₀ ≤ T.subgroupOf M →
      (T₀.subgroupOf (T.subgroupOf M)).Characteristic →
      Open.pRank p (normalizer (T₀ : Set ↥M)) ≤ 1 := fun T₀ hne hle hchar =>
    pRank_normalizer_pair_le_one ctx.sylow.le hle hchar hne hpp (ctx.rank_char p hp)
  haveI hHn : (cMHat L).Normal := cMHat_normal hLn
  have hrkH : 2 ≤ Open.pRank p (cMHat L) := by
    have hbar : barO2 (cMHat L) = cMBar L :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    rw [pRank_barO2_eq_aux_eq (cMHat L) hpp hp2, hbar]
    exact hrk
  obtain ⟨I, hIH, hI, h3, hpI⟩ := exists_pComponent_dvd_three_of_two_le_pRank hSz ctx.gn.kGroup
    hpp hp5 ctx.gn.charTwo ctx.gn.sylow hN hno hrkH
  have hIp : CFSG.IsPComponent p I :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff p I
      (cMHat L) hIH (Subgroup.Normal.isSubnormal hHn)).1 hI
  have hle : Open.pRank p I ≤ 1 :=
    pRank_pComponent_le_one hpp hp2 ctx.cover.2 (ctx.rank_N₁ p hp) (ctx.rank_N₂ p hp)
      (pRank_yComponent_le_one h19 hLifts hp hpp hp2) hIp
  exact ⟨I, hIH, hI,
    le_antisymm hle (CFSG.LocalAnalysis.RankThreeUC.S15.one_le_pRank_of_dvd I hpp hpI),
    CFSG.LocalAnalysis.RankThreeUC.S15.one_le_pRank_of_dvd I Nat.prime_three h3⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
