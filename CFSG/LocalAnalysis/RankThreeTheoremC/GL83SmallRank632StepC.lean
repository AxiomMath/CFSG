module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Step0
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Solvable

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem stepC_pRank_top_le {q : ℕ} (hq : 1 < q) (M : Subgroup G) :
    CFSG.Open.pRank q (⊤ : Subgroup ↥M) ≤ CFSG.Open.pRank q M := by
  have h := CFSG.SectionRank.pRank_le_map hq M.subtype M.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

private theorem stepC_pRank_centralizer_le {M : Subgroup G} {x : G} (hxM : x ∈ M) {k : ℕ}
    (h : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ k) :
    CFSG.Open.pRank 3 (centralizer ({(⟨x, hxM⟩ : ↥M)} : Set ↥M)) ≤ k := by
  refine le_trans (CFSG.SectionRank.pRank_le_map (by norm_num) M.subtype M.subtype_injective _)
    (le_trans (CFSG.SectionRank.pRank_mono (by norm_num) ?_) h)
  rintro _ ⟨c, hc, rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))

theorem isSolvable_quotient_of_kfact (hK : SmallRankConstraintKFact3) (hS : Setting G)
    (hU0 : FullCoreLocal G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x : G} (hx : SmallRankPoint P M x)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) :
    Group.IsSolvable (↥M ⧸ primeComplementCore (G := ↥M) 3) := by
  have := hS.simple
  have hMtop : M ≠ ⊤ := twoLocal_ne_top hS.nonab M hs.isCoreMaxLocal.1.1
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal).1
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hs.largeObstruction_empty x
      ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩
  let e' : ((P.subtype hPM : Sylow 3 ↥M) : Subgroup ↥M) ≃*
      (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) :=
    (Subgroup.subgroupOfEquivOfLe hPM).trans e
  have hX : HasPrimeConstraint (G := ↥M) 3 :=
    hK ↥M (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper M hMtop)
      (fun q hq h5 => (stepC_pRank_top_le hq.one_lt M).trans
        (pRank_le_two_of_situation hS hs hq h5))
      (no_normal_index_three_of_situation hS hU0 hs) (P.subtype hPM) ⟨e'⟩
      ⟨⟨x, hPM hx.mem⟩, hx.mem, fun h => hx.ne_one (congrArg Subtype.val h),
        Subtype.ext hx.pow_eq_one, stepC_pRank_centralizer_le (hPM hx.mem) hCx⟩
  exact isSolvable_quotient_of_hasPrimeConstraint_wreath hX (P.subtype hPM) e'

private theorem stepC_primeCore_eq_map (M : Subgroup G) :
    rankThreePrimeCore 3 M = (primeComplementCore (G := ↥M) 3).map M.subtype := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro N ⟨hNM, hnormal, hcop⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hNM]
    refine Subgroup.map_mono (normal_coprime_le_primeComplementCore 3 _ hnormal ?_)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  · refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact primeComplementCore_coprime 3

theorem isSolvable_of_primeCore_of_quotient {M : Subgroup G}
    (hD : Group.IsSolvable ↥(rankThreePrimeCore 3 M))
    (hQ : Group.IsSolvable (↥M ⧸ primeComplementCore (G := ↥M) 3)) : Group.IsSolvable ↥M := by
  have hN : Group.IsSolvable ↥(primeComplementCore (G := ↥M) 3) := by
    rw [stepC_primeCore_eq_map] at hD
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((primeComplementCore (G := ↥M) 3).equivMapOfInjective M.subtype
        M.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  exact Group.isSolvable_of_subgroup_quotient (primeComplementCore (G := ↥M) 3)

end CFSG.LocalAnalysis.RankThreeTheoremC
