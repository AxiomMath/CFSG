module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftC
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftD
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding
open scoped commutatorElement

theorem cover_core_gen {Y Z : Type} [Group Y] [Finite Y] [Group Z] (π : Y →* Z)
    (hπ : Function.Surjective π) (hY : CFSG.Open.IsKGroup Y) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hrkC : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r π.ker ≤ 3)
    (hSch : KSch) (hK63 : K63) (hList : KListI1)
    (hloc : ∀ r : ℕ, r.Prime → r ≠ 2 →
      IsCyclic ↥(CFSG.Open.pCoreOf r π.ker) ∨
        (r = 3 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3))
    (Ls : Subgroup Z) (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hI1 : ShapeI1 (↥Ls ⧸ Subgroup.center ↥Ls))
    (h3 : 3 ∣ Nat.card (↥Ls ⧸ Subgroup.center ↥Ls)) :
    ∃ Ebar : Subgroup Y, CFSG.Open.IsComponentOf Ebar ⊤ ∧ Ebar.map π = Ls := by
  classical
  set Chat : Subgroup Y := π.ker with hChat
  obtain ⟨E, hEperf, hEπ⟩ := exists_perfect_cover π hπ Ls hLs
  have hnormJ : ∀ J : Subgroup Y, CFSG.Open.IsComponentOf J Chat →
      E ≤ Subgroup.normalizer (J : Set Y) := fun J hJ =>
    perfect_le_normalizer_component_gen Chat (fun r hr hr2 => hrkC r hr hr2) E hEperf J hJ
  have hE1 := perfect_le_layer_sup_centralizer hSch hY Chat E hEperf hnormJ
  haveI hLn := layerIn_normal Chat
  obtain ⟨E₂, hE₂perf, hE₂le, hE₂cent, hEle, -⟩ :=
    exists_perfect_centralizing (layerIn Chat) E hEperf Subgroup.le_normalizer_of_normal hE1
  have hLC : layerIn Chat ≤ Chat := sSup_le fun J hJ => hJ.1
  have hKbar : E₂ ⊔ Chat = Ls.comap π := by
    have h1 : Ls.comap π = E ⊔ Chat := by rw [← hEπ, Subgroup.comap_map_eq]
    rw [h1]
    apply le_antisymm
    · exact sup_le (hE₂le.trans (sup_le_sup_left hLC E)) le_sup_right
    · exact sup_le (hEle.trans (sup_le_sup_left hLC E₂)) le_sup_right
  have hperf : ⁅E₂ ⊔ Chat, E₂ ⊔ Chat⁆ ⊔ Chat = E₂ ⊔ Chat := by
    rw [hKbar]
    apply le_antisymm
    · refine sup_le (Subgroup.commutator_le_of_le le_rfl le_rfl) (fun x hx => ?_)
      rw [Subgroup.mem_comap]
      have : π x = 1 := hx
      rw [this]
      exact Ls.one_mem
    · intro k hk
      have hmapK : (Ls.comap π).map π = Ls := Subgroup.map_comap_eq_self_of_surjective hπ Ls
      have hcomm : (⁅Ls.comap π, Ls.comap π⁆).map π = Ls := by
        rw [Subgroup.map_commutator, hmapK]
        exact commutator_eq_self_of_isQuasisimple hLs.2.2
      have h3 : π k ∈ (⁅Ls.comap π, Ls.comap π⁆).map π := by
        rw [hcomm]
        exact hk
      have h4 : k ∈ ((⁅Ls.comap π, Ls.comap π⁆).map π).comap π := h3
      rwa [Subgroup.comap_map_eq] at h4
  obtain ⟨V, hVE₂, hVsup, hVperf, hVnil, hVmin⟩ := exists_minimal_supplement Chat E₂ hperf
  have hVmap : V.map π = Ls := by
    have h1 : (V ⊔ Chat).map π = Ls := by
      rw [hVsup, hKbar, Subgroup.map_comap_eq_self_of_surjective hπ]
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 le_rfl, sup_bot_eq] at h1
    exact h1
  have hVmin' : ∀ W : Subgroup Y, W ≤ V → W.map π = Ls → W = V := by
    intro W hWV hW
    apply hVmin W hWV
    rw [hKbar, ← hW, Subgroup.comap_map_eq]
  have hVlayer : V ≤ Subgroup.centralizer (layerIn Chat : Set Y) := hVE₂.trans hE₂cent
  have hlocal : ∀ r : ℕ, r.Prime → r ≠ 2 →
      V ≤ Subgroup.centralizer (CFSG.Open.pCoreOf r Chat : Set Y) := by
    intro r hr hr2
    haveI := pCoreOf_normal r Chat
    have hQr := pCoreOf_isPGroup r hr Chat
    have hnabLs := quotient_center_nonabelian_of_isQuasisimple hLs.2.2
    rcases hloc r hr hr2 with hcyc | ⟨hr3, h3Y⟩
    · exact perfect_le_centralizer_of_cyclic _ V hcyc hVperf
    · subst hr3
      rcases centralizes_or_solvable π Ls hLs V hVmap hVmin' hVnil (CFSG.Open.pCoreOf 3 Chat)
        with hV | ⟨hDs, hDc⟩
      · exact hV
      · exfalso
        have hCs := solvable_centralizer_amb (CFSG.Open.pCoreOf 3 Chat) V hr hQr hDs
        haveI hNn := zPre_normal π Ls V hVmap.le
        obtain ⟨e⟩ := zPre_equiv π Ls V hVmap
        haveI := hLs.2.2.2
        have hSs : IsSimpleGroup (↥V ⧸ (zPre π Ls V).subgroupOf V) := e.isSimpleGroup
        have hnab : ¬ IsMulCommutative (↥V ⧸ (zPre π Ls V).subgroupOf V) := by
          intro hc
          apply hnabLs
          exact ⟨⟨fun a b => by
            have := hc.is_comm.comm (e.symm a) (e.symm b)
            simpa using congrArg e this⟩⟩
        have hrS : 3 ∣ Nat.card (↥V ⧸ (zPre π Ls V).subgroupOf V) := by
          rw [Nat.card_congr e.toEquiv]
          exact h3
        exact not_k63List_three hList (hI1.of_equiv e.symm) hSs hnab
          (k63_apply_amb hK63 hr hr2 rfl hY h3Y (CFSG.Open.pCoreOf 3 Chat) V hQr hCs
            (zPre π Ls V) inf_le_left hSs hnab hrS)
  have hcentF := centralizes_fstar hO2 Chat V hVlayer hlocal
  have hsub : CFSG.Open.IsSubnormal (V ⊔ π.ker) ⊤ := by
    rw [hVsup, hKbar]
    exact isSubnormal_comap π hLs.2.1
  exact ⟨V, isComponent_of_centralizes_fstar π Ls hLs V hVmap hVperf hsub hcentF, hVmap⟩

theorem pRank_gnC_le_three_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (gnC (T.subgroupOf M)) ≤ 3 := by
  by_cases hσ : r ∈ sigmaM G M
  · exact (ctx.rank_C r hσ).trans (by norm_num)
  · exact (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (ctx.rank_odd_off r hr hr2 hσ)

theorem pRank_cHat_le_three_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r
      ((gnC (T.subgroupOf M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) ≤ 3 :=
  (pRank_barO2_eq_aux_eq (gnC (T.subgroupOf M)) hr hr2).ge.trans
    (pRank_gnC_le_three_gen ctx hr hr2)

theorem hloc_of_ctx_gen {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hcyc : CycHat G M T) (ctx : S15CtxGen G M T T₁ T₂) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    IsCyclic ↥(CFSG.Open.pCoreOf r
      ((gnC (T.subgroupOf M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)))) ∨
      (r = 3 ∧ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ 3) := by
  rcases hloc_of_ctx hcyc hr hr2 with h | rfl
  · exact Or.inl h
  · by_cases h3 : 3 ∈ sigmaM G M
    · refine Or.inl (exists_yComponent_dvd_aux_isCyclic hr hr2 (pCoreOf_isPGroup 3 hr _) ?_)
      exact (CFSG.SectionRank.pRank_mono hr.one_lt (Subgroup.map_subtype_le _)).trans
        ((pRank_barO2_eq_aux_eq (gnC (T.subgroupOf M)) hr hr2).ge.trans (ctx.rank_C 3 h3))
    · exact Or.inr ⟨rfl, (pRank_top_bar_le M hr hr2).trans
        ((CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) M).le.trans
          (ctx.rank_odd_off 3 hr hr2 h3))⟩

theorem liftsExist_of_ctx2_gen (hKSch : KSch) (hK63 : K63) (hList : KListI1)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hcyc : CycHat G M T) (ctx : S15CtxGen G M T T₁ T₂) :
    LiftsExist (T.subgroupOf M) T₁ T₂ := by
  intro Ls hLs
  have hle : CFSG.pCore 2 ↥M ≤ gnC (T.subgroupOf M) := pCore_le_gnC ctx.gn
  obtain ⟨Ebar, hE, hEs⟩ := cover_core_gen (barToStar (T.subgroupOf M) hle)
    (barToStar_surjective _ hle) (isKGroup_barO2 ctx.gn.kGroup) pCore_two_quotient_eq_bot
    (fun r hr hr2 => by rw [ker_barToStar]; exact pRank_cHat_le_three_gen ctx hr hr2)
    hKSch hK63 hList
    (fun r hr hr2 => by rw [ker_barToStar]; exact hloc_of_ctx_gen hcyc ctx hr hr2)
    Ls hLs.1 (shapeI1_of_gnShape ctx.shape hLs) (three_dvd_card_of_gnThree ctx.gnThree hLs)
  exact exists_lift_of_cover hle Ebar hE hEs

theorem liftsExist_of_ctx2 (hKSch : KSch) (hK63 : K63) (hList : KListI1)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hcyc : CycHat G M T) (ctx : S15Ctx2 G M T T₁ T₂) :
    LiftsExist (T.subgroupOf M) T₁ T₂ :=
  liftsExist_of_ctx2_gen hKSch hK63 hList hcyc (S15CtxGen.of_ctx2 ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15
