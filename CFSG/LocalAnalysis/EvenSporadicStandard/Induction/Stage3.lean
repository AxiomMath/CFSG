module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem stage3Pair {S : List TauCeti.SporadicName} {Q : TauCeti.SporadicName → PairClass}
    (row : Stage3Row S Q) (lit : Sol78Lit) (hH : Balance.UHered H)
    (hyp31 : ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ L : Subgroup H, SolStd L →
        (∃ s ∈ S, OddCover s L) → Hyp31Glob H N row.IsK (IsLS S) ∧ Hyp31FourA H N row.IsK)
    (h33 : Lemma33Two row.IsK (IsLS S) H) :
    ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ L : Subgroup H, SolStd L →
        (∃ s ∈ S, OddCover s L) →
          ∃ (s' : TauCeti.SporadicName) (L' K : Subgroup H) (t u : H), s' ∈ S ∧ OddCover s' L' ∧
            SolomonGlobalQ H L' K t u ∧ Q s' H L' K u ∧ ¬ (K ≤ N ∧ Maximal (K.subgroupOf N)) := by
  classical
  intro N hN hidx hkp L hSol ⟨s, hsS, hcov⟩
  obtain ⟨hglob, hfourA⟩ := hyp31 N hN hidx hkp L hSol ⟨s, hsS, hcov⟩
  have hyp : Hyp31 H N row.IsK (IsLS S) := { row.hyp31Row, hglob with }
  obtain ⟨K₀, u₀, hQ₀⟩ := row.rowExists s hsS H L hcov
  have hK₀ : row.IsK ↥K₀ := row.rowIsK s hsS H L K₀ u₀ hcov hQ₀
  obtain ⟨hu₀2, hu₀L, hK₀X, hchar₀, hK₀q⟩ := (row.rec36 s hsS).local_facts hcov hQ₀
  obtain ⟨t₀, ht₀2, ht₀c⟩ := hSol.exists_involution
  have ht₀L : t₀ ∈ centralizer (L : Set H) := mem_centralizer_iff.2 fun l hl =>
    mem_centralizer_singleton_iff.1 (ht₀c.1 hl)
  have hCt₀ := hSol.centralizer_le_normalizer ht₀L ht₀2
  have hu₀t₀ : u₀ * t₀ = t₀ * u₀ := mem_centralizer_iff.1 ht₀L u₀ hu₀L
  have hK₀comp : IsCompIn K₀ (centralizer ({u₀} : Set H) ⊓ centralizer ({t₀} : Set H)) :=
    isCompIn_of_normal
      (fun k hk => ⟨(hK₀X hk).2, mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 ht₀L k (hK₀X hk).1)⟩) hK₀q
      (normal_subgroupOf_of_characteristic ht₀L hCt₀ hK₀X hchar₀)
  have hu₀1 : u₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hu₀2; omega
  have hT₀p : IsPGroup 2 ↥(zpowers u₀ ⊔ zpowers t₀) := by
    have hts : t₀ ∈ normalizer ((zpowers u₀ : Subgroup H) : Set H) := by
      refine Subgroup.centralizer_le_normalizer ((zpowers u₀ : Subgroup H) : Set H) ?_
      rw [centralizer_zpowers_eq]
      exact mem_centralizer_singleton_iff.2 hu₀t₀.symm
    have ht₀sq : t₀ ^ 2 ∈ zpowers u₀ := by
      have h1 : t₀ ^ 2 = 1 := by
        have := pow_orderOf_eq_one t₀
        rwa [ht₀2] at this
      rw [h1]
      exact one_mem _
    exact isPGroup_sup_zpowers (isPGroup_zpowers_of_orderOf_two hu₀2) hts ht₀sq
  have hT₀ne : zpowers u₀ ⊔ zpowers t₀ ≠ ⊥ := fun hb => hu₀1 (Subgroup.mem_bot.1
    (hb ▸ mem_sup_left (mem_zpowers u₀)))
  obtain ⟨n₀, L₀, T₀, s₀, hch₀, hL₀⟩ :=
    lit.cor23 H hH hkp N hN (perfect_subgroups_le_of_index_le_two hN.normal hidx)
      (zpowers u₀ ⊔ zpowers t₀) K₀ hT₀p (by rw [centralizer_sup_zpowers_eq]; exact hK₀comp)
    (hyp.K_not_exc _ hK₀).1 (hyp.K_not_exc _ hK₀).2
  have hKch₀ : IsKChain row.IsK N n₀ := ⟨L₀, T₀, s₀, hch₀, by rw [hL₀]; exact hK₀⟩
  have hn₀ : 1 ≤ n₀ := by
    by_contra hn0
    have hn0' : n₀ = 0 := by omega
    have hKN : K₀ = N := by rw [← hL₀, ← hch₀.last, hn0']
    have hcomp : IsCompIn N (centralizer ((zpowers u₀ ⊔ zpowers t₀ : Subgroup H) : Set H)) := by
      rw [← hKN, centralizer_sup_zpowers_eq]
      exact hK₀comp
    exact hT₀ne (hN.eq_bot_of_isCompIn hcomp)
  obtain ⟨n, hmax⟩ := exists_isMaxKChain hKch₀
  obtain ⟨L₁, T₁, s₁, hch, hL1⟩ := hmax.1
  have hn : n₀ ≤ n := hmax.2 n₀ hKch₀
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    exact not_klike_last hyp hch (by omega) (by
      have : n - 1 = 0 := by omega
      rw [this]
      exact KLike.of_isK hL1)
  obtain ⟨hL, hK, hle, hlt, hmaxL, hstdL, hstdK, hA, hcyc⟩ :=
    lemma33_pair hyp (lit.thm22 H hH) hkp hch hL1 hn2
  have hKlike : KLike row.IsK (L₁ (n - 2)) :=
    (lemma33_one_klike hyp (lit.thm22 H hH) hkp hch hL1 hn2).2.1
  obtain ⟨s', hs', hqs, hodd, hspor⟩ := hL
  have hcov' : OddCover s' (L₁ (n - 1)) := ⟨hqs, hodd, hspor⟩
  have hinLK : InL (L₁ (n - 2)) := hch.inL hN (by omega)
  have hinLL : InL (L₁ (n - 1)) := hch.inL hN (by omega)
  obtain ⟨u, hQ⟩ := row.rowFit s' hs' H (L₁ (n - 1)) (L₁ (n - 2)) hcov' hle hinLK.isQuasisimple
    hK hstdK hA
  have hSol' : SolStd (L₁ (n - 1)) := solStd_of_inL_stdBare hinLL hstdL
  obtain ⟨t, ht2, htc⟩ := hSol'.exists_involution
  have htL : t ∈ centralizer (L₁ (n - 1) : Set H) := mem_centralizer_iff.2 fun l hl =>
    mem_centralizer_singleton_iff.1 (htc.1 hl)
  have hCt := hSol'.centralizer_le_normalizer htL ht2
  obtain ⟨hu2, huL, hKX, hchar, hKq⟩ := (row.rec36 s' hs').local_facts hcov' hQ
  have hut : u * t = t * u := mem_centralizer_iff.1 htL u huL
  have hKcomp : IsCompIn (L₁ (n - 2)) (centralizer ({u} : Set H) ⊓ centralizer ({t} : Set H)) :=
    isCompIn_of_normal
      (fun k hk => ⟨(hKX hk).2, mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 htL k (hKX hk).1)⟩) hKq
      (normal_subgroupOf_of_characteristic htL hCt hKX hchar)
  have hB : BTheoremAt u := lit.bthm H hH hkp hN.oddCore_eq_bot u hu2
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have htypeL : ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      L₁ (n - 2) ≤ M ⊔ CFSG.conjugate M t → M ≠ L₁ (n - 2) → ∃ s'' ∈ S, OddCover s'' M := by
    intro M hM hKM hMK
    have hinLM : InL M := ⟨zpowers u, fun hb => hu1 (Subgroup.mem_bot.1 (hb ▸ mem_zpowers u)),
      isPGroup_zpowers_of_orderOf_two hu2, by rw [centralizer_zpowers_eq]; exact hM⟩
    exact h33 lit hH hkp N n L₁ T₁ s₁ hyp hfourA hch hL1 hn2 hmax.2 M hinLM
      (lt_of_le_sup_conj hu2 ht2 hut hKcomp hM hKM) hMK
  have hC2 : u ∉ L₁ (n - 2) → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      (∃ s'' ∈ S, OddCover s'' M) → ∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2 := by
    intro huK M hM hMcov P
    rcases row.inOrTwoSylow with hall | htwo
    · exact absurd (hall s' hs' H (L₁ (n - 1)) (L₁ (n - 2)) u hcov' hQ) huK
    · obtain ⟨s'', hs'', hcM⟩ := hMcov
      have hinLM : InL M := ⟨zpowers u, fun hb => hu1 (Subgroup.mem_bot.1 (hb ▸ mem_zpowers u)),
        isPGroup_zpowers_of_orderOf_two hu2, by rw [centralizer_zpowers_eq]; exact hM⟩
      have hMN : M ≠ N := by
        intro hMN
        have hcomp : IsCompIn N (centralizer ((zpowers u : Subgroup H) : Set H)) := by
          rw [← hMN, centralizer_zpowers_eq]
          exact hM
        exact hu1 (Subgroup.mem_bot.1 (hN.eq_bot_of_isCompIn hcomp ▸ mem_zpowers u))
      have hLM : IsLS S ↥M := ⟨s'', hs'', hcM⟩
      have hSolM : SolStd M :=
        solStd_of_inL_stdBare hinLM (stdBare_of_inL hyp (lit.thm22 H hH) hkp hinLM hMN hLM)
      exact htwo s'' hs'' H N M hN hidx hkp hcM hSolM (hyp.type_max M hinLM hLM).2 P
  have hCL2 : u ∉ L₁ (n - 2) →
      ∀ P : Sylow 2 (centralizer (L₁ (n - 1) : Set H)), Nat.card P = 2 := by
    intro huK P
    rcases row.inOrTwoSylow with hall | htwo
    · exact absurd (hall s' hs' H (L₁ (n - 1)) (L₁ (n - 2)) u hcov' hQ) huK
    · exact htwo s' hs' H N (L₁ (n - 1)) hN hidx hkp hcov' hSol' hcyc P
  have hK36 : L₁ (n - 2) = componentProduct (L₁ (n - 2)) u :=
    componentProduct_eq_of_rec36 hH (row.rec36 s' hs') row.outTwo hN hidx hkp hcov' hQ hSol'
      hcyc hCL2 htL ht2 hB htypeL hC2
  exact ⟨s', L₁ (n - 1), L₁ (n - 2), t, u, hs', hcov',
    ⟨hSol', hcyc, ht2, htL, hut, hK36⟩, hQ, hyp.not_max _ hinLK hKlike N le_rfl⟩

theorem hyp35At_of_stage3 {S : List TauCeti.SporadicName} {Q : TauCeti.SporadicName → PairClass}
    (row : Stage3Row S Q) (lit : Sol78Lit) (hH : Balance.UHered H)
    (hyp31 : ∀ N : Subgroup H, FStarSimple N → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → ∀ L : Subgroup H, SolStd L →
        (∃ s ∈ S, OddCover s L) → Hyp31Glob H N row.IsK (IsLS S) ∧ Hyp31FourA H N row.IsK)
    (h33 : Lemma33Two row.IsK (IsLS S) H) : Hyp35At S Q H := by
  intro N hN hidx hkp L hSol hcov
  obtain ⟨s', L', K, t, u, hs', hcov', hglob, hQ, -⟩ :=
    stage3Pair row lit hH hyp31 h33 N hN hidx hkp L hSol hcov
  exact ⟨s', L', K, t, u, hs', hcov', hglob, hQ⟩

end CFSG.EvenSporadicStandard.Induction
