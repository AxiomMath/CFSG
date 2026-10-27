module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

namespace O1218Proof

variable {G : Type} [Group G] [Finite G]

theorem isTwoLocal_normalizer_pCoreOf {H : Subgroup G} (h : pCoreOf 2 H ≠ ⊥) :
    IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) ∧
      H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  refine ⟨⟨pCoreOf 2 H, h, (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype, rfl⟩, ?_⟩
  have hN : ((pCoreOf 2 H).subgroupOf H).Normal := by
    have : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    exact CFSG.pCore_normal (p := 2) (G := ↥H)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp hN

theorem exists_maxTwoLocal_ge {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ N : Subgroup G, rankThreeIsMaxTwoLocal N ∧ H ≤ N := by
  classical
  obtain ⟨M, ⟨hM, hHM⟩, hmax⟩ := Set.exists_max_image {K : Subgroup G | IsTwoLocal K ∧ H ≤ K}
    (fun K => Nat.card K) (Set.toFinite _) ⟨H, hH, le_rfl⟩
  exact ⟨M, ⟨hM, fun K hK hMK =>
    (Subgroup.eq_of_le_of_card_ge hMK (hmax K ⟨hK, hHM.trans hMK⟩)).symm⟩, hHM⟩

theorem le_of_isTwoLocal_of_mem_sigmaA (hS : Standing G) (hUC : rankThreeUC G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    {H : Subgroup G} (hH : IsTwoLocal H) (hEH : E ≤ H) : H ≤ M := by
  have hpp : p.Prime := sigmaA_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hEp : IsPGroup p E := elementary_isPGroup p E hE
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨M₁, hcw⟩ := exists_isCoreWitness hUC hp Q
  have hQM₁ : (Q : Subgroup G) ≤ M₁ := le_normalizer.trans (hcw.normalizer_le hS hp)
  have hk : 2 ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hpp.one_lt (le_refl E) hE hEc
  have hE2 : 2 ≤ CFSG.Open.pRank p (M ⊓ M₁) :=
    hk.trans (pRank_mono p hpp.one_lt (le_inf hEM (hEQ.trans hQM₁)))
  have hMM₁ : M ≤ M₁ := hcw.u2 M hM.1 hE2
  have heq : M₁ = M := hM.2 M₁ hcw.maxLocal.1 hMM₁
  have hH2 : 2 ≤ CFSG.Open.pRank p (H ⊓ M₁) :=
    hk.trans (pRank_mono p hpp.one_lt (le_inf hEH (hEM.trans hMM₁)))
  exact heq ▸ hcw.u2 H hH hH2

end O1218Proof

theorem O1218_of (hO1211 : O1211) (hO1521b : O1521b) : O1218 := by
  intro G _ _ hS hUC M hM hwit hstr q p hq hp hp2 E hEM hE hEc hΓ H hEH hqH hO2
  obtain ⟨hN2, hHN⟩ := O1218Proof.isTwoLocal_normalizer_pCoreOf hO2
  have hEH0 : E ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hEH.trans hHN
  by_cases hpσ : p ∈ sigmaM G M
  · exact hHN.trans (O1218Proof.le_of_isTwoLocal_of_mem_sigmaA hS hUC hpσ.1 hM hEM hE hEc hN2 hEH0)
  · by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨H1, hH1, hH0H1⟩ := O1218Proof.exists_maxTwoLocal_ge hN2
      by_cases hH1M : H1 = M
      · exact hHN.trans (hH0H1.trans hH1M.le)
      · exfalso
        have hHH1 : H ≤ H1 := hHN.trans hH0H1
        have h9 : Nat.card E = 9 := by rw [hEc]; norm_num
        exact hO1521b G hS hUC M hM hwit hstr hpσ E hEM hE h9 hΓ H1 hH1 (hEH.trans hHH1) hH1M q hq
          (dvd_trans hqH (Subgroup.card_dvd_of_le (inf_le_inf_right M hHH1)))
    · have h5 : 5 ≤ p := by
        by_contra hlt
        have h2le := hp.two_le
        have h234 : p = 2 ∨ p = 3 ∨ p = 4 := by omega
        rcases h234 with h | h | h
        · exact hp2 h
        · exact hp3 h
        · rw [h] at hp
          exact absurd hp (by norm_num)
      exact hHN.trans (hO1211 G hS hUC M hM hwit hstr p hp h5 hpσ E hEM hE hEc hΓ _ hN2 hEH0)

end CFSG.LocalAnalysis.RankThreeUC.S15
