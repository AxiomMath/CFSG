module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem D2L34SideCtx3.false_of_rank_two_le_conj {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {a : G} (ha : a ∉ M) {E : Subgroup G}
    (hEP : E ≤ (P : Subgroup G)) (hE2 : 2 ≤ CFSG.Open.pRank 3 E)
    (hEa : E ≤ M.map (MulAut.conj a).toMonoidHom) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have hΓ : GLBCore 3 2 (P : Subgroup G) ≤ M := h.fullCore 3 h.sigma P h.core
  set M₂ : Subgroup G := M.map (MulAut.conj a).toMonoidHom with hM₂
  obtain ⟨S, ⟨hES, hSP, hSM₂⟩, hmax⟩ := Set.exists_max_image
    {T : Subgroup G | E ≤ T ∧ T ≤ (P : Subgroup G) ∧ T ≤ M₂} (fun T => Nat.card T)
    (Set.toFinite _) ⟨E, le_rfl, hEP, hEa⟩
  have hSM : S ≤ M := hSP.trans hPM
  have hSp : IsPGroup 3 S := P.isPGroup'.to_le hSP
  have hS2 : 2 ≤ CFSG.Open.pRank 3 S := hE2.trans (pRank_mono 3 hp3 hES)
  have hNM : Subgroup.normalizer (S : Set G) ≤ M := normalizer_le_of_core hp3 P hPM hΓ hSM hSp hS2
  have hSa : S.map (MulAut.conj a⁻¹).toMonoidHom ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨y, hy, hys⟩ := hSM₂ hs
    have : (MulAut.conj a⁻¹).toMonoidHom s = y := by
      rw [← hys]
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hy
  have hN' : Subgroup.normalizer ((S.map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_core hp3 P hPM hΓ hSa (hSp.map _)
      (by rw [pRank_map_of_injective 3 hp3 _ (MulAut.conj a⁻¹).injective]; exact hS2)
  rw [normalizer_map_conj] at hN'
  have hNM₂ : Subgroup.normalizer (S : Set G) ≤ M₂ := by
    intro x hx
    refine ⟨(MulAut.conj a⁻¹).toMonoidHom x, hN' ⟨x, hx, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hNPS : (P : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) ≤ S := by
    have h1 : E ≤ (P : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) :=
      le_inf (hES.trans hSP) (hES.trans Subgroup.le_normalizer)
    have hcard := hmax _ ⟨h1, inf_le_left, inf_le_right.trans hNM₂⟩
    have hSle : S ≤ (P : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) :=
      le_inf hSP Subgroup.le_normalizer
    exact (Subgroup.eq_of_le_of_card_ge hSle hcard).ge
  have hPS : (P : Subgroup G) ≤ S := by
    refine le_of_normalizer_inf_le (p := 3) P.isPGroup' ?_
    rw [inf_eq_right.mpr hSP]
    exact hNPS
  have hPM₂ : (P : Subgroup G) ≤ M₂ := hPS.trans hSM₂
  have heq : M₂ = M := eq_of_isMaxTwoLocal_of_three_le_pRank h.d1 h.sigma h.core hPM hP3.ge
    (rankThreeIsMaxTwoLocal_map h.maxLocal (MulAut.conj a)) hPM₂
  apply ha
  rw [← maxTwoLocal_self_normalizing M h.maxLocal]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem D2L34SideCtx3.pRank_inf_conj_le_one {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) {g : G} (hg : g ∉ M) :
    CFSG.Open.pRank 3 (M ⊓ GLBConj g M) ≤ 1 := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  by_contra hlt
  have h2 : 2 ≤ CFSG.Open.pRank 3 (M ⊓ GLBConj g M) := by omega
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  obtain ⟨E, hEle, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) h2
  have hEM : E ≤ M := hEle.trans inf_le_left
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEcard
  obtain ⟨m, hm⟩ := exists_conjugate_le_sylow_of_le 3 P hPM hEM hEp
  refine h.false_of_rank_two_le_conj (a := (m : G) * g⁻¹)
    (E := E.map (MulAut.conj (m : G)).toMonoidHom) ?_ hm ?_ ?_
  · intro ha
    apply hg
    have h1 : (m : G)⁻¹ * ((m : G) * g⁻¹) ∈ M := M.mul_mem (M.inv_mem m.2) ha
    have h2' : g = ((m : G)⁻¹ * ((m : G) * g⁻¹))⁻¹ := by group
    rw [h2']
    exact M.inv_mem h1
  · rw [pRank_map_of_injective 3 hp3 _ (MulAut.conj (m : G)).injective]
    exact (le_pRank_of_isElemAbelian hp3 hEel hEcard)
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨y, hy, hye⟩ := (hEle he).2
    refine ⟨y, hy, ?_⟩
    rw [← hye]
    simp [MulAut.conj_apply, mul_assoc]

theorem one_le_pRank_three_of_dvd_card (N : Subgroup G) (hdvd : 3 ∣ Nat.card N) :
    1 ≤ CFSG.Open.pRank 3 N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hx' : orderOf (x : G) = 3 := (Subgroup.orderOf_coe x).trans hx
  unfold CFSG.Open.pRank
  refine le_csSup (pRank_set_bddAbove 3 Nat.prime_three.one_lt N)
    ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx', pow_orderOf_eq_one,
      one_zpow]
  · rw [Nat.card_zpowers, hx', pow_one]

theorem D2L34SideCtx3.exists_cyclic_of_not_stronglyEmbedded {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hns : ¬ GLBStronglyEmbedded 3 M) :
    ∃ g : G, g ∉ M ∧ 3 ∣ Nat.card ↥(M ⊓ GLBConj g M) ∧ CFSG.Open.pRank 3 (M ⊓ GLBConj g M) = 1 := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  have := h.setting.simple
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top h.setting.nonab
    h.maxLocal.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have h3M : 3 ∣ Nat.card M := by
    obtain ⟨F, hFP, -, hFcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 1)
        (H := (P : Subgroup G)) (by rw [hP3]; norm_num)
    have := Subgroup.card_dvd_of_le (hFP.trans hPM)
    rw [hFcard, pow_one] at this
    exact this
  by_contra hcon
  refine hns ⟨hMtop, h3M, fun g hg hdvd => hcon ⟨g, hg, hdvd, le_antisymm
    (h.pRank_inf_conj_le_one hg) (one_le_pRank_three_of_dvd_card _ hdvd)⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
