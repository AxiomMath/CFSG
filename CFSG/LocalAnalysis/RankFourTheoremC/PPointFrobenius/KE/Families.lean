module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE.Statement
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.SeitzScope
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharCyc
import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration

theorem pRank_le_pRank_mulAut {K : Type} [Group K] [Finite K]
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) {p : ℕ} (hp : p.Prime)
    (H : Subgroup K) :
    Open.pRank p H ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  obtain ⟨A, hAH, hAel, hAcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp H
  have hA' : IsElemAbelian p (A.map (MulAut.conj : K →* MulAut K)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAel _
  have hcard : Nat.card (A.map (MulAut.conj : K →* MulAut K)) = p ^ Open.pRank p H := by
    rw [Subgroup.card_map_of_injective hinj, hAcard]
  refine le_csSup ⟨Nat.card (MulAut K), ?_⟩
    ⟨A.map (MulAut.conj : K →* MulAut K), le_top, hA', hcard⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card (MulAut K) := Subgroup.card_le_card_group B

theorem ke_glbCore_eq_top_of_innerExFive (hS : SeitzInnerExFive) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* Cat d) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) (T : Sylow p K)
    (h3 : 3 ≤ Open.pRank p (T : Subgroup K)) : GLBCore p 1 (T : Subgroup K) = ⊤ := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  have hnc : ¬ IsCyclic (T : Subgroup K) :=
    CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hp (by omega)
  obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hnc
  set E₀ : Subgroup K := E.map (T : Subgroup K).subtype with hE₀
  have hEel' : IsElemAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mp hEel
  have hE₀el : IsElemAbelian p E₀ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEel' _
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hEcard]
  have hinj := CFSG.AGLEmbedding.conj_injective_of_simple hs hnab
  let ψ : K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp MulAut.conj
  have hψ : Function.Injective ψ := (MulAut.congr e).injective.comp hinj
  have hψel : IsElemAbelian p (E₀.map ψ) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀el ψ
  have hrank : ¬ RankLE2 p (Cat d) := by
    intro hr
    obtain ⟨A, -, hAel, hAcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (T : Subgroup K)
    have hmap := hr (A.map e.toMonoidHom)
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hAel _)
    rw [Subgroup.card_map_of_injective e.injective, hAcard] at hmap
    have h3' : p ^ 3 ≤ p ^ Open.pRank p (T : Subgroup K) := Nat.pow_le_pow_right hp.pos h3
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hgen := hS d p hp hp5 hpd hex hrank
    ⟨E₀.map ψ, hψel, by rw [Subgroup.card_map_of_injective hψ, hE₀card],
      InnerPlane.map_congr_conj e E₀ p⟩
  exact kc_glbCore_eq_top_of_innerGen hs hnab e hp T hgen

@[expose] def KFactOneLieIdentFive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ T : Sylow p K,
      3 ≤ Open.pRank p (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
          (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent)) ∧
        Nonempty (K ≃* CatGroup d)

theorem kFactOneLieIdentFive_of (hS : SeitzInnerExFive)
    (haut : OffCharAut) (halt : OneLieIdentAlt) (hcp : OneLieIdentLieCharP)
    (hspor : ∀ s, OneLieIdentSporAt s) : KFactOneLieIdentFive := by
  intro K _ _ hs hnab hcat p hp hp5 T h3 hΓ
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hnc : ¬ IsCyclic (T : Subgroup K) :=
    CFSG.Goldschmidt.Sec82.not_isCyclic_of_two_le_pRank hp (by omega)
  have hinj := CFSG.AGLEmbedding.conj_injective_of_simple hs hnab
  have hAut : ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
    intro h
    have := pRank_le_pRank_mulAut hinj hp (T : Subgroup K)
    omega
  have hres : ∃ d : TauCeti.ValidLieTypeIndex,
      ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨ (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
        IsReeGTwoIndex p d) ∧ Nonempty (K ≃* CatGroup d) := by
    obtain ⟨i, ⟨e⟩⟩ := hcat
    cases i with
    | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
    | alternating n hn => exact halt K n hn ⟨e⟩ p hp hp2 T hnc hΓ hAut
    | lie d =>
      by_cases hc : p = d.1.characteristic
      · exact hcp K hs hnab d ⟨e⟩ p hc hp hp2 T hnc hΓ hAut
      · exfalso
        by_cases hex : IsD2SeitzException p d.1
        · obtain ⟨d, hv⟩ := d
          change IsD2SeitzException p d at hex
          rcases hex with ⟨h3', -⟩ | ⟨h5, hd⟩
          · omega
          · rcases hd with hd | hd
            · have := haut K hs hnab ⟨d, hv⟩ ⟨e⟩ p (Or.inr ⟨h5, hd⟩)
              exact hAut this
            · subst h5
              subst hd
              exact hnc (isCyclic_sylow_five_suzuki 2 hv e T)
        · exact hΓ (ke_glbCore_eq_top_of_innerExFive hS hs hnab d e hp hp5 hc hex T h3)
    | sporadic s => exact hspor s K hs hnab ⟨e⟩ p hp hp2 T hnc hΓ hAut
  obtain ⟨d, hd, he⟩ := hres
  refine ⟨d, ?_, he⟩
  rcases hd with h | h | ⟨hp3, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · omega

theorem ke_psl2_of_abelian_sylow (hId : KFactOneLieIdentFive) (hU : KFactUnitarySylowStructure) :
    KEStatement := by
  intro K _ _ hs hnab hcat p _ hp5 T hab h3 hΓ
  obtain ⟨d, hd, ⟨e⟩⟩ := hId K hs hnab hcat p Fact.out hp5 T h3 hΓ
  rcases hd with ⟨n, hn, hd⟩ | ⟨hd, hfe⟩
  · obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
    exact ⟨n, hn, ⟨e.trans e'⟩⟩
  · exfalso
    obtain ⟨hcard, hcomm, -, -⟩ := hU K p d (by omega) hd ⟨e⟩ T
    have hle : (T : Subgroup K) ≤ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hab
    have hbot : ⁅(T : Subgroup K), (T : Subgroup K)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    rw [hbot, inf_eq_left.mpr hle] at hcomm
    have h1 : Nat.card (T : Subgroup K) = 1 := by
      rw [← hcomm, Subgroup.card_bot]
    have hq : 1 ≤ d.1.fieldExponent := by omega
    rw [hcard] at h1
    have : p ^ (3 * d.1.fieldExponent) > 1 :=
      Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KE
