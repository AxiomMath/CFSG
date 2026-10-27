module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem pRank_top_le_of_forall_sylow {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {m : ℕ} (h : ∀ T : Sylow p K, Nat.card T ≤ p ^ m) : Open.pRank p (⊤ : Subgroup K) ≤ m := by
  refine CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE => ?_
  obtain ⟨T, hT⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE).exists_le_sylow
  exact (Subgroup.card_le_of_le hT).trans (h T)

theorem pRank_top_le_one_of_forall_sylow_isCyclic {K : Type*} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (h : ∀ T : Sylow p K, IsCyclic T) : Open.pRank p (⊤ : Subgroup K) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE => ?_
  obtain ⟨T, hT⟩ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.elementary_isPGroup p E hE).exists_le_sylow
  have : IsCyclic (T : Subgroup K) := h T
  have : IsCyclic E :=
    isCyclic_of_injective (Subgroup.inclusion hT) (Subgroup.inclusion_injective hT)
  rw [pow_one]
  exact card_le_of_isCyclic_of_pow_eq_one (Fact.out : p.Prime).pos
    fun x => Subtype.ext (hE.2 _ x.2)

theorem pRank_mulAut_le_two_of_altSix {K : Type} [Group K] [Finite K] (hZ : center K = ⊥)
    (e : K ≃* alternatingGroup (Fin (2 * 3))) : Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  refine (pRank_mulAut_le_add_pRank_outer hp hZ).trans ?_
  have h1 : Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
    refine openPRank_top_le_of_not_dvd 2 fun hd => ?_
    have hcard : Nat.card K = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rw [hcard] at hd
    omega
  have h2 : Open.pRank 3 (⊤ : Subgroup (Outer K)) ≤ 0 := by
    refine openPRank_top_le_of_not_dvd 0 fun hd => ?_
    have h4 := card_outer_alternatingGroup_dvd_four (2 * 3) (by norm_num)
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
      at h4
    have := (hd.trans h4)
    omega
  omega

theorem pRank_mulAut_le_two_of_m11 (hM11 : CFSG.AGLEmbeddingD2.KFactM11Three) {K : Type}
    [Group K] [Finite K] (hZ : center K = ⊥)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) :
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hOut, hS⟩ := hM11 K ⟨e⟩
  refine (pRank_mulAut_le_add_pRank_outer hp hZ).trans ?_
  have h1 : Open.pRank 3 (⊤ : Subgroup K) ≤ 2 :=
    pRank_top_le_of_forall_sylow fun T => ((hS T).1).le
  have h2 : Open.pRank 3 (⊤ : Subgroup (Outer K)) ≤ 0 := by
    refine openPRank_top_le_of_not_dvd 0 fun hd => ?_
    rw [hOut] at hd
    omega
  omega

theorem isCyclic_sylow_three_of_l28 {K : Type} [Group K] [Finite K] (hK : IsCaseTwoGroup 3 K)
    (T : Sylow 3 K) : IsCyclic (T : Subgroup K) := by
  obtain ⟨ε⟩ := CFSG.AGLEmbedding.KFactProofs.L28Local.nonempty_equiv_G8 hK
  have hT9 : Nat.card (T : Subgroup K) = 9 :=
    CFSG.AGLEmbedding.KFactProofs.L28Local.card_sylow_three ε T
  have hE9 : Nat.card ((T : Subgroup K).map ε.toMonoidHom) = 9 := by
    rw [← hT9]
    exact (Nat.card_congr (ε.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := CFSG.AGLEmbedding.KFactProofs.L28Local.exists_conj_of_card_nine
    CFSG.Quasithin.F6.L28Res.card_G8 hE9 CFSG.AGLEmbedding.KFactProofs.L28Local.card_T0
  let κ : ((T : Subgroup K).map ε.toMonoidHom) →* CFSG.AGLEmbedding.KFactProofs.L28Local.T0 :=
    ((MulAut.conj g).toMonoidHom.comp ((T : Subgroup K).map ε.toMonoidHom).subtype).codRestrict
      _ fun y => (hg y).1 y.2
  have hκ : Function.Injective κ := by
    intro a b hab
    have := congrArg (Subtype.val : _ → CFSG.Quasithin.F6.L28Res.G8) hab
    exact Subtype.ext ((MulAut.conj g).injective this)
  have hcyc : IsCyclic ((T : Subgroup K).map ε.toMonoidHom) := by
    have : IsCyclic CFSG.AGLEmbedding.KFactProofs.L28Local.T0 := by
      unfold CFSG.AGLEmbedding.KFactProofs.L28Local.T0
      infer_instance
    exact isCyclic_of_injective κ hκ
  exact (MulEquiv.isCyclic (ε.subgroupMap (T : Subgroup K))).mpr hcyc

theorem pRank_mulAut_le_two_of_l28 {K : Type} [Group K] [Finite K] (hZ : center K = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex 2 3 d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨q, hq, hqp, hqe⟩ := hd
  have hK : IsCaseTwoGroup 3 K := ⟨d, Or.inl ⟨rfl, q, hqp, hqe, hq⟩, ⟨e⟩⟩
  obtain ⟨ε⟩ := CFSG.AGLEmbedding.KFactProofs.L28Local.nonempty_equiv_G8 hK
  refine (pRank_mulAut_le_add_pRank_outer hp hZ).trans ?_
  have h1 : Open.pRank 3 (⊤ : Subgroup K) ≤ 1 :=
    pRank_top_le_one_of_forall_sylow_isCyclic fun T => isCyclic_sylow_three_of_l28 hK T
  have h2 : Open.pRank 3 (⊤ : Subgroup (Outer K)) ≤ 1 := by
    refine openPRank_top_le_of_not_dvd 1 fun hd => ?_
    have hAut : Nat.card (MulAut K) = 1512 := by
      rw [Nat.card_congr (MulAut.congr ε).toEquiv]
      exact CFSG.Quasithin.F6.L28Res.card_mulAut
    have hK : Nat.card K = 504 := by
      rw [Nat.card_congr ε.toEquiv]
      exact CFSG.Quasithin.F6.L28Res.card_G8
    have hinner : Nat.card (inner K) = 504 := by
      rw [← hK]
      exact (Nat.card_congr (MonoidHom.ofInjective
        (conj_injective_of_center_eq_bot hZ)).toEquiv).symm
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (inner K)
    rw [hAut, hinner] at hmul
    have h3 : Nat.card (Outer K) = 3 := by
      have : Nat.card (MulAut K ⧸ inner K) * 504 = 3 * 504 := by omega
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
    have h3' : Nat.card (Outer K) = 3 := h3
    rw [h3'] at hd
    omega
  omega

theorem pRank_mulAut_le_two_of_unitaryThree (hKU9 : KFactUnitaryAutElemRank) {K : Type} [Group K]
    [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 3 d)
    (hn : d.1.fieldExponent = 1) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun B _ hB => ?_
  have := hKU9 K 3 d hd ⟨e⟩ B hB
  rw [hn] at this
  simpa using this

theorem pRank_mulAut_le_two_of_linThreeFour {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsLThreeFourIndex d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hq, hq2, hqe⟩ := hd
  simp only at hq
  subst hq
  exact pRank_three_mulAut_linThreeFour q hq2 hqe hv e

theorem exists_linTwo_or_pRank_mulAut_le_two (hKU9 : KFactUnitaryAutElemRank)
    (hM11 : CFSG.AGLEmbeddingD2.KFactM11Three) {K : Type} [Group K] [Finite K]
    (hZ : center K = ⊥) {i : TauCeti.CFSGIndex} (hi : PPointType 3 i) (e : K ≃* i.Group) :
    (∃ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), i = .lie d ∧ IsLinTwoIndex 3 n d ∧ 2 ≤ n) ∨
      Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  cases hi with
  | linTwo hn hd => exact Or.inl ⟨_, _, rfl, hd, hn⟩
  | altTwoP h hp => exact Or.inr (pRank_mulAut_le_two_of_altSix hZ e)
  | unitary hd hn => exact Or.inr (pRank_mulAut_le_two_of_unitaryThree hKU9 hd hn e)
  | linTwoEight hp hd => exact Or.inr (pRank_mulAut_le_two_of_l28 hZ hd e)
  | mEleven hp => exact Or.inr (pRank_mulAut_le_two_of_m11 hM11 hZ e)
  | linThreeFour hp hd => exact Or.inr (pRank_mulAut_le_two_of_linThreeFour hd e)
  | suzuki hp => omega
  | tits hp => omega
  | mcl hp => omega
  | jFour hp => omega

end CFSG.LocalAnalysis.RankFourTheoremC
