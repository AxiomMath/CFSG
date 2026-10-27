module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props313Narrow
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L33Full

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

theorem le_of_coprime_of_centralizer {K M O : Subgroup G} (hKs : K ∈ solomonKStar G)
    (hCb : ∀ s ∈ K, orderOf s = 2 → centralizer ({s} : Set G) ≤ M)
    (hO : Nat.Coprime 2 (Nat.card O)) (hKO : K ≤ normalizer (O : Set G)) : O ≤ M := by
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have h2 := two_le_pRank_of_mem_solomonKStar hKs
  have hlarge : 2 ^ (1 + 1) ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h2
  have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two E O hE hlarge (hEK.trans hKO) hO
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSE, hScard⟩ := hS
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
  obtain ⟨⟨v, hvS⟩, hv1⟩ := exists_ne (1 : S)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hE.2 v (hSE hvS)) hv1'
  exact inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hvS)).trans
    (hCb v (hEK (hSE hvS)) hv2))

theorem commutator_eq_bot_of_le_coreActionKernel {K J : Subgroup G}
    (hKperf : Group.IsPerfect ↥K) (hOK : oddCoreIn K ≤ centralizer (K : Set G))
    (hKJ : K ≤ coreActionKernel J) (hJK : J ≤ normalizer (K : Set G)) : ⁅J, K⁆ = ⊥ := by
  have hKJn : K ≤ normalizer (J : Set G) := fun k hk => (hKJ hk).1
  have h1 : ⁅K, J⁆ ≤ oddCoreIn J := by
    refine commutator_le.mpr fun k hk j hj => ?_
    have h : (j⁻¹⁻¹ * k⁻¹⁻¹ * j⁻¹ * k⁻¹)⁻¹ ∈ oddCoreIn J :=
      inv_mem ((hKJ (inv_mem hk)).2 j⁻¹ (inv_mem hj))
    rwa [show (j⁻¹⁻¹ * k⁻¹⁻¹ * j⁻¹ * k⁻¹)⁻¹ = ⁅k, j⁆ by rw [commutatorElement_def]; group] at h
  have h2 : ⁅K, J⁆ ≤ K := (commutator_le_inf_of_le_normalizer hKJn hJK).trans inf_le_left
  have hKO : K ≤ normalizer (oddCoreIn J : Set G) := fun k hk =>
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hKJn hk))
  have h3 : ⁅K, J⁆ ≤ oddCoreIn K :=
    (le_inf h1 h2).trans (inf_le_oddCoreIn (coprime_card_oddCoreIn J) hKO)
  refine commutator_eq_bot_of_le_centralizer hKperf ?_
  rw [commutator_comm]
  exact h3.trans hOK

theorem le_of_mutual_cover {K J M : Subgroup G} (hJperf : ⁅J, J⁆ = J)
    (hKJ : K ≤ normalizer (J : Set G)) (hKM : K ≤ M) (hOJM : oddCoreIn J ≤ M)
    (hCb : ∀ b ∈ K, orderOf b = 2 → centralizer ({b} : Set G) ≤ M)
    (hKres : oddResidualIn K = K) (hKq' : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hnc : ∃ q : ↥K ⧸ pPrimeCore 2 ↥K, orderOf q = 2 ∧ q ∉ center (↥K ⧸ pPrimeCore 2 ↥K))
    (hKJQ : K ≤ J ⊔ coreActionKernel J) (hJKQ : J ≤ K ⊔ coreActionKernel J) : J ≤ M := by
  set Q := coreActionKernel J with hQ
  have hJQ : J ≤ normalizer (Q : Set G) := fun j hj =>
    FooteLit.mem_normalizer_coreActionKernel (le_normalizer hj)
  have hKQ : K ≤ normalizer (Q : Set G) := fun k hk =>
    FooteLit.mem_normalizer_coreActionKernel (hKJ hk)
  have hinv : ∀ b ∈ K, orderOf b = 2 → b ∈ Q ⊔ (J ⊓ M) := by
    intro b hb hb2
    have hbQJ : b ∈ Q ⊔ J := by
      rw [sup_comm]
      exact hKJQ hb
    obtain ⟨q, hqQ, j, hj, hbqj⟩ := exists_mul_of_mem_sup_normalizer hJQ hbQJ
    have hqO : q ∈ normalizer (oddCoreIn J : Set G) :=
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hqQ.1)
    have hfix : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn J := by
      have h1 : j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q ∈ oddCoreIn J := hqQ.2 j⁻¹ (inv_mem hj)
      have h2 : q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ ∈ oddCoreIn J :=
        (mem_normalizer_iff.mp hqO _).mp h1
      rw [hbqj, show q * j * j * (q * j)⁻¹ * j⁻¹ = q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ by
        group]
      exact h2
    obtain ⟨c, -, hcb, hcO⟩ := exists_commute_mem_coset (hKJ hb) hb2 hj hfix
    have hcM : c ∈ M := hCb b hb hb2 (mem_centralizer_singleton_iff.mpr hcb)
    have hjM : j ∈ M := by
      have h1 := mul_mem (inv_mem (hOJM hcO)) hcM
      rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    rw [hbqj]
    exact mul_mem (mem_sup_left hqQ) (mem_sup_right ⟨hj, hjM⟩)
  have hKQJM : K ≤ Q ⊔ (J ⊓ M) :=
    le_of_forall_involution le_rfl (sup_eq_left.mpr (map_subtype_le _)) hKres hKq' hnc
      (le_normalizer_sup hKQ (le_normalizer_inf' hKJ (hKM.trans le_normalizer))) hinv
  have hJQJM : J ≤ Q ⊔ (J ⊓ M) := hJKQ.trans (sup_le hKQJM le_sup_left)
  have hdec : ∀ j ∈ J, ∃ b ∈ J ⊓ M, b⁻¹ * j ∈ Q := by
    intro j hj
    obtain ⟨q, hqQ, y, hy, hjqy⟩ :=
      exists_mul_of_mem_sup_normalizer (inf_le_left.trans hJQ) (hJQJM (inv_mem hj))
    refine ⟨y⁻¹, inv_mem hy, ?_⟩
    have hj' : j = (q * y)⁻¹ := by rw [← hjqy, inv_inv]
    rw [hj', show y⁻¹⁻¹ * (q * y)⁻¹ = q⁻¹ by group]
    exact inv_mem hqQ
  calc J = J ⊓ M ⊔ oddCoreIn J :=
        (sup_oddCoreIn_eq_of_forall_coreActionKernel inf_le_left hJperf hdec).symm
    _ ≤ M := sup_le inf_le_right hOJM

theorem lemma313ResidueInputFor_of_narrow (h315a : Lemma315aInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜) (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G)
    (hnarrow : Lemma313NarrowInputFor 𝒜) : Lemma313ResidueInputFor 𝒜 := by
  intro G _ _ hG N hN hKstar hCb K hK g hKg hβ1 hβ2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hnarrow G hG N hN hKstar hCb K hK g hKg hβ1 hβ2 ?_
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  have hcomps : kStarComponents M = kStarComponents N := kStarComponents_normalizer_eq hbal hG hN
  have hKMc : IsTwoComponentIn K M := by
    have h : K ∈ kStarComponents M := by
      rw [hcomps]
      exact hK
    exact h.1
  have hLg : ∀ L ∈ kStarComponents N, IsTwoComponentIn (conjugate L g) (conjugate M g) := by
    intro L hL
    have h : conjugate L g ∈ kStarComponents (conjugate M g) := by
      rw [kStarComponents_conjugate, hcomps]
      exact ⟨L, hL, rfl⟩
    exact h.1
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hKM : K ≤ M := hKD.trans le_normalizer
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hOK : oddCoreIn K ≤ centralizer (K : Set G) :=
    ((oddCoreIn_le_of_isTwoComponentIn (isTwoComponentIn_of_le hK.1 hKD
      (solomonKStarOf_le N))).trans (h315a G hG N hN)).trans (centralizer_le hKD)
  have hKq' : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hnc := exists_noncentral_involution_coreQuot hq (h𝒜 G hG) hK.1 hK.2
  have hKres : oddResidualIn K = K := oddResidualIn_eq_self_of_isPComponent hK.1.1 hK.1.2
  obtain ⟨s, hsK, hs2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
  have hOM : ∀ L : Subgroup G, K ≤ normalizer (conjugate L g : Set G) →
      oddCoreIn (conjugate L g) ≤ M := fun L hKL =>
    le_of_coprime_of_centralizer hK.2 (hCb K hK) (coprime_card_oddCoreIn _)
      fun k hk => mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hKL hk))
  by_cases hP : ∃ L ∈ kStarComponents N, ¬ K ≤ normalizer (conjugate L g : Set G)
  · exact Or.inl hP
  push Not at hP
  by_cases hN1 : ∃ L ∈ kStarComponents N, K ≤ coreActionKernel (conjugate L g)
  ·
    obtain ⟨L, hL, hKQ⟩ := hN1
    refine Or.inr (Or.inl ⟨L, hL, ?_, K, hK, fun hLK => ?_⟩)
    · exact le_of_mem_coreActionKernel (hLg L hL) hs2 (hKQ hsK) (hCb K hK s hsK hs2)
        (hOM L (hP L hL))
    · have h := commutator_eq_bot_of_le_coreActionKernel (Subgroup.isPerfect_iff.mpr hKperf)
        hOK hKQ hLK
      have hLc : conjugate L g ≤ centralizer (K : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp h
      exact hβ1 K hK s hsK hs2 L hL fun x hx =>
        mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hLc hx)) s hsK).symm
  push Not at hN1
  refine Or.inr (Or.inr fun L hL => ⟨hP L hL, hN1 L hL, fun hKLQ hLKQ => ?_⟩)
  have hLperf : ⁅conjugate L g, conjugate L g⁆ = conjugate L g :=
    UnbalancedCorr.commutator_eq_of_isPComponent (hLg L hL).1 (hLg L hL).2
  have hLM : conjugate L g ≤ M :=
    le_of_mutual_cover hLperf (hP L hL) hKM (hOM L (hP L hL)) (hCb K hK) hKres hKq' hnc hKLQ
      hLKQ
  have hKC : IsTwoComponentIn K (M ⊓ conjugate M g) :=
    ⟨le_inf hKM hKg, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKM hKg)
      inf_le_left hKMc.2⟩
  have hLC : IsTwoComponentIn (conjugate L g) (M ⊓ conjugate M g) :=
    ⟨le_inf hLM (hLg L hL).1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
      (le_inf hLM (hLg L hL).1) inf_le_right (hLg L hL).2⟩
  by_cases hLK : conjugate L g = K
  ·
    obtain ⟨K', hK', hne⟩ := exists_mem_kStarComponents_ne hN K
    obtain ⟨e, heK', he2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK'.2
    have hcomm := commutator_eq_bot_of_mem_kStarComponents h315a hG hN hK' hK hne
    refine hβ1 K' hK' e heK' he2 L hL ?_
    rw [hLK]
    exact fun k hk => mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm heK')) k hk)
  · exact hN1 L hL (GSThmB.B5a.le_coreActionKernel_of_ne hLC.1 hKC.1 hLC.2 hKC.2 hLK)

end CFSG.ComponentClassification.Sol76T13
