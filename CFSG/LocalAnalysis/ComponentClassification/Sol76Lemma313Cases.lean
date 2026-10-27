module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma313Star
public import CFSG.LocalAnalysis.ComponentClassification.Sol76ChoiceConj

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]
variable {𝒜 : Thm13Ambient}

theorem eq_of_le_oddCoreIn_sup {Q K Y : Subgroup G} (hQ : IsTwoComponentIn Q Y)
    (hK : IsTwoComponentIn K Y) (hQK : Q ≤ oddCoreIn Y ⊔ K) (hQinv : ∃ b ∈ Q, orderOf b = 2) :
    Q = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : CatalogueBPrimeJoin.primeResidual 2 ↥Q = ⊤ :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Q Y hQ.1).mp hQ.2).2.1
  have h1 := Sol78.le_oPrimeResidualOf hQK hres
  rw [show oddCoreIn Y = GH74.GLS.pPrimeCoreOf 2 Y from rfl,
    Sol78.oPrimeResidualOf_core_sup_eq hK.1 hK.2] at h1
  by_contra hne
  have h2 := FooteLit.commutator_le_oddCoreIn_of_ne hQ hK hne
  have hQp : ⁅Q, Q⁆ = Q := UnbalancedCorr.commutator_eq_of_isPComponent hQ.1 hQ.2
  have h3 : Q ≤ oddCoreIn Y := by
    rw [← hQp]
    exact (commutator_mono le_rfl h1).trans h2
  obtain ⟨b, hbQ, hb2⟩ := hQinv
  have h4 := orderOf_dvd_natCard (⟨b, h3 hbQ⟩ : oddCoreIn Y)
  rw [Subgroup.orderOf_mk, hb2] at h4
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn Y) h4) (by norm_num)

theorem mem_kStarComponents_of_le_centralizer (h33 : Lemma33CentralInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N₁ N₂ : Subgroup G}
    (hN₁ : IsSolomonChoice N₁) (hN₂ : IsSolomonChoice N₂) {K K' : Subgroup G}
    (hK : K ∈ kStarComponents N₁) (hK' : K' ∈ kStarComponents N₂) {s : G} (hsK' : s ∈ K')
    (hs2 : orderOf s = 2) (hKs : K ≤ centralizer ({s} : Set G)) : K ∈ kStarComponents N₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({s} : Set G) with hC
  set D₁ := solomonKStarOf N₁ with hD₁
  set M₁ := normalizer (D₁ : Set G) with hM₁
  have hLM : twoLayerIn C ≤ M₁ :=
    twoLayerIn_centralizer_le_normalizer h33 h32 h315a h315c hbal hprod hG hN₁ hK hs2 hKs
  have hT2 := kStarComponents_centralizer h32 h315a h315c hbal hprod hG hN₂ hK' hsK' hs2
  have hKKC : K ≤ solomonKStarOf C := le_solomonKStarOf_centralizer hK.1 hK.2
    (isPGroup_zpowers_of_orderOf_eq_two hs2) (ne_one_of_orderOf_eq_two hs2) hKs
  have hKL : K ≤ twoLayerIn C := hKKC.trans (solomonKStarOf_le_twoLayerIn C)
  obtain ⟨Q, hQ, hmove⟩ :=
    exists_not_le_coreActionKernel hK.1 hKKC (exists_orderOf_eq_two_of_mem_solomonKStar hK.2)
  have hQN₂ : Q ∈ kStarComponents N₂ := by
    have h : Q ∈ kStarComponents C := hQ
    rw [hT2] at h
    exact h.1
  have hCb₁ := (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N₁ hN₁).2
  obtain ⟨b, hbK, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
  have hks : ∀ k ∈ K, k * s = s * k := fun k hk => mem_centralizer_singleton_iff.mp (hKs hk)
  have hsN : s ∈ M₁ := hCb₁ K hK b hbK hb2 (mem_centralizer_singleton_iff.mpr (hks b hbK).symm)
  have h3 := h33 G hG N₁ hN₁ K hK s hsN hs2 hKs
  have hQle : Q ≤ oddCoreIn (twoLayerIn C) ⊔ K :=
    (le_conjClosure_of_not_le_coreActionKernel hQ.1 hKL hmove).trans h3
  have hLC : twoLayerIn C ≤ C := map_subtype_le _
  have hLY : twoLayerIn C ≤ M₁ ⊓ C := le_inf hLM hLC
  have hOL : oddCoreIn (twoLayerIn C) ≤ twoLayerIn C := map_subtype_le _
  have hOY : oddCoreIn (twoLayerIn C) ≤ oddCoreIn (M₁ ⊓ C) := by
    have hn : M₁ ⊓ C ≤ normalizer (oddCoreIn (twoLayerIn C) : Set G) := fun y hy =>
      mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (le_normalizer_twoLayerIn C hy.2))
    have h := inf_le_oddCoreIn (coprime_card_oddCoreIn (twoLayerIn C)) hn
    rwa [inf_eq_left.mpr (hOL.trans hLY)] at h
  have hKD₁ : K ≤ D₁ := le_iSup₂_of_le K hK le_rfl
  have hD₁M₁ : D₁ ≤ M₁ := le_normalizer
  have hKM₁ : IsTwoComponentIn K M₁ := by
    have hKD : IsTwoComponentIn K D₁ := isTwoComponentIn_of_le hK.1 hKD₁ (solomonKStarOf_le N₁)
    have hDn : (D₁.subgroupOf M₁).IsSubnormal :=
      Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer hD₁M₁).mpr le_rfl)
    exact ⟨hKD₁.trans hD₁M₁, GrSLit.isPComponent_subgroupOf_of_isSubnormal hKD₁ hD₁M₁ hDn hKD.2⟩
  have hKY : IsTwoComponentIn K (M₁ ⊓ C) :=
    isTwoComponentIn_of_le hKM₁ (le_inf (hKD₁.trans hD₁M₁) hKs) inf_le_left
  have hQY : IsTwoComponentIn Q (M₁ ⊓ C) :=
    isTwoComponentIn_of_le hQ.1 (hQle.trans (sup_le (hOL.trans hLY) hKY.1)) inf_le_right
  have hQK := eq_of_le_oddCoreIn_sup hQY hKY (hQle.trans (sup_le_sup_right hOY K))
    (exists_orderOf_eq_two_of_mem_solomonKStar hQ.2)
  rw [← hQK]
  exact hQN₂

theorem kStarComponents_eq_of_mem (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N₁ N₂ : Subgroup G} (hN₁ : IsSolomonChoice N₁)
    (hN₂ : IsSolomonChoice N₂) {K : Subgroup G} (hK₁ : K ∈ kStarComponents N₁)
    (hK₂ : K ∈ kStarComponents N₂) : kStarComponents N₁ = kStarComponents N₂ := by
  obtain ⟨w, hwK, hw2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK₁.2
  have e₁ := kStarComponents_centralizer h32 h315a h315c hbal hprod hG hN₁ hK₁ hwK hw2
  have e₂ := kStarComponents_centralizer h32 h315a h315c hbal hprod hG hN₂ hK₂ hwK hw2
  have hsplit : ∀ {N : Subgroup G}, IsSolomonChoice N → K ∈ kStarComponents N →
      ∀ J ∈ kStarComponents N, J ≠ K → J ≤ centralizer ({w} : Set G) := by
    intro N hN hK J hJ hne
    have hc := commutator_eq_bot_of_mem_kStarComponents h315a hG hN hJ hK hne
    exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hwK))
  ext J
  by_cases hJK : J = K
  · rw [hJK]
    exact ⟨fun _ => hK₂, fun _ => hK₁⟩
  · constructor
    · intro hJ
      have h1 : J ∈ {J | J ∈ kStarComponents N₁ ∧ J ≤ centralizer ({w} : Set G)} :=
        ⟨hJ, hsplit hN₁ hK₁ J hJ hJK⟩
      rw [← e₁, e₂] at h1
      exact h1.1
    · intro hJ
      have h1 : J ∈ {J | J ∈ kStarComponents N₂ ∧ J ≤ centralizer ({w} : Set G)} :=
        ⟨hJ, hsplit hN₂ hK₂ J hJ hJK⟩
      rw [← e₂, e₁] at h1
      exact h1.1

theorem mem_normalizer_of_caseAlpha (h33 : Lemma33CentralInputFor 𝒜) (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {g : G}
    (h : (∃ K ∈ kStarComponents N, ∃ s ∈ K, orderOf s = 2 ∧
          ∃ L ∈ kStarComponents N, conjugate L g ≤ centralizer ({s} : Set G)) ∨
        (∃ L ∈ kStarComponents N, ∃ s ∈ conjugate L g, orderOf s = 2 ∧
          ∃ K ∈ kStarComponents N, K ≤ centralizer ({s} : Set G))) :
    g ∈ normalizer (solomonKStarOf N : Set G) := by
  have hNg := isSolomonChoice_conjugate hN g
  have hconj : ∀ L ∈ kStarComponents N, conjugate L g ∈ kStarComponents (conjugate N g) := by
    intro L hL
    rw [kStarComponents_conjugate]
    exact ⟨L, hL, rfl⟩
  have hkey : kStarComponents N = kStarComponents (conjugate N g) := by
    rcases h with ⟨K, hK, s, hsK, hs2, L, hL, hLs⟩ | ⟨L, hL, s, hsL, hs2, K, hK, hKs⟩
    · have hLgN := mem_kStarComponents_of_le_centralizer h33 h32 h315a h315c hbal hprod hG hNg hN
        (hconj L hL) hK hsK hs2 hLs
      exact kStarComponents_eq_of_mem h32 h315a h315c hbal hprod hG hN hNg hLgN (hconj L hL)
    · have hKNg := mem_kStarComponents_of_le_centralizer h33 h32 h315a h315c hbal hprod hG hN hNg
        hK (hconj L hL) hsL hs2 hKs
      exact kStarComponents_eq_of_mem h32 h315a h315c hbal hprod hG hN hNg hK hKNg
  have hD : conjugate (solomonKStarOf N) g = solomonKStarOf N := by
    rw [conjugate_solomonKStarOf, solomonKStarOf_eq_sSup (conjugate N g), ← hkey,
      ← solomonKStarOf_eq_sSup N]
  have hginv : g⁻¹ ∈ normalizer (solomonKStarOf N : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr hD
  simpa using inv_mem hginv

end CFSG.ComponentClassification.Sol76
