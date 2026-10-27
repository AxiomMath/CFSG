module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78MaxAlt
public import CFSG.LocalAnalysis.ComponentClassification.Sol76StrongEmb

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem sup_conjugate_le_solomonKStarOf_top
    (h13 : ∀ N : Subgroup G, IsKBalanced N → solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G))
    {K C : Subgroup G}
    (hKC : IsTwoComponentIn K C) (hKs : K ∈ solomonKStar G) (h3 : 3 ≤ CFSG.pRank 2 K) (g : G)
    (hc : ⁅K, conjugate K g⁆ ≤ oddCoreIn K ⊓ oddCoreIn (conjugate K g)) :
    K ⊔ conjugate K g ≤ solomonKStarOf (⊤ : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := conjugate K g with hK'
  set N := K ⊔ K' with hN
  have hcK : ⁅K, K'⁆ ≤ K := hc.trans (inf_le_left.trans (map_subtype_le _))
  have hcK' : ⁅K, K'⁆ ≤ K' := hc.trans (inf_le_right.trans (map_subtype_le _))
  have hK'N : K' ≤ normalizer (K : Set G) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 := hcK (commutator_mem_commutator (inv_mem hx) hy)
      rw [commutatorElement_def, inv_inv] at h1
      rw [show y * x * y⁻¹ = x * (x⁻¹ * y * x * y⁻¹) by group]
      exact mul_mem hx h1
    · intro hx
      have h1 := hcK (commutator_mem_commutator (inv_mem hx) (inv_mem hy))
      rw [commutatorElement_def, inv_inv, inv_inv] at h1
      rw [show x = y * x * y⁻¹ * ((y * x * y⁻¹)⁻¹ * y⁻¹ * (y * x * y⁻¹) * y) by group]
      exact mul_mem hx h1
  have hKN' : K ≤ normalizer (K' : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h1 := hcK' (commutator_mem_commutator hx hy)
      rw [commutatorElement_def] at h1
      rw [show x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y by group]
      exact mul_mem h1 hy
    · intro hy
      have h1 := hcK' (commutator_mem_commutator (inv_mem hx) hy)
      rw [commutatorElement_def, inv_inv] at h1
      rw [show y = x⁻¹ * (x * y * x⁻¹) * x * (x * y * x⁻¹)⁻¹ * (x * y * x⁻¹) by group]
      exact mul_mem h1 hy
  have hperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hKC.1 hKC.2
  have hKne : K ≠ ⊥ := fun h =>
    Sol78.ne_bot_of_isPComponent' hKC.2 (by rw [h]; exact bot_subgroupOf _)
  have hinv : ∃ b ∈ K, orderOf b = 2 := by
    have h3' := h3
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h3'
    exact exists_orderOf_eq_two_of_pRank (by omega)
  have hne : K ≠ K' := by
    intro h
    obtain ⟨b, hbK, hb2⟩ := hinv
    have hKO : K ≤ oddCoreIn K := by
      calc K = ⁅K, K⁆ := hperf.symm
        _ = ⁅K, K'⁆ := by rw [← h]
        _ ≤ oddCoreIn K := hc.trans inf_le_left
    have h1 := orderOf_dvd_natCard (⟨b, hKO hbK⟩ : oddCoreIn K)
    rw [Subgroup.orderOf_mk, hb2] at h1
    exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn K) h1) (by norm_num)
  have hNK : N ≤ normalizer (K : Set G) := sup_le le_normalizer hK'N
  have hNK' : N ≤ normalizer (K' : Set G) := sup_le hKN' le_normalizer
  have hKN : IsTwoComponentIn K N := Sol78.isTwoComponentIn_of_le_normalizer hKC le_sup_left hNK
  have hK'C := isTwoComponentIn_map (MulAut.conj g⁻¹) hKC
  have hK'N2 : IsTwoComponentIn K' N :=
    Sol78.isTwoComponentIn_of_le_normalizer hK'C le_sup_right hNK'
  have hK's : K' ∈ solomonKStar G := conjugate_mem_solomonKStar hKs g
  have hr3' : 3 ≤ CFSG.pRank 2 K' := by
    rw [hK', conjugate, pRank_map]
    exact h3
  have hK'ker : K' ≤ coreActionKernel K := by
    intro y hy
    refine ⟨hK'N hy, fun k hk => ?_⟩
    have h1 := hc (commutator_mem_commutator (inv_mem hk) (inv_mem hy))
    rw [commutatorElement_def, inv_inv, inv_inv] at h1
    exact (mem_inf.mp h1).1
  set S : Set (Subgroup G) := {L | IsTwoComponentIn L N ∧ L ∈ solomonKStar G} with hSdef
  have hSfin : S.Finite := Set.toFinite S
  set s := hSfin.toFinset with hs
  have hKs' : K ∈ s := hSfin.mem_toFinset.mpr ⟨hKN, hKs⟩
  have hK's' : K' ∈ s := hSfin.mem_toFinset.mpr ⟨hK'N2, hK's⟩
  have hr : 2 ≤ s.card := Finset.one_lt_card.mpr ⟨K, hKs', K', hK's', hne⟩
  set ee := s.equivFin.symm with hee
  set Kf : Fin s.card → Subgroup G := fun i => ((ee i : s) : Subgroup G) with hKf
  have hKfS : ∀ i, Kf i ∈ S := fun i => hSfin.mem_toFinset.mp (ee i).2
  have hHSE : HasStronglyEmbedded K ↔ HasStronglyEmbedded K' :=
    ⟨hasStronglyEmbedded_of_mulEquiv (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective),
      hasStronglyEmbedded_of_mulEquiv (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).symm⟩
  have hbal : IsKBalanced N := by
    refine ⟨s.card, Kf, fun i j hij => ee.injective (Subtype.ext hij), fun L => ⟨fun hL => ?_,
      ?_⟩, hr, fun i j hij => ?_, ?_, ?_⟩
    · refine ⟨ee.symm ⟨L, hSfin.mem_toFinset.mpr hL⟩, ?_⟩
      simp only [hKf, Equiv.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact hKfS i
    · exact commutator_le_oddCoreIn_of_ne (hKfS i).1 (hKfS j).1
        (fun h => hij (ee.injective (Subtype.ext h)))
    ·
      refine ⟨ee.symm ⟨K, hKs'⟩, ?_⟩
      have hKi : Kf (ee.symm ⟨K, hKs'⟩) = K := by simp only [hKf, Equiv.apply_symm_apply]
      rw [hKi]
      exact hr3'.trans (Sol78.pRank_le_of_le (le_inf
        ((le_twoLayerIn_of_isTwoComponentIn hK'N2).trans le_sup_right) hK'ker))
    ·
      by_cases h3s : 3 ≤ s.card
      · exact Or.inl h3s
      · right; right
        have hsub : ({K, K'} : Finset (Subgroup G)) ⊆ s := by
          intro L hL
          rw [Finset.mem_insert, Finset.mem_singleton] at hL
          rcases hL with rfl | rfl
          · exact hKs'
          · exact hK's'
        have hseq : ({K, K'} : Finset (Subgroup G)) = s :=
          Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)
        have hcases : ∀ i, Kf i = K ∨ Kf i = K' := by
          intro i
          have hi : Kf i ∈ ({K, K'} : Finset (Subgroup G)) := by rw [hseq]; exact (ee i).2
          rwa [Finset.mem_insert, Finset.mem_singleton] at hi
        have hrank : ∀ i, 3 ≤ CFSG.pRank 2 ↥(Kf i) := fun i => by
          rcases hcases i with hi | hi <;> rw [hi]
          · exact h3
          · exact hr3'
        have hdisc : HasStronglyEmbedded K → ∀ i, IsTwoDisconnected ↥(Kf i) := by
          intro hK i
          rcases hcases i with hi | hi <;> rw [hi]
          · exact isTwoDisconnected_of_hasStronglyEmbedded hK (by omega)
          · exact isTwoDisconnected_of_hasStronglyEmbedded (hHSE.mp hK) (by omega)
        have hHi : ∀ i, HasStronglyEmbedded ↥(Kf i) → HasStronglyEmbedded K := by
          intro i hi'
          rcases hcases i with hi | hi
          · rwa [hi] at hi'
          · rw [hi] at hi'
            exact hHSE.mpr hi'
        refine ⟨hrank _, hrank _, fun h => ⟨?_, ?_⟩⟩ <;>
          rcases h with h | h <;> exact hdisc (hHi _ h) _
  have hle := h13 N hbal
  have hKle : K ≤ solomonKStarOf N := le_iSup₂_of_le K ⟨hKN, hKs⟩ le_rfl
  have hK'le : K' ≤ solomonKStarOf N := le_iSup₂_of_le K' ⟨hK'N2, hK's⟩ le_rfl
  exact sup_le (hKle.trans hle) (hK'le.trans hle)

end CFSG.ComponentClassification.Sol76
