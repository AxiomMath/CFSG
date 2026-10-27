module

public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G] {J : Subgroup G}

omit [Finite G] in
theorem not_le_of_le_commutator_eq_bot {K A B : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple K)
    (hKA : K ≤ A) (hKB : K ≤ B) (hAB : ⁅A, B⁆ = ⊥) : False :=
  not_le_centralizer_self_of_isQuasisimple hK
    (hKA.trans ((commutator_eq_bot_iff_le_centralizer.1 hAB).trans (centralizer_le hKB)))

theorem eq_of_isComponentOf_of_le {K L₁ L₂ N : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple K)
    (hL₁ : CFSG.Assembly.IsComponentOf L₁ N) (hL₂ : CFSG.Assembly.IsComponentOf L₂ N)
    (hK₁ : K ≤ L₁) (hK₂ : K ≤ L₂) : L₁ = L₂ :=
  (isComponentOf_eq_or_commute hL₁ hL₂).resolve_right fun h =>
    not_le_of_le_commutator_eq_bot hK hK₁ hK₂ h

theorem eq_of_isComponentOf_le {K L C : Subgroup G} (hK : CFSG.Assembly.IsComponentOf K C)
    (hL : CFSG.Assembly.IsComponentOf L C) (hKL : K ≤ L) : K = L :=
  (isComponentOf_eq_or_commute hK hL).resolve_right fun h =>
    not_le_of_le_commutator_eq_bot hK.2.2 le_rfl hKL h

omit [Finite G] in
theorem isComponentOf_conjSub_of_mem {L N : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L N)
    {n : G} (hn : n ∈ N) : CFSG.Assembly.IsComponentOf (conjSub n L) N := by
  have := isComponentOf_map_conj hL n
  rwa [show N.map (MulAut.conj n).toMonoidHom = N from
    conjSub_eq_of_mem_normalizer (le_normalizer hn)] at this

theorem commuting_block_overgroup_single_component_dichotomy
    (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {N : Subgroup G}
    (hHN : normalizer (blockGroup J : Set G) ≤ N)
    (hME : blockGroup J ≤ (CFSG.layer N).map N.subtype) :
    (∀ K ∈ block J, ∃! L : Subgroup G, CFSG.Assembly.IsComponentOf L N ∧ K ≤ L) ∧
      ((∃ K₁ ∈ block J, ∃ K₂ ∈ block J, ∃ L₁ L₂ : Subgroup G,
          CFSG.Assembly.IsComponentOf L₁ N ∧ K₁ ≤ L₁ ∧ CFSG.Assembly.IsComponentOf L₂ N ∧
            K₂ ≤ L₂ ∧ L₁ ≠ L₂) → N = normalizer (blockGroup J : Set G)) ∧
      (normalizer (blockGroup J : Set G) < N →
        ∃ L : Subgroup G, (CFSG.Assembly.IsComponentOf L N ∧ blockGroup J ≤ L) ∧
          (∀ L' : Subgroup G, CFSG.Assembly.IsComponentOf L' N → blockGroup J ≤ L' → L' = L) ∧
          (L.subgroupOf N).Normal ∧ blockGroup J < L ∧
          ¬ L ≤ normalizer (blockGroup J : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := blockGroup J with hMdef
  set H := normalizer (M : Set G) with hHdef
  have hMH : M ≤ H := le_normalizer
  have hKN : ∀ K ∈ block J, K ≤ N := fun K hK => ((le_blockGroup hK).trans hMH).trans hHN
  have hKq : ∀ K ∈ block J, CFSG.Assembly.IsQuasisimple K := fun K hK =>
    isQuasisimple_of_isConjOf hq hK.1
  have hKu : ∀ K ∈ block J, IsUniversalComponent K := fun K hK => by
    obtain ⟨c, rfl⟩ := hK.1
    exact isUniversalComponent_conjSub hJ c
  have hinv : ∀ K ∈ block J, ∃ t ∈ K, orderOf t = 2 := fun K hK => by
    obtain ⟨g, rfl⟩ := hK.1
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := conjSub g J) 2
      (even_iff_two_dvd.1 (by rwa [card_conjSub]))
    exact ⟨k, k.2, by rw [Subgroup.orderOf_coe, hk]⟩
  have hcomp_t : ∀ K ∈ block J, ∀ K₁ ∈ block J, K ≠ K₁ → ∀ t ∈ K₁, orderOf t = 2 →
      CFSG.Assembly.IsComponentOf K (centralizer ({t} : Set G)) ∧
        centralizer ({t} : Set G) ≤ H := by
    intro K hK K₁ hK₁ hne t htK₁ ht
    have h := (commRel_of_mem_block hJ heven hK hK₁).resolve_left hne
    have htc : t ∈ centralizer (K : Set G) := by
      rw [mem_centralizer_iff]
      intro k hk
      exact commute_of_commutator_eq_bot' h hk htK₁
    exact ⟨hKu K hK t htc ht, centralizer_le_normalizer_blockGroup_of_mem hJ heven hΔ hK₁ htK₁ ht⟩
  have hexists : ∀ K ∈ block J, ∃ L : Subgroup G, CFSG.Assembly.IsComponentOf L N ∧ K ≤ L := by
    intro K hK
    obtain ⟨K₁, hK₁, hne⟩ := hΔ.exists_ne K
    obtain ⟨t, htK₁, ht⟩ := hinv K₁ hK₁
    obtain ⟨hcomp, hCH⟩ := hcomp_t K hK K₁ hK₁ hne.symm t htK₁ ht
    have htN : t ∈ N := hKN K₁ hK₁ htK₁
    set t' : N := ⟨t, htN⟩ with ht'def
    have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk, ht]
    have hcompN : CFSG.Assembly.IsComponentOf K (N ⊓ centralizer ({t} : Set G)) :=
      isComponentOf_of_le hcomp (le_inf (hKN K hK) hcomp.1) inf_le_right
    rw [← map_subtype_centralizer_singleton N t',
      ← Subgroup.map_subgroupOf_eq_of_le (hKN K hK)] at hcompN
    have hcompN' := (isComponentOf_map_iff N.subtype_injective).1 hcompN
    have hlayer : ∀ g ∈ M, ∀ hg : g ∈ N, (⟨g, hg⟩ : N) ∈ CFSG.layer N := by
      intro g hgM hg
      obtain ⟨n, hn, hng⟩ := hME hgM
      have : n = ⟨g, hg⟩ := Subtype.ext hng
      rw [← this]
      exact hn
    have hKE : K.subgroupOf N ≤ CFSG.layer N := fun k hk =>
      hlayer _ (le_blockGroup hK (Subgroup.mem_subgroupOf.1 hk)) _
    have htE : t' ∈ CFSG.layer N := hlayer t (le_blockGroup hK₁ htK₁) htN
    obtain ⟨L', hL', hcase⟩ := involution_layer_component_orbit_location ht' hcompN' hKE
    have hLt : conjSub t'⁻¹ L' = L' :=
      conjSub_eq_of_mem_normalizer (inv_mem (CFSG.LocalCores.layer_le_normalizer hL' htE))
    rcases hcase with ⟨-, hJL⟩ | ⟨hne', -⟩
    · refine ⟨L'.map N.subtype, ?_, ?_⟩
      · rw [isComponentOf_iff_isComponent_subgroupOf (Subgroup.map_subtype_le L'),
          Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
        exact hL'
      · intro k hk
        exact ⟨⟨k, hKN K hK hk⟩, (Subgroup.mem_inf.1 (hJL.1 (Subgroup.mem_subgroupOf.2 hk))).1, rfl⟩
    · exact absurd hLt hne'
  have huniq : ∀ K ∈ block J, ∀ L₁ L₂ : Subgroup G, CFSG.Assembly.IsComponentOf L₁ N →
      K ≤ L₁ → CFSG.Assembly.IsComponentOf L₂ N → K ≤ L₂ → L₁ = L₂ :=
    fun K hK L₁ L₂ h₁ hK₁ h₂ hK₂ => eq_of_isComponentOf_of_le (hKq K hK) h₁ h₂ hK₁ hK₂
  have hb : (∃ K₁ ∈ block J, ∃ K₂ ∈ block J, ∃ L₁ L₂ : Subgroup G,
      CFSG.Assembly.IsComponentOf L₁ N ∧ K₁ ≤ L₁ ∧ CFSG.Assembly.IsComponentOf L₂ N ∧
        K₂ ≤ L₂ ∧ L₁ ≠ L₂) → N = H := by
    rintro ⟨K₁, hK₁, K₂, hK₂, L₁, L₂, hL₁, hKL₁, hL₂, hKL₂, hL₁₂⟩
    have hall : ∀ K ∈ block J, CFSG.Assembly.IsComponentOf K N := by
      intro K hK
      obtain ⟨LK, hLK, hKLK⟩ := hexists K hK
      obtain ⟨K', hK', L', hL', hK'L', hne⟩ : ∃ K' ∈ block J, ∃ L' : Subgroup G,
          CFSG.Assembly.IsComponentOf L' N ∧ K' ≤ L' ∧ L' ≠ LK := by
        by_cases h : L₁ = LK
        · exact ⟨K₂, hK₂, L₂, hL₂, hKL₂, fun h' => hL₁₂ (h.trans h'.symm)⟩
        · exact ⟨K₁, hK₁, L₁, hL₁, hKL₁, h⟩
      have hKK' : K ≠ K' := by
        rintro rfl
        exact hne (huniq K hK L' LK hL' hK'L' hLK hKLK)
      obtain ⟨t, htK', ht⟩ := hinv K' hK'
      obtain ⟨hcompK, hCH⟩ := hcomp_t K hK K' hK' hKK' t htK' ht
      have hcomm : ⁅LK, L'⁆ = ⊥ :=
        (isComponentOf_eq_or_commute hLK hL').resolve_left fun h => hne h.symm
      have hLKC : LK ≤ centralizer ({t} : Set G) := by
        intro l hl
        rw [mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff.1 hw]
        exact (commute_of_commutator_eq_bot' hcomm hl (hK'L' htK')).symm
      have hLKcomp : CFSG.Assembly.IsComponentOf LK (centralizer ({t} : Set G)) :=
        isComponentOf_of_le hLK hLKC (hCH.trans hHN)
      rw [eq_of_isComponentOf_le hcompK hLKcomp hKLK]
      exact hLK
    refine le_antisymm (fun n hn => ?_) hHN
    have hJn := isComponentOf_conjSub_of_mem (hall J mem_block_self) hn
    have hrel : CommRel J (conjSub n J) :=
      isComponentOf_eq_or_commute (hall J mem_block_self) hJn
    exact mem_normalizer_blockGroup hJ heven mem_block_self ⟨⟨n, rfl⟩, hrel⟩
  refine ⟨fun K hK => ?_, hb, fun hHlt => ?_⟩
  · obtain ⟨L, hL, hKL⟩ := hexists K hK
    exact ⟨L, ⟨hL, hKL⟩, fun L' hL' => huniq K hK L' L hL'.1 hL'.2 hL hKL⟩
  ·
    obtain ⟨L, hL, hJL⟩ := hexists J mem_block_self
    have hall : ∀ K ∈ block J, K ≤ L := by
      intro K hK
      obtain ⟨LK, hLK, hKLK⟩ := hexists K hK
      by_contra hKL
      have hne : LK ≠ L := fun h => hKL (h ▸ hKLK)
      exact hHlt.ne (hb ⟨K, hK, J, mem_block_self, LK, L, hLK, hKLK, hL, hJL, hne⟩).symm
    have hML : M ≤ L := iSup₂_le fun K hK => hall K hK
    have hLuniq : ∀ L' : Subgroup G, CFSG.Assembly.IsComponentOf L' N → M ≤ L' → L' = L :=
      fun L' hL' hML' => huniq J mem_block_self L' L hL' ((le_blockGroup mem_block_self).trans hML')
        hL hJL
    have hconj : ∀ n ∈ N, conjSub n L = L := by
      intro n hn
      by_contra hne
      have hLn := isComponentOf_conjSub_of_mem hL hn
      have hcomm : ⁅L, conjSub n L⁆ = ⊥ :=
        (isComponentOf_eq_or_commute hL hLn).resolve_left fun h => hne h.symm
      have hJn : conjSub n J ≤ conjSub n L := map_mono hJL
      have hrel : CommRel J (conjSub n J) := Or.inr (eq_bot_iff.2
        (hcomm ▸ commutator_mono hJL hJn))
      have hJnΔ : conjSub n J ∈ block J := ⟨⟨n, rfl⟩, hrel⟩
      exact not_le_of_le_commutator_eq_bot (hKq _ hJnΔ)
        ((le_blockGroup hJnΔ).trans hML) hJn hcomm
    have hLn : (L.subgroupOf N).Normal := by
      refine normal_subgroupOf_of_le_normalizer fun n hn => ?_
      exact mem_normalizer_of_conjSub_le (le_of_eq (hconj n hn))
        (le_of_eq (hconj n⁻¹ (inv_mem hn)))
    have hLH : ¬ L ≤ H := by
      intro hLH
      have hLcompH : CFSG.Assembly.IsComponentOf L H := isComponentOf_of_le hL hLH hHN
      obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
      have h₁ := eq_of_isComponentOf_le (isComponentOf_normalizer_blockGroup hq hJ heven hK₁)
        hLcompH (hall K₁ hK₁)
      have h₂ := eq_of_isComponentOf_le (isComponentOf_normalizer_blockGroup hq hJ heven hK₂)
        hLcompH (hall K₂ hK₂)
      exact hne (h₁.trans h₂.symm)
    exact ⟨L, ⟨hL, hML⟩, hLuniq, hLn, lt_of_le_of_ne hML fun h => hLH (h ▸ hMH), hLH⟩

end CFSG.LocalAnalysis.ComponentInitial
