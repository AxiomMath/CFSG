module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeSelector
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def relativeCentralizer {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    Subgroup G := overgroup ⊓ Subgroup.centralizer (subgroup : Set G)

@[expose] def centralizerProduct {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    Subgroup G := subgroup ⊔ relativeCentralizer overgroup subgroup

@[expose] noncomputable def generatedPCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G) : Subgroup G :=
  ⨆ (subgroup : Subgroup G) (_ : subgroup ≤ overgroup) (_ : threshold ≤ pRank prime subgroup),
    Subgroup.normalizer (subgroup : Set G)

@[expose] noncomputable def aschbacherCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G) : Subgroup G :=
  ⨆ (subgroup : Subgroup G) (_ : subgroup ≤ overgroup) (_ : threshold ≤ pRank prime subgroup)
    (_ : 3 ≤ pRank prime (centralizerProduct overgroup subgroup)),
    Subgroup.normalizer (subgroup : Set G)

@[expose] def AschCoreLocal (G : Type u) [Group G] [Finite G] (threshold : ℕ) : Prop :=
  ∀ prime ∈ aschbacherPrimes G, ∀ sylow : Sylow prime G,
    ∃ localSubgroup : Subgroup G,
      IsTwoLocal localSubgroup ∧ aschbacherCore prime threshold sylow ≤ localSubgroup

theorem relativeCentralizer_le {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    relativeCentralizer overgroup subgroup ≤ overgroup := inf_le_left

theorem relativeCentralizer_le_centralizer {G : Type u} [Group G]
    (overgroup subgroup : Subgroup G) :
    relativeCentralizer overgroup subgroup ≤ Subgroup.centralizer (subgroup : Set G) :=
  inf_le_right

theorem centralizerProduct_le {G : Type u} [Group G] (overgroup subgroup : Subgroup G)
    (hle : subgroup ≤ overgroup) : centralizerProduct overgroup subgroup ≤ overgroup := by
  exact sup_le hle (relativeCentralizer_le overgroup subgroup)

theorem centralizerProduct_coe {G : Type u} [Group G] (overgroup subgroup : Subgroup G) :
    (centralizerProduct overgroup subgroup : Set G) =
      (subgroup : Set G) * (relativeCentralizer overgroup subgroup : Set G) := by
  exact Subgroup.coe_mul_of_right_le_normalizer_left subgroup
    (relativeCentralizer overgroup subgroup)
    ((relativeCentralizer_le_centralizer overgroup subgroup).trans
      (Subgroup.centralizer_le_normalizer (subgroup : Set G)))

theorem centralizerProduct_self {G : Type u} [Group G] (overgroup : Subgroup G) :
    centralizerProduct overgroup overgroup = overgroup := by
  apply le_antisymm (centralizerProduct_le overgroup overgroup le_rfl)
  exact le_sup_left

theorem normalizer_le_generatedPCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup subgroup : Subgroup G)
    (hle : subgroup ≤ overgroup) (hrank : threshold ≤ pRank prime subgroup) :
    Subgroup.normalizer (subgroup : Set G) ≤ generatedPCore prime threshold overgroup := by
  exact le_iSup_of_le subgroup (le_iSup_of_le hle (le_iSup_of_le hrank le_rfl))

theorem generatedPCore_le {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup larger : Subgroup G)
    (hle : ∀ subgroup ≤ overgroup, threshold ≤ pRank prime subgroup →
      Subgroup.normalizer (subgroup : Set G) ≤ larger) :
    generatedPCore prime threshold overgroup ≤ larger := by
  exact iSup_le fun subgroup => iSup_le fun hsubgroup =>
    iSup_le fun hrank => hle subgroup hsubgroup hrank

theorem normalizer_le_aschbacherCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup subgroup : Subgroup G)
    (hle : subgroup ≤ overgroup) (hrank : threshold ≤ pRank prime subgroup)
    (hproduct : 3 ≤ pRank prime (centralizerProduct overgroup subgroup)) :
    Subgroup.normalizer (subgroup : Set G) ≤ aschbacherCore prime threshold overgroup := by
  exact le_iSup_of_le subgroup
    (le_iSup_of_le hle (le_iSup_of_le hrank (le_iSup_of_le hproduct le_rfl)))

theorem aschbacherCore_le {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup larger : Subgroup G)
    (hle : ∀ subgroup ≤ overgroup, threshold ≤ pRank prime subgroup →
      3 ≤ pRank prime (centralizerProduct overgroup subgroup) →
        Subgroup.normalizer (subgroup : Set G) ≤ larger) :
    aschbacherCore prime threshold overgroup ≤ larger := by
  exact iSup_le fun subgroup => iSup_le fun hsubgroup =>
    iSup_le fun hrank => iSup_le fun hproduct => hle subgroup hsubgroup hrank hproduct

theorem generatedPCore_antitone_threshold {G : Type u} [Group G] [Finite G]
    (prime lower upper : ℕ) (overgroup : Subgroup G) (hthreshold : lower ≤ upper) :
    generatedPCore prime upper overgroup ≤ generatedPCore prime lower overgroup := by
  apply generatedPCore_le
  intro subgroup hle hrank
  exact normalizer_le_generatedPCore prime lower overgroup subgroup hle
    (hthreshold.trans hrank)

theorem aschbacherCore_antitone_threshold {G : Type u} [Group G] [Finite G]
    (prime lower upper : ℕ) (overgroup : Subgroup G) (hthreshold : lower ≤ upper) :
    aschbacherCore prime upper overgroup ≤ aschbacherCore prime lower overgroup := by
  apply aschbacherCore_le
  intro subgroup hle hrank hproduct
  exact normalizer_le_aschbacherCore prime lower overgroup subgroup hle
    (hthreshold.trans hrank) hproduct

theorem aschbacherCore_le_generatedPCore {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G) :
    aschbacherCore prime threshold overgroup ≤ generatedPCore prime threshold overgroup := by
  apply aschbacherCore_le
  intro subgroup hle hrank _
  exact normalizer_le_generatedPCore prime threshold overgroup subgroup hle hrank

theorem generatedPCore_mono {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    generatedPCore prime threshold smaller ≤ generatedPCore prime threshold larger := by
  apply generatedPCore_le
  intro subgroup hsubgroup hrank
  exact normalizer_le_generatedPCore prime threshold larger subgroup
    (hsubgroup.trans hle) hrank

theorem generatedPCore_eq_bot_of_rank_lt {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (overgroup : Subgroup G)
    (hrank : pRank prime overgroup < threshold) :
    generatedPCore prime threshold overgroup = ⊥ := by
  apply le_antisymm _ bot_le
  apply generatedPCore_le
  intro subgroup hle hsubgroup
  have hmono := pRank_mono prime hprime hle
  omega

theorem aschbacherCore_eq_bot_of_rank_le_two {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (overgroup : Subgroup G)
    (hrank : pRank prime overgroup ≤ 2) : aschbacherCore prime threshold overgroup = ⊥ := by
  apply le_antisymm _ bot_le
  apply aschbacherCore_le
  intro subgroup hle _ hproduct
  have hmono := pRank_mono prime hprime (centralizerProduct_le overgroup subgroup hle)
  omega

theorem normalizer_le_aschbacherCore_of_rank {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G)
    (hthreshold : threshold ≤ pRank prime overgroup) (hrank : 3 ≤ pRank prime overgroup) :
    Subgroup.normalizer (overgroup : Set G) ≤ aschbacherCore prime threshold overgroup := by
  apply normalizer_le_aschbacherCore prime threshold overgroup overgroup le_rfl hthreshold
  simpa only [centralizerProduct_self] using hrank

theorem overgroup_le_aschbacherCore_of_rank {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G)
    (hthreshold : threshold ≤ pRank prime overgroup) (hrank : 3 ≤ pRank prime overgroup) :
    overgroup ≤ aschbacherCore prime threshold overgroup := by
  exact Subgroup.le_normalizer.trans
    (normalizer_le_aschbacherCore_of_rank prime threshold overgroup hthreshold hrank)

theorem aschbacherCore_not_local_of_rank_gt {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) (threshold : ℕ)
    (hthreshold : threshold ≤ 3) (overgroup localSubgroup : Subgroup G)
    (hlocal : IsTwoLocal localSubgroup) (hrank : evenRank G < pRank prime overgroup)
    (heven : 3 ≤ evenRank G) : ¬aschbacherCore prime threshold overgroup ≤ localSubgroup := by
  intro hle
  have hthree : 3 ≤ pRank prime overgroup := heven.trans (Nat.le_of_lt hrank)
  have hcontain := (overgroup_le_aschbacherCore_of_rank prime threshold overgroup
    (hthreshold.trans hthree) hthree).trans hle
  have hmono := pRank_mono prime hprime hcontain
  have hbound := pRank_le_evenRank prime hprime hodd localSubgroup hlocal
  exact (Nat.not_lt_of_ge (hmono.trans hbound)) hrank

theorem AschCoreLocal_antitone_threshold (G : Type u) [Group G] [Finite G]
    (lower upper : ℕ) (hthreshold : lower ≤ upper) (hlocal : AschCoreLocal G lower) :
    AschCoreLocal G upper := by
  unfold AschCoreLocal at hlocal ⊢
  intro prime hselected sylow
  obtain ⟨localSubgroup, htwoLocal, hle⟩ := hlocal prime hselected sylow
  have hcore : aschbacherCore prime upper (sylow : Subgroup G) ≤
      aschbacherCore prime lower (sylow : Subgroup G) :=
    aschbacherCore_antitone_threshold prime lower upper (sylow : Subgroup G) hthreshold
  exact ⟨localSubgroup, htwoLocal,
    hcore.trans hle⟩

theorem selected_sylow_rank_ge_three (G : Type u) [Group G] [Finite G]
    (heven : evenRank G = 3) (prime : ℕ) (hselected : prime ∈ aschbacherPrimes G)
    (sylow : Sylow prime G) : 3 ≤ pRank prime (sylow : Subgroup G) := by
  obtain ⟨hprime, _, _, hrank⟩ := aschbacherPrimes_mem_rank_three G heven prime hselected
  calc
    3 = twoLocalRank prime G := hrank.symm
    _ ≤ pRank prime (⊤ : Subgroup G) := twoLocalRank_le_pRank prime hprime G
    _ = pRank prime (sylow : Subgroup G) := (pRank_eq_sylow prime hprime sylow).symm

theorem selected_sylow_normalizer_le_core (G : Type u) [Group G] [Finite G]
    (heven : evenRank G = 3) (prime : ℕ) (hselected : prime ∈ aschbacherPrimes G)
    (threshold : ℕ) (hthreshold : threshold ≤ 3) (sylow : Sylow prime G) :
    Subgroup.normalizer (sylow : Set G) ≤ aschbacherCore prime threshold sylow := by
  have hrank := selected_sylow_rank_ge_three G heven prime hselected sylow
  exact normalizer_le_aschbacherCore_of_rank prime threshold (sylow : Subgroup G)
    (hthreshold.trans hrank) hrank

theorem selected_global_rank_eq_three_of_core_local (G : Type u) [Group G] [Finite G]
    (heven : evenRank G = 3) (prime : ℕ) (hselected : prime ∈ aschbacherPrimes G)
    (threshold : ℕ) (hthreshold : threshold ≤ 3) (sylow : Sylow prime G)
    (localSubgroup : Subgroup G) (hlocal : IsTwoLocal localSubgroup)
    (hcore : aschbacherCore prime threshold sylow ≤ localSubgroup) :
    pRank prime (⊤ : Subgroup G) = 3 := by
  obtain ⟨hprime, hodd, _, _⟩ := aschbacherPrimes_mem_rank_three G heven prime hselected
  have hrank := selected_sylow_rank_ge_three G heven prime hselected sylow
  have hcontain : (sylow : Subgroup G) ≤ localSubgroup :=
    (overgroup_le_aschbacherCore_of_rank prime threshold (sylow : Subgroup G)
      (hthreshold.trans hrank) hrank).trans hcore
  have hmono := pRank_mono prime hprime hcontain
  have hbound := pRank_le_evenRank prime hprime hodd localSubgroup hlocal
  rw [pRank_eq_sylow prime hprime sylow] at hrank hmono
  exact le_antisymm (heven ▸ hmono.trans hbound) hrank

theorem AschCoreLocal_selected_rank_three (G : Type u) [Group G] [Finite G]
    (heven : evenRank G = 3) (threshold : ℕ) (hthreshold : threshold ≤ 3)
    (hlocal : AschCoreLocal G threshold) (prime : ℕ) (hselected : prime ∈ aschbacherPrimes G) :
    pRank prime (⊤ : Subgroup G) = 3 := by
  classical
  let sylow : Sylow prime G := Classical.choice inferInstance
  obtain ⟨localSubgroup, htwoLocal, hcore⟩ := hlocal prime hselected sylow
  change aschbacherCore prime threshold (sylow : Subgroup G) ≤ localSubgroup at hcore
  exact selected_global_rank_eq_three_of_core_local G heven prime hselected threshold
    hthreshold sylow localSubgroup htwoLocal hcore

theorem AschCoreLocal_core_proper (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ first second : G, first * second ≠ second * first)
    (threshold : ℕ) (hlocal : AschCoreLocal G threshold) (prime : ℕ)
    (hselected : prime ∈ aschbacherPrimes G) (sylow : Sylow prime G) :
    aschbacherCore prime threshold (sylow : Subgroup G) ≠ ⊤ := by
  obtain ⟨localSubgroup, htwoLocal, hcore⟩ := hlocal prime hselected sylow
  intro htop
  exact twoLocal_ne_top hnonab localSubgroup htwoLocal
    (top_le_iff.mp (htop ▸ hcore))

end CFSG.RankThreeEvenClassification.Helpers
