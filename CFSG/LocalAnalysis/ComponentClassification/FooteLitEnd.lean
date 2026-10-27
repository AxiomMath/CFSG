module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndRankOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndRankTwo

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def FooteTheoremTwoTwo : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (Q : Subgroup G), TightlyEmbedded Q →
    OddNormalizerOverlaps Q → Q.Normal ∨ Open.fusionStronglyEmbedded
      ((normalizer (Q : Set G)).subgroupOf (normalClosure (Q : Set G)))

@[expose] def FooteBenderSolvable : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (M : Subgroup K), Open.fusionStronglyEmbedded M →
    2 ≤ Open.twoRank K → Group.IsSolvable M

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_even_inf_normalizer_of_tight
    {C : Subgroup G} (hsimple : IsSimpleGroup G)
    (hCtight : TightlyEmbedded C)
    (hE8 : ∃ E : Subgroup G, E ≤ C ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 8)
    (hNproper : Subgroup.normalizer (C : Set G) ≠ ⊤)
    (hNsolv : ¬ Group.IsSolvable ↥(Subgroup.normalizer (C : Set G)))
    (hT22 : FooteTheoremTwoTwo) (hBen : FooteBenderSolvable) :
    ∃ g : G, g ∉ Subgroup.normalizer (C : Set G) ∧
      Even (Nat.card ↥(rightConjugate C g ⊓ Subgroup.normalizer (C : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEC, hEel, hE8⟩ := hE8
  have hE2 : ∀ x ∈ E, x ^ 2 = 1 := hEel.2
  by_contra hall
  push Not at hall
  have hodd : OddNormalizerOverlaps C := by
    intro g hg
    have h1 := hall g hg
    rwa [Nat.not_even_iff_odd] at h1
  rcases hT22 C hCtight hodd with hnorm | hse
  ·
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hnorm with h1 | h1
    · exfalso
      have h2 := Subgroup.card_le_of_le hEC
      rw [h1, card_bot, hE8] at h2
      omega
    · apply hNproper
      rw [h1]
      exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
  ·
    have hC1 : C ≠ ⊥ := fun h1 => by
      have h2 := Subgroup.card_le_of_le hEC
      rw [h1, card_bot, hE8] at h2
      omega
    have hcl : normalClosure (C : Set G) = ⊤ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ normalClosure_normal with h1 | h1
      · exfalso
        apply hC1
        rw [eq_bot_iff, ← h1]
        exact subset_normalClosure
      · exact h1
    set K := normalClosure (C : Set G) with hKdef
    have hrank : 2 ≤ Open.twoRank ↥K := by
      have hEK : E ≤ K := hEC.trans subset_normalClosure
      have hel : Open.IsElemAbelian 2 (E.subgroupOf K) := by
        refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
        · exact commute_of_sq_eq_one hE2 a.2 b.2
        · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
          exact hE2 _ ha
      have hcard : Nat.card (E.subgroupOf K) = 2 ^ 3 := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hEK).symm.toEquiv, hE8]
        norm_num
      have h3 := SectionRank.le_pRank one_lt_two (le_top : E.subgroupOf K ≤ ⊤) hel hcard
      exact le_trans (by norm_num) h3
    have hsolv := hBen ↥K _ hse hrank
    have hNsolv' : Group.IsSolvable ↥(Subgroup.normalizer (C : Set G)) := by
      have e : ↥((Subgroup.normalizer (C : Set G)).subgroupOf K) ≃*
          ↥(Subgroup.normalizer (C : Set G)) :=
        subgroupOfEquivOfLe (hcl ▸ le_top)
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact hNsolv hNsolv'

theorem exists_even_inf_normalizer (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hT22 : FooteTheoremTwoTwo)
    (hBen : FooteBenderSolvable) {M : Subgroup G} (hM : IsFooteM L M) (hne : FooteNoEscape M) :
    ∃ g : G, g ∉ normalizer (M : Set G) ∧ Even (Nat.card ↥(rightConjugate (coreActionKernel M) g ⊓
      normalizer (coreActionKernel M : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.simple
  have hNC := normalizer_coreActionKernel_eq h h47 hST hM
  have htight := tightlyEmbedded_coreActionKernel h h47 hST hM hne
  obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
  have hNproper : normalizer (coreActionKernel M : Set G) ≠ ⊤ := by
    intro htop
    have hCnorm : (coreActionKernel M).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hCnorm with hbot | htopC
    · have h2 := Subgroup.card_le_of_le hEC
      rw [hbot, card_bot, hE8] at h2
      omega
    · apply hM.not_odd h
      have h2 : M ≤ oddCoreIn M := fun x hx =>
        hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hx, htopC ▸ mem_top x⟩)
      have h3 : oddCoreIn M = M := le_antisymm (map_subtype_le _) h2
      rw [← h3]
      exact odd_card_oddCoreIn M
  have hMN : M ≤ normalizer (coreActionKernel M : Set G) := fun m hm =>
    normalizer_le_normalizer_coreActionKernel M (le_normalizer hm)
  have hNsolv : ¬ Group.IsSolvable ↥(normalizer (coreActionKernel M : Set G)) := by
    intro hN
    have hMsolv : Group.IsSolvable ↥M :=
      @Group.isSolvable_of_isSolvable_injective ↥M
        ↥(normalizer (coreActionKernel M : Set G)) _ _
        (Subgroup.inclusion hMN) (Subgroup.inclusion_injective hMN) hN
    have hqsolv : Group.IsSolvable (M ⧸ pPrimeCore 2 M) :=
      @Group.isSolvable_of_surjective ↥M (M ⧸ pPrimeCore 2 M) _ _
        (QuotientGroup.mk' (pPrimeCore 2 M))
        (QuotientGroup.mk'_surjective (pPrimeCore 2 M)) hMsolv
    obtain ⟨hsimp, -⟩ := hM.quotient h
    obtain ⟨a, b, hab⟩ := hM.exists_mul_ne h
    exact hab ((@IsSimpleGroup.comm_iff_isSolvable _ _ hsimp).mpr hqsolv a b)
  obtain ⟨g, hgC, heven⟩ := exists_even_inf_normalizer_of_tight hs htight
    ⟨E, hEC, ⟨isMulCommutative_of_sq_eq_one hE2, hE2⟩, hE8⟩ hNproper hNsolv hT22 hBen
  exact ⟨g, by rwa [hNC] at hgC, heven⟩

theorem false_of_footeNoEscape (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner)
    (hT22 : FooteTheoremTwoTwo) (hBen : FooteBenderSolvable)
    (h3 : AschbacherTheorem3.Theorem3Statement) {M : Subgroup G} (hM : IsFooteM L M)
    (hne : FooteNoEscape M) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨g₀, hg₀, hg₀even⟩ := exists_even_inf_normalizer h h47 hST hT22 hBen hM hne
  set f : G → ℕ := fun g => (Nat.card ↥(rightConjugate (coreActionKernel M) g ⊓
    normalizer (coreActionKernel M : Set G))).factorization 2 with hfdef
  obtain ⟨g, hgs, hgmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun g => g ∉ normalizer (M : Set G)) f ⟨g₀, by simp [hg₀]⟩
  have hg : g ∉ normalizer (M : Set G) := (Finset.mem_filter.mp hgs).2
  have hmax : ∀ g' : G, g' ∉ normalizer (M : Set G) → f g' ≤ f g := fun g' hg' =>
    hgmax g' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg'⟩)
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(rightConjugate (coreActionKernel M) g ⊓
    normalizer (coreActionKernel M : Set G))) := inferInstance
  have hT1 : sylowImage _ T ≠ ⊥ := by
    intro h1
    have h2 : Nat.card (sylowImage _ T) = 2 ^ f g := by
      rw [sylowImage_card, Sylow.card_eq_multiplicity]
    rw [h1, card_bot] at h2
    have h3 : f g = 0 := by
      by_contra h4
      have : 2 ≤ 2 ^ f g := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f g := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 := hmax g₀ hg₀
    rw [h3] at h4
    have h5 : 0 < f g₀ := by
      have hpos : Nat.card ↥(rightConjugate (coreActionKernel M) g₀ ⊓
          normalizer (coreActionKernel M : Set G)) ≠ 0 := Nat.card_pos.ne'
      exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos).mp
        (even_iff_two_dvd.mp hg₀even)
    omega
  by_cases hU : ∃ U : Subgroup G, U ≤ sylowImage _ T ∧ IsKleinFour U
  · obtain ⟨U, hUT, hU4⟩ := hU
    exact false_of_isKleinFour_le_sylow h h47 hST hA5 hE8 hK hcalc hFI hM hne hg T hU4 hUT
  · push Not at hU
    exact false_of_sylow_unique_involution h h47 hST h3 hM hne hg hmax T hT1 hU

end CFSG.ComponentClassification.FooteLit
