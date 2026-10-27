module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma43ii

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

structure FooteSec4 (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  hLB : FooteLBalanceInput
  hCI : GSLit.ClassicalInvolutionInput
  hGA : TBLit.GriessMultipliersAllModels
  hGC : TBLit.GriessMultipliersCentralCovers
  hSA : SolAltLit.SchurAlternatingMultiplierInput
  hOut : FooteL2OutAbelian
  hAb : FooteL2AbelianCore
  h9 : FooteL2NineOddInner
  hRk : FooteL2RankThree
  hSolv : FooteL2InvolutionSolvable
  simple : IsSimpleGroup G
  ce : ∃ t : G, FooteCounterexample G t L
  huniq : ∀ (a : G) (K M : Subgroup G), IsTwoComponentAt a K → IsTwoComponentAt a M →
    K ∈ footeFamilyOf L → M ∈ footeFamilyOf L → K = M
  hrank2 : ∀ B ∈ footeFamilyOf L, CFSG.pRank 2 ↥B = 2

@[expose] noncomputable def footeME {G : Type} [Group G] (L E : Subgroup G) : Subgroup G :=
  ⨆ e ∈ E, ⨆ (_ : e ≠ 1), footeF L e

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem FooteSec4.footeFamilyType (h : FooteSec4 G L) : FooteFamilyType L := by
  obtain ⟨t, hce⟩ := h.ce
  exact hce.1.2.2.2.2.1

theorem exists_isKleinFour_le_inf_centralizer (h : FooteSec4 G L) {A : Subgroup G}
    (hAF : A ∈ footeFamilyOf L) {E : Subgroup G}
    (hE : IsPGroup 2 E) (hEA : E ≤ coreActionKernel A) :
    ∃ V : Subgroup G, IsKleinFour V ∧ V ≤ A ⊓ centralizer (E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := A ⊓ centralizer (E : Set G) with hW
  have hWA : W ≤ A := inf_le_left
  have hcov : A ≤ W ⊔ oddCoreIn A := le_inf_centralizer_sup_oddCoreIn hE hEA
  set φ := (QuotientGroup.mk' (pPrimeCore 2 A)).comp (Subgroup.inclusion hWA) with hφ
  have hWO : W ≤ normalizer ((oddCoreIn A : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer (hWA hx))
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 A) q
    have hk' := hcov hk
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right W (oddCoreIn A) hWO] at hk'
    obtain ⟨w, hw, o, ho, he⟩ := hk'
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have e1 : (Subgroup.inclusion hWA ⟨w, hw⟩)⁻¹ * ⟨k, hk⟩ = o' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← he]
      simp
    rw [e1]
    exact ho'
  have hker : ¬ 2 ∣ Nat.card φ.ker := by
    intro h2
    have hle := ker_le_pPrimeCore hWA
    have h3 := (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (pPrimeCore_coprime_card (p := 2) (G := ↥W)))
    exact absurd (Nat.Coprime.eq_one_of_dvd h3 h2) (by norm_num)
  have hrank : CFSG.pRank 2 ↥W = 2 := by
    have e₁ := QuotientGroup.quotientKerEquivOfSurjective φ hsurj
    have h1 := GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
      φ.ker hker
    rw [← h1, pRank_eq_of_mulEquiv one_lt_two e₁, pRank_quotient_pPrimeCore, h.hrank2 A hAF]
  have hrank' : CFSG.Open.pRank 2 W = 2 := by
    rwa [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at hrank
  obtain ⟨V, hVW, hVel, hVcard⟩ := SectionRank.exists_pRank one_lt_two W
  rw [hrank'] at hVcard
  refine ⟨V, isKleinFour_of_card_four_of_sq (by rw [hVcard]; norm_num) fun x =>
    Subtype.ext ?_, hVW⟩
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact hVel.2 x x.2

theorem footeME_spec (h : FooteSec4 G L) {z : G} {A : Subgroup G}
    (hAmax : FootePointedMaximal z A) (hAF : A ∈ footeFamilyOf L) {E : Subgroup G}
    (hEc : IsMulCommutative E) (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : Nat.card E = 8)
    (hEA : E ≤ coreActionKernel A) :
    (∀ e ∈ E, e ≠ 1 → IsTwoComponentAt e (footeF L e) ∧ footeF L e ∈ footeFamilyOf L ∧
      centralizer ({e} : Set G) ≤ normalizer (footeF L e : Set G) ∧
      oddResidualIn (A ⊓ centralizer ({e} : Set G)) ≤ footeF L e) ∧
    (Odd (Nat.card ↥(⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (footeF L e))) ∧
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), oddCoreIn (footeF L e)) ≤ oddCoreIn (footeME L E) ∧
      footeME L E ≤ oddResidualIn (A ⊓ centralizer (E : Set G)) ⊔ oddCoreIn (footeME L E)) ∧
    ∀ F : Subgroup G, IsKleinFour F → F ≤ E → footeME L E = footeME L F := by
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  obtain ⟨V, hV, hVA⟩ := exists_isKleinFour_le_inf_centralizer h hAF hEp hEA
  obtain ⟨t, hce⟩ := h.ce
  have := h.simple
  exact foote_lemma_4_3_of_counterexample h.hLB h.hCI h.hGA h.hGC h.hSA h.hOut h.hAb h.h9 h.hRk
    h.hSolv hce h.huniq h.hrank2 hAmax hAF hEc hexp h8 hEA hV hVA

end CFSG.ComponentClassification.FooteLit
