module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearAssemblyChain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem normalizer_ne_top_of_isPGroup_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (hV1 : V ≠ ⊥) : normalizer (V : Set G) ≠ ⊤ := by
  intro htop
  have hVn : V.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal V with h | h
  · exact hV1 h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hG2 : IsPGroup 2 G := by
      rw [h] at hV2
      exact hV2.of_equiv Subgroup.topEquiv
    have hZ : Subgroup.center G ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot _).mp hG2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
    · exact hZ h'
    · obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h']; exact mem_top b
      exact hab (Subgroup.mem_center_iff.mp hb a)

theorem Endings.Setting.isPGroup {L T : Subgroup G} {f : ℕ} {t : G}
    (hS : Endings.Setting G L f t T) : IsPGroup 2 T := by
  obtain ⟨P, hP⟩ := hS.sylow
  have h1 : IsPGroup 2 (T.subgroupOf (normalizer (zpowers t : Set G))) := hP ▸ P.isPGroup'
  exact h1.of_equiv (subgroupOfEquivOfLe hS.le_normalizer)

theorem psl2_gmsHasRegularNormal_of_setting (hGold : Goldschmidt1974)
    (hHKS : SmallRootRegularNormalInput) {L T : Subgroup G} {f : ℕ} {t : G}
    (hS : Endings.Setting G L f t T) : GMSHasRegularNormal (T ⊓ L) (zpowers t) := by
  have h0 := psl2_smallRootStage_of_card_sylow_eq_two hS.seitz hS.three_le hS.lieModel
    hS.card_sylow hS.orderOf_t hS.mem_centralizer hS.le_normalizer hS.sylow
  obtain ⟨-, -, -, -, -, hΔ, -⟩ := psl2_stage_zero_full_of_card_sylow_eq_two hGold hS.seitz
    hS.three_le hS.lieModel hS.card_sylow hS.orderOf_t hS.mem_centralizer hS.le_normalizer
    hS.sylow
  have h3 : 3 ≤ (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t)).ncard := by
    rw [hΔ]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.three_le
  obtain ⟨hsimple, hnab, hK, -⟩ := hS.seitz
  have ht1 : t ≠ 1 := fun e => by
    have := hS.orderOf_t
    rw [e, orderOf_one] at this
    exact absurd this (by norm_num)
  have htT : t ∈ T := by
    obtain ⟨-, -, -, -, -, -, ⟨-, -, -, hRP, -, -, -, -⟩⟩ := h0.1
    exact hRP (mem_zpowers t)
  have hV2 : IsPGroup 2 (T ⊓ L ⊔ zpowers t : Subgroup G) :=
    hS.isPGroup.to_le (sup_le inf_le_left (zpowers_le.mpr htT))
  have hV1 : T ⊓ L ⊔ zpowers t ≠ ⊥ := fun e => ht1 (by
    have : t ∈ T ⊓ L ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    rwa [e, mem_bot] at this)
  have hY := normalizer_ne_top_of_isPGroup_two hnab hV2 hV1
  have hcat : ∀ S : Subgroup (Equiv.Perm (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t))),
      S ≤ (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range →
      (S.subgroupOf (gmsRootConjugateAction (T ⊓ L ⊔ zpowers t) (zpowers t)).range).Normal →
      IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → CFSG.Blueprint.Catalog S :=
    fun S hS' _ hs hnabS => catalog_of_le_range_of_kProper hK hY _ hS' hs hnabS
  rcases hHKS G (zpowers t) L (T ⊓ L) T f h0 h3 hcat with hE | ⟨hf3, hproj⟩
  · exact hE
  · subst hf3
    exact absurd (h0.exists_normal_index_two_of_projectiveEight h3 hproj)
      (Endings.not_exists_normal_index_two hnab)

theorem LinearPushChain.eq_of_gms28Result (hGold : Goldschmidt1974) {L T : Subgroup G} {f : ℕ}
    {t d : G} {C : ℕ → Subgroup G} (hS : Endings.Setting G L f t T)
    (h : LinearPushChain t d T (T ⊓ L) f 1 C)
    (hdfix : ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hel : ∀ x ∈ C 2, x * x = 1) (hE : GMSHasRegularNormal (T ⊓ L) (zpowers t))
    {V₁ U₁ : Subgroup G} {y d' : G} (hR : GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d') :
    U₁ = C 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨htT, htt, -, -, -, -, -, -, -, -, -, -, -, -, hTU, -⟩ :=
    Endings.psl2_ending_facts hGold hS
  have hf : 2 ≤ f := by have := hS.three_le; omega
  have h0 := psl2_smallRootStage_of_card_sylow_eq_two hS.seitz hS.three_le hS.lieModel
    hS.card_sylow hS.orderOf_t hS.mem_centralizer hS.le_normalizer hS.sylow
  obtain ⟨-, -, -, -, -, hΔ, -⟩ := psl2_stage_zero_full_of_card_sylow_eq_two hGold hS.seitz
    hS.three_le hS.lieModel hS.card_sylow hS.orderOf_t hS.mem_centralizer hS.le_normalizer
    hS.sylow
  have h3 : 3 ≤ (gmsRootConjugates (T ⊓ L ⊔ zpowers t) (zpowers t)).ncard := by
    rw [hΔ]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hS.three_le
  have htr := smallRoot_translations h0 h3 hE
  simp only at htr
  obtain ⟨hTr2, hTrcard, -⟩ := htr
  set Tr : Subgroup G := normalizer ((T ⊓ L ⊔ zpowers t : Subgroup G) : Set G) ⊓
    centralizer ((T ⊓ L : Subgroup G) : Set G) with hTr
  have hV₁ : V₁ = Tr := (hR.sylow.eq_of_le hR.sylow.le le_rfl hTr2).symm
  have hcomm := h.commute_base hf htt hdfix (j := 2) (by omega) le_rfl
  have htUn : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := zpowers_le.mpr (hTU htT)
  have hAt : ∀ a ∈ T ⊓ L, t * a = a * t := fun a ha =>
    mem_centralizer_iff.mp (h.base_le_centralizer ha) t (Set.mem_singleton t)
  have hC2Tr : C 2 ≤ Tr := by
    intro x hx
    refine mem_inf.mpr ⟨GMS28.mem_normalizer_of_conj_mem_of_finite fun v hv => ?_,
      mem_centralizer_iff.mpr fun a ha => (hcomm x hx a ha).symm⟩
    obtain ⟨a, ha, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htUn hv
    · rw [hcomm x hx a ha, mul_inv_cancel_right]
      exact mem_sup_left ha
    · have hxt : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ L := h.base ▸ h.comm_t 1 le_rfl le_rfl x hx
      have e : x * (a * t) * x⁻¹ = (x * a * x⁻¹) * (x * t * x⁻¹ * t⁻¹) * t := by group
      rw [e, hcomm x hx a ha, mul_inv_cancel_right]
      exact mul_mem (mul_mem (mem_sup_left ha) (mem_sup_left hxt)) (mem_sup_right (mem_zpowers t))
  have htTr : zpowers t ≤ Tr := by
    rw [zpowers_le]
    refine mem_inf.mpr ⟨le_normalizer (mem_sup_right (mem_zpowers t)),
      mem_centralizer_iff.mpr fun a ha => (hAt a ha).symm⟩
  have hHle : C 2 ⊔ zpowers t ≤ Tr := sup_le hC2Tr htTr
  have htC2 : t ∉ C 2 := h.t_not_mem
  have hHcard : Nat.card Tr ≤ Nat.card (C 2 ⊔ zpowers t : Subgroup G) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : C 2 ≤ C 2 ⊔ zpowers t)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact Nat.card_pos.ne' hk
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      have heq : C 2 = C 2 ⊔ zpowers t :=
        Subgroup.eq_of_le_of_card_ge le_sup_left hk.le
      exact htC2 (heq ▸ mem_sup_right (mem_zpowers t))
    rw [hk, hTrcard, h.card 2 le_rfl]
    have : 2 ≤ k := by omega
    calc 2 * 2 ^ f * 2 ^ f = 2 * 2 ^ (f * 2) := by ring
      _ ≤ 2 ^ (f * 2) * k := by rw [mul_comm]; exact Nat.mul_le_mul_left _ this
  have hH : C 2 ⊔ zpowers t = Tr := Subgroup.eq_of_le_of_card_ge hHle hHcard
  have hV₁H : V₁ = C 2 ⊔ zpowers t := hV₁.trans hH.symm
  obtain ⟨hyU, -, hdV₁, hdV, hdt, -, hdy⟩ := hR.torus
  have htC2n : zpowers t ≤ normalizer (C 2 : Set G) := zpowers_le.mpr (h.t_norm 2 le_rfl)
  have hdC2 : d' ∈ normalizer (C 2 : Set G) := by
    refine GMS28.mem_normalizer_of_conj_mem_of_finite fun c hc => ?_
    have hzV₁ : d' * c * d'⁻¹ ∈ C 2 ⊔ zpowers t := by
      rw [← hV₁H]
      exact (mem_normalizer_iff.mp hdV₁ c).mp (hV₁H ▸ mem_sup_left hc)
    obtain ⟨u, hu, hzu | hzu⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htC2n hzV₁
    · rw [← hzu]
      exact hu
    ·
      have hzz : (u * t) * (u * t) = 1 := by
        rw [hzu]
        calc d' * c * d'⁻¹ * (d' * c * d'⁻¹) = d' * (c * c) * d'⁻¹ := by group
          _ = 1 := by rw [hel c hc]; group
      have huu : u * u = 1 := hel u hu
      have hut : u * t = t * u := by
        have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
        have h1 : t * u * t = u⁻¹ := by
          have : u * (t * u * t) = 1 := by rw [← hzz]; group
          exact eq_inv_of_mul_eq_one_right this
        calc u * t = t * u * t * t := by rw [h1, hu1]
          _ = t * u := by rw [mul_assoc (t * u), htt, mul_one]
      have huA : u ∈ T ⊓ L := h.mem_base_of_commute le_rfl hu hut
      have hzV : d' * c * d'⁻¹ ∈ T ⊓ L ⊔ zpowers t := by
        rw [← hzu]
        exact mul_mem (mem_sup_left huA) (mem_sup_right (mem_zpowers t))
      have hcV : c ∈ T ⊓ L ⊔ zpowers t := by
        have := (mem_normalizer_iff.mp hdV c).mpr hzV
        exact this
      obtain ⟨a, ha, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htUn hcV
      · rw [hdy a (mem_sup_left ha)]
        exact h.base_le (by omega) le_rfl ((mem_normalizer_iff.mp hyU a).mp ha)
      · exfalso
        apply htC2
        have := mul_mem (inv_mem (h.base_le (by omega) le_rfl ha)) hc
        rwa [inv_mul_cancel_left] at this
  have hU₁le : U₁ ≤ C 2 := by
    rw [hR.eq_commutator, commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hg₁N : g₁ ∈ normalizer (C 2 : Set G) := (zpowers_le.mpr hdC2) hg₁
    have hg₁t : g₁ * t = t * g₁ := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg₁
      exact ((Commute.zpow_left hdt k) : _)
    rw [hV₁H] at hg₂
    obtain ⟨u, hu, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt htC2n hg₂
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp hg₁N u).mp hu) (inv_mem hu)
    · have e : ⁅g₁, u * t⁆ = (g₁ * u * g₁⁻¹) * (g₁ * t * g₁⁻¹ * t⁻¹) * u⁻¹ := by
        rw [commutatorElement_def]
        group
      have e2 : g₁ * t * g₁⁻¹ * t⁻¹ = 1 := by
        rw [hg₁t, mul_assoc t, mul_inv_cancel, mul_one, mul_inv_cancel]
      rw [e, e2, mul_one]
      exact mul_mem ((mem_normalizer_iff.mp hg₁N u).mp hu) (inv_mem hu)
  refine Subgroup.eq_of_le_of_card_ge hU₁le ?_
  rw [hR.card, h.card 2 le_rfl, ← pow_mul, mul_comm]

theorem false_of_chain_of_eq_one_of_elem (hGold : Goldschmidt1974)
    (hHKS : SmallRootRegularNormalInput) (hcase : Endings.GMS43InvolutionCase)
    {L T : Subgroup G} {f : ℕ} {t d : G} {C : ℕ → Subgroup G} (hS : Endings.Setting G L f t T)
    (h : LinearPushChain t d T (T ⊓ L) f 1 C)
    (hdfix : ∀ k : ℕ, ∀ a ∈ T ⊓ L, a ≠ 1 → d ^ k * a * (d ^ k)⁻¹ = a → d ^ k = 1)
    (hel : ∀ x ∈ C 2, x * x = 1) : False := by
  have hE := psl2_gmsHasRegularNormal_of_setting hGold hHKS hS
  obtain ⟨E, hEN, hEn, hreg⟩ := hE
  obtain ⟨V₁, U₁, y, d', hR⟩ := psl2_lemma28_of_card_sylow_eq_two hGold hS.seitz hS.three_le
    hS.lieModel hS.card_sylow hS.orderOf_t hS.mem_centralizer hS.le_normalizer hS.sylow E hEN
    hEn hreg
  have hU₁ := h.eq_of_gms28Result hGold hS hdfix hel ⟨E, hEN, hEn, hreg⟩ hR
  exact Endings.false_of_gms43 hGold hcase hS hR (fun u hu => hel u (hU₁ ▸ hu))

end CFSG.SeitzReduction.RankOne
