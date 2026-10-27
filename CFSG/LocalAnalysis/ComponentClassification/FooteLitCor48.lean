module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_card_eight_of_commute_normal {Q W U F : Subgroup G} (hW : IsKleinFour W)
    (hWQ : W ≤ Q) (hU : IsKleinFour U) (hUQ : U ≤ Q) (hQU : Q ≤ normalizer (U : Set G))
    (hUW : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u) {x : G} (hxW : x ∈ W) (hx1 : x ≠ 1)
    (hxZ : ∀ q ∈ Q, q * x = x * q) (hFQ : F ≤ Q) (hF2 : ∀ y ∈ F, y ^ 2 = 1)
    (hF8 : Nat.card F = 8) :
    ∃ A : Subgroup G, (∀ y ∈ A, y ^ 2 = 1) ∧ Nat.card A = 8 ∧ W ≤ A ∧ A ≤ Q := by
  by_cases hUW' : U ≤ W
  ·
    have hUeq : U = W := Subgroup.eq_of_le_of_card_ge hUW' (by rw [hU.card_four, hW.card_four])
    subst hUeq
    obtain ⟨w', hw', hw'1, hw'x⟩ := exists_ne_of_isKleinFour hW x
    have hmove : ∀ f ∈ F, f * w' * f⁻¹ = w' ∨ f * w' * f⁻¹ = x * w' := by
      intro f hf
      have hfU : f * w' * f⁻¹ ∈ U := (mem_normalizer_iff.mp (hQU (hFQ hf)) w').mp hw'
      have hne1 : f * w' * f⁻¹ ≠ 1 := fun h1 => hw'1 (by
        calc w' = f⁻¹ * (f * w' * f⁻¹) * f := by group
          _ = 1 := by rw [h1]; group)
      have hnex : f * w' * f⁻¹ ≠ x := fun h1 => hw'x (by
        have h2 : f * x * f⁻¹ = x := by rw [hxZ f (hFQ hf)]; group
        calc w' = f⁻¹ * (f * w' * f⁻¹) * f := by group
          _ = f⁻¹ * (f * x * f⁻¹) * f := by rw [h1, h2]
          _ = x := by group)
      rcases mem_of_isKleinFour hU hxW hw' hfU hx1 hw'1 hw'x.symm with h1 | h1 | h1 | h1
      · exact absurd h1 hne1
      · exact absurd h1 hnex
      · exact Or.inl h1
      · exact Or.inr h1
    have hcard := card_le_two_mul_card_inf_centralizer_of_or hmove
    rw [hF8] at hcard
    by_cases hFW : F ⊓ centralizer ({w'} : Set G) ≤ U
    · have heq : F ⊓ centralizer ({w'} : Set G) = U :=
        Subgroup.eq_of_le_of_card_ge hFW (by rw [hU.card_four]; omega)
      have hUF : U ≤ F := heq ▸ inf_le_left
      exact ⟨F, hF2, hF8, hUF, hFQ⟩
    · obtain ⟨f, hf, hfU⟩ := IsConcreteLE.not_le_iff_exists.mp hFW
      obtain ⟨hfF, hfC⟩ := mem_inf.mp hf
      have hfx : ∀ u ∈ U, u * f = f * u := by
        intro u hu
        have hgen := eq_sup_zpowers_of_isKleinFour hU hxW hw' hw'1 hw'x hx1
        have hUC : U ≤ centralizer ({f} : Set G) := by
          rw [← hgen]
          refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
          · exact mem_centralizer_singleton_iff.mpr (hxZ f (hFQ hfF)).symm
          · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hfC).symm
        exact mem_centralizer_singleton_iff.mp (hUC hu)
      obtain ⟨h2, h8⟩ := sup_zpowers_spec hU hfU (hF2 f hfF) hfx
      exact ⟨U ⊔ zpowers f, h2, h8, le_sup_left, sup_le hUQ (zpowers_le.mpr (hFQ hfF))⟩
  · obtain ⟨u, hu, huW⟩ := IsConcreteLE.not_le_iff_exists.mp hUW'
    obtain ⟨h2, h8⟩ := sup_zpowers_spec hW huW (sq_eq_one_of_isKleinFour hU hu)
      fun w hw => (hUW u hu w hw).symm
    exact ⟨W ⊔ zpowers u, h2, h8, le_sup_left, sup_le hWQ (zpowers_le.mpr (hUQ hu))⟩

theorem exists_card_eight_le_of_isSylowOf (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    {M : Subgroup G} (hM : IsFooteM L M) {x : G} (hx : orderOf x = 2)
    (hxC : x ∈ coreActionKernel M) {Q : Subgroup G}
    (hQ : IsSylowOf 2 Q (coreActionKernel M ⊓ centralizer ({x} : Set G))) :
    ∃ F : Subgroup G, F ≤ Q ∧ (∀ y ∈ F, y ^ 2 = 1) ∧ Nat.card F = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F₀, hF₀, hF₀2, hF₀8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM x hx hxC)
  have hF₀p : IsPGroup 2 F₀ := IsPGroup.of_card (n := 3) (by rw [hF₀8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hQ hF₀ hF₀p
  exact ⟨conjugate F₀ k, conjugate_le_of_forall hk, sq_eq_one_of_mem_conjugate hF₀2 k,
    by rw [card_conjugate_eq_card, hF₀8]⟩

theorem foote_cor_4_8_i (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {W : Subgroup G}
    (hW : IsKleinFour W) (hWC : W ≤ coreActionKernel M) :
    ∃ A : Subgroup G, (∀ y ∈ A, y ^ 2 = 1) ∧ Nat.card A = 8 ∧ W ≤ A ∧
      A ≤ coreActionKernel M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  have hW2 : ∀ x ∈ W, x ^ 2 = 1 := fun x hx => sq_eq_one_of_isKleinFour hW hx
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hW2 ha hb
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW.card_four]; norm_num)
  obtain ⟨t, htW, ht1, -⟩ := exists_ne_of_isKleinFour hW 1
  have ht2 : orderOf t = 2 := orderOf_eq_prime (hW2 t htW) ht1
  have hWCt : W ≤ C ⊓ centralizer ({t} : Set G) := le_inf hWC fun x hx =>
    mem_centralizer_singleton_iff.mpr (hWcomm x hx t htW)
  obtain ⟨Q, hQ, hWQ⟩ := exists_isSylowOf_ge_of_le hWCt hWp
  have hQp := hQ.isPGroup
  have hQC : Q ≤ C := hQ.le.trans inf_le_left
  have hQt : ∀ q ∈ Q, q * t = t * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hQ.le hq)).2
  obtain ⟨F, hFQ, hF2, hF8⟩ := exists_card_eight_le_of_isSylowOf h h47 hM ht2 (hWC htW) hQ
  obtain ⟨U, hU, hUQ, hQU, u₁, hu₁U, hu₁1, hu₁Z⟩ := exists_normal_four_le hQp hFQ hF2 hF8
  by_cases hWU : ∀ u ∈ U, ∀ w ∈ W, u * w = w * u
  · obtain ⟨A, hA2, hA8, hWA, hAQ⟩ :=
      exists_card_eight_of_commute_normal hW hWQ hU hUQ hQU hWU htW ht1 hQt hFQ hF2 hF8
    exact ⟨A, hA2, hA8, hWA, hAQ.trans hQC⟩
  push Not at hWU
  obtain ⟨u, hu, w, hwW, huw⟩ := hWU
  have hw1 : w ≠ 1 := fun h1 => huw (by rw [h1, mul_one, one_mul])
  have hwt : w ≠ t := fun h1 => huw (by rw [h1]; exact (hQt u (hUQ hu)))
  have hw2 : orderOf w = 2 := orderOf_eq_prime (hW2 w hwW) hw1
  have hWgen := eq_sup_zpowers_of_isKleinFour hW htW hwW hw1 hwt ht1
  set R := Q ⊓ centralizer ({w} : Set G) with hR
  have hWR : W ≤ R := le_inf hWQ fun x hx => mem_centralizer_singleton_iff.mpr (hWcomm x hx w hwW)
  have hRW : ∀ r ∈ R, ∀ v ∈ W, r * v = v * r := by
    intro r hr v hv
    have hWC' : W ≤ centralizer ({r} : Set G) := by
      rw [← hWgen]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (hQt r (mem_inf.mp hr).1).symm
      · exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hr).2).symm
    exact (mem_centralizer_singleton_iff.mp (hWC' hv)).symm
  by_cases hRF : ∃ F' : Subgroup G, F' ≤ R ∧ (∀ y ∈ F', y ^ 2 = 1) ∧ Nat.card F' = 8
  · obtain ⟨F', hF'R, hF'2, hF'8⟩ := hRF
    obtain ⟨A, hA2, hA8, hWA, hAle⟩ := exists_card_eight_le_sup hF'2 hF'8 hW
      fun f hf v hv => hRW f (hF'R hf) v hv
    exact ⟨A, hA2, hA8, hWA, hAle.trans ((sup_le hWR hF'R).trans (inf_le_left.trans hQC))⟩
  push Not at hRF
  set W₀ := R ⊓ centralizer (U : Set G) with hW₀
  have htW₀ : t ∈ W₀ := mem_inf.mpr ⟨hWR htW, mem_centralizer_iff.mpr fun v hv =>
    (hQt v (hUQ hv))⟩
  have hwU : w ∉ centralizer (U : Set G) := fun h1 =>
    huw (mem_centralizer_iff.mp h1 u hu)
  have huniq : ∀ x ∈ W₀, orderOf x = 2 → x = t := by
    intro x hx hx2
    by_contra hxt
    obtain ⟨hxR, hxU⟩ := mem_inf.mp hx
    have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx2; omega
    have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
    have hV := isKleinFour_sup_zpowers (hW2 t htW) hx2' ht1 hx1 hxt
      (hRW x hxR t htW).symm
    have hwV : w ∉ zpowers t ⊔ zpowers x := fun h1 => hwU (by
      have h2 : zpowers t ⊔ zpowers x ≤ centralizer (U : Set G) :=
        sup_le (zpowers_le.mpr (mem_inf.mp htW₀).2) (zpowers_le.mpr hxU)
      exact h2 h1)
    obtain ⟨h3, h8⟩ := sup_zpowers_spec hV hwV (hW2 w hwW) fun v hv => by
      have h4 : zpowers t ⊔ zpowers x ≤ centralizer ({w} : Set G) :=
        sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hWcomm t htW w hwW)))
          (zpowers_le.mpr (mem_inf.mp hxR).2)
      exact mem_centralizer_singleton_iff.mp (h4 hv)
    exact hRF _ (sup_le (sup_le (zpowers_le.mpr (hWR htW)) (zpowers_le.mpr hxR))
      (zpowers_le.mpr (hWR hwW))) h3 h8
  obtain ⟨u₂, hu₂U, hu₂1, hu₂₁⟩ := exists_ne_of_isKleinFour hU u₁
  have hUgen := eq_sup_zpowers_of_isKleinFour hU hu₁U hu₂U hu₂1 hu₂₁ hu₁1
  have hRle : Nat.card R ≤ 2 * Nat.card W₀ := by
    have hmove : ∀ r ∈ R, r * u₂ * r⁻¹ = u₂ ∨ r * u₂ * r⁻¹ = u₁ * u₂ := by
      intro r hr
      have hrQ := (mem_inf.mp hr).1
      have hfU : r * u₂ * r⁻¹ ∈ U := (mem_normalizer_iff.mp (hQU hrQ) u₂).mp hu₂U
      have hne1 : r * u₂ * r⁻¹ ≠ 1 := fun h1 => hu₂1 (by
        calc u₂ = r⁻¹ * (r * u₂ * r⁻¹) * r := by group
          _ = 1 := by rw [h1]; group)
      have hne₁ : r * u₂ * r⁻¹ ≠ u₁ := fun h1 => hu₂₁ (by
        have h2 : r * u₁ * r⁻¹ = u₁ := by rw [hu₁Z r hrQ]; group
        calc u₂ = r⁻¹ * (r * u₂ * r⁻¹) * r := by group
          _ = r⁻¹ * (r * u₁ * r⁻¹) * r := by rw [h1, h2]
          _ = u₁ := by group)
      rcases mem_of_isKleinFour hU hu₁U hu₂U hfU hu₁1 hu₂1 hu₂₁.symm with h1 | h1 | h1 | h1
      · exact absurd h1 hne1
      · exact absurd h1 hne₁
      · exact Or.inl h1
      · exact Or.inr h1
    refine (card_le_two_mul_card_inf_centralizer_of_or hmove).trans
      (Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le fun r hr => mem_inf.mpr ⟨(mem_inf.mp hr).1,
        ?_⟩))
    obtain ⟨hrR, hru⟩ := mem_inf.mp hr
    have hUC : U ≤ centralizer ({r} : Set G) := by
      rw [← hUgen]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (hu₁Z r (mem_inf.mp hrR).1).symm
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hru).symm
    exact mem_centralizer_iff.mpr fun v hv => mem_centralizer_singleton_iff.mp (hUC hv)
  have hW₀4 : 4 ≤ Nat.card W₀ := by
    by_contra hlt
    push Not at hlt
    have hW₀p : IsPGroup 2 W₀ := hQp.to_le (inf_le_left.trans inf_le_left)
    have hW₀2 : Nat.card W₀ ≤ 2 := by
      obtain ⟨n, hn⟩ := hW₀p.exists_card_eq
      rw [hn] at hlt ⊢
      have : n ≤ 1 := by
        by_contra h3
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    have hR4 : Nat.card R = 4 := le_antisymm (by omega)
      (by rw [← hW.card_four]; exact Subgroup.card_le_of_le hWR)
    exact card_inf_centralizer_ne_four hST hQp hFQ hF2 hF8 (hWQ hwW) hw2 hR4
  obtain ⟨y, hyW₀, hyt⟩ := exists_sq_eq_of_unique_involution
    (hQp.to_le (inf_le_left.trans inf_le_left)) hW₀4 huniq
  have hRCw : R ≤ C ⊓ centralizer ({w} : Set G) := inf_le_inf_right _ hQC
  obtain ⟨Q', hQ', hRQ'⟩ := exists_isSylowOf_ge_of_le hRCw (hQp.to_le inf_le_left)
  have hQ'p := hQ'.isPGroup
  have hQ'w : ∀ q ∈ Q', q * w = w * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hQ'.le hq)).2
  obtain ⟨F', hF'Q', hF'2, hF'8⟩ :=
    exists_card_eight_le_of_isSylowOf h h47 hM hw2 (hWC hwW) hQ'
  obtain ⟨U', hU', hU'Q', hQ'U', -, -, -, -⟩ := exists_normal_four_le hQ'p hF'Q' hF'2 hF'8
  have hyQ' : y ∈ Q' := hRQ' (mem_inf.mp hyW₀).1
  have hy2 : ∃ k : ℕ, orderOf y = 2 ^ k := by
    obtain ⟨k, hk⟩ := hQ'p ⟨y, hyQ'⟩
    have hdvd : orderOf y ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_mk y hyQ']
      exact orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩
  have htU' : t ∈ centralizer (U' : Set G) :=
    hyt ▸ sq_mem_centralizer_of_isKleinFour hU' (hQ'U' hyQ') hy2
  have hWU' : ∀ v ∈ U', ∀ x ∈ W, v * x = x * v := by
    intro v hv x hx
    have hWC' : W ≤ centralizer ({v} : Set G) := by
      rw [← hWgen]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htU' v hv).symm
      · exact mem_centralizer_singleton_iff.mpr (hQ'w v (hU'Q' hv)).symm
    exact mem_centralizer_singleton_iff.mp (hWC' hx) |>.symm
  obtain ⟨A, hA2, hA8, hWA, hAQ'⟩ := exists_card_eight_of_commute_normal hW
    (hWR.trans hRQ') hU' hU'Q' hQ'U' hWU' hwW hw1 hQ'w hF'Q' hF'2 hF'8
  exact ⟨A, hA2, hA8, hWA, hAQ'.trans (hQ'.le.trans inf_le_left)⟩

theorem foote_cor_4_8_ii (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {g : G}
    {W : Subgroup G} (hW : IsKleinFour W) (hW₁ : W ≤ coreActionKernel M)
    (hW₂ : W ≤ coreActionKernel (conjugate M g)) : g ∈ normalizer (M : Set G) := by
  have hM' := isFooteM_conjugate h hM g
  obtain ⟨A, hA2, hA8, hWA, hAC⟩ := foote_cor_4_8_i h h47 hST hM hW hW₁
  obtain ⟨A', hA'2, hA'8, hWA', hA'C⟩ := foote_cor_4_8_i h h47 hST hM' hW hW₂
  have h1 := (foote_lemma_4_5_ii h hM hA2 hA8 hAC).2 W hW hWA
  have h2 := (foote_lemma_4_5_ii h hM' hA'2 hA'8 hA'C).2 W hW hWA'
  exact mem_normalizer_of_conjugate_eq (h2.symm.trans h1)

theorem foote_cor_4_8_iv (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {T W : Subgroup G}
    (hTC : T ≤ coreActionKernel M) (hW : IsKleinFour W) (hWT : W ≤ T) :
    normalizer (T : Set G) ≤ normalizer (M : Set G) := by
  intro g hg
  refine foote_cor_4_8_ii h h47 hST hM hW (hWT.trans hTC) fun w hw => ?_
  apply mem_coreActionKernel_conjugate
  exact hTC ((mem_normalizer_iff.mp hg w).mp (hWT hw))

theorem foote_cor_4_8_iii (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {g t : G}
    (ht : orderOf t = 2) (ht₁ : t ∈ coreActionKernel M)
    (ht₂ : t ∈ coreActionKernel (conjugate M g)) :
    ∃ n ∈ normalizer (M : Set G), ∃ c ∈ centralizer ({t} : Set G), g = n * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M' := conjugate M g with hM'def
  have hM' := isFooteM_conjugate h hM g
  set B := footeF L t with hB
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM t ht ht₁)
  obtain ⟨E', hE', hE'2, hE'8⟩ := exists_card_eight_of_le_pRank (h47 G L h M' hM' t ht ht₂)
  obtain ⟨hBM, -⟩ := footeF_le_of_card_eight h hM ht ht₁ hF2 hF8 hF
  obtain ⟨hBM', -⟩ := footeF_le_of_card_eight h hM' ht ht₂ hE'2 hE'8 hE'
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM ht ht₁
  have hBN : centralizer ({t} : Set G) ≤ normalizer (B : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  have hCB : coreActionKernel M ⊓ centralizer ({t} : Set G) ≤ coreActionKernel B := fun x hx =>
    mem_coreActionKernel_of_le hBM (hBN (mem_inf.mp hx).2) (mem_inf.mp hx).1
  have hCB' : coreActionKernel M' ⊓ centralizer ({t} : Set G) ≤ coreActionKernel B := fun x hx =>
    mem_coreActionKernel_of_le hBM' (hBN (mem_inf.mp hx).2) (mem_inf.mp hx).1
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (coreActionKernel M ⊓ centralizer ({t} : Set G))
  have heq : coreActionKernel M ⊓ coreActionKernel B ⊓ centralizer ({t} : Set G) =
      coreActionKernel M ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf (le_inf inf_le_left hCB) inf_le_right
  obtain ⟨-, hiv2, -, -⟩ := foote_lemma_4_5_iv h hM ht ht₁ hF2 hF8 hF
  have hTB := hiv2 T (heq ▸ hT)
  have hE'B : E' ≤ coreActionKernel B ⊓ centralizer ({t} : Set G) :=
    le_inf (hE'.trans hCB') (hE'.trans inf_le_right)
  have hE'p : IsPGroup 2 E' := IsPGroup.of_card (n := 3) (by rw [hE'8]; norm_num)
  obtain ⟨k, hkB, hk⟩ := exists_conj_le_of_isSylowOf hTB hE'B hE'p
  have hkt : k ∈ centralizer ({t} : Set G) := (mem_inf.mp hkB).2
  have hE'kT : conjugate E' k ≤ T := conjugate_le_of_forall hk
  obtain ⟨W, hW, hWE⟩ := exists_isKleinFour_le (B := conjugate E' k)
    (sq_eq_one_of_mem_conjugate hE'2 k) (by rw [card_conjugate_eq_card, hE'8]; norm_num)
  have hW₁ : W ≤ coreActionKernel M := hWE.trans (hE'kT.trans (hT.le.trans inf_le_left))
  have hW₂ : W ≤ coreActionKernel (conjugate M (g * k)) := by
    intro x hx
    have hx' := hWE hx
    rw [mem_conjugate_iff] at hx'
    have h1 : k * x * k⁻¹ ∈ coreActionKernel M' := (hE'.trans inf_le_left) hx'
    have h2 := mem_coreActionKernel_conjugate h1
    rwa [hM'def, UnbalancedLayer.conjugate_conjugate] at h2
  have hgk := foote_cor_4_8_ii h h47 hST hM hW hW₁ hW₂
  exact ⟨g * k, hgk, k⁻¹, inv_mem hkt, by group⟩

end CFSG.ComponentClassification.FooteLit
