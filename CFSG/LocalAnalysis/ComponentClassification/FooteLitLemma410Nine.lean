module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Layer
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCent
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410BenderAct

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_mulAut_fixedPoints_ge_sixty {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Nat.card S = 360)
    (hc8 : ∀ s : S, orderOf s = 2 → Nat.card (centralizer ({s} : Set S)) = 8)
    {τ : MulAut S} (hτ1 : τ ≠ 1)
    (h60 : 60 ≤ Nat.card (MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S)))
    {v : S} (hv : orderOf v = 2) (hτv : τ v = v) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C₀ := MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id S) with hC₀
  have hmem : ∀ s, s ∈ C₀ ↔ τ s = s := fun s => Iff.rfl
  have hC₀top : C₀ ≠ ⊤ := by
    intro htop
    apply hτ1
    ext s
    exact (hmem s).mp (htop ▸ mem_top s)
  have hci := C₀.card_mul_index
  rw [hS] at hci
  have hidx6 : C₀.index = 6 := by
    have hle : C₀.index ≤ 6 := by nlinarith
    have hcore : C₀.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal C₀.normalCore with h1 | h1
      · exact h1
      · exact absurd (eq_top_iff.mpr (h1 ▸ C₀.normalCore_le)) hC₀top
    have hdvd := C₀.index_normalCore_dvd_factorial_index
    rw [hcore, index_bot, hS] at hdvd
    have hpos : C₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain ⟨n, hn⟩ : ∃ n, C₀.index = n := ⟨_, rfl⟩
    rw [hn] at hle hpos hdvd ⊢
    interval_cases n
    all_goals first
      | rfl
      | (exfalso; revert hdvd; decide)
  set V := zpowers v with hV
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  have hvC₀ : v ∈ C₀ := hτv
  have hcong := hVp.card_modEq_card_fixedPoints (S ⧸ C₀)
  rw [← Subgroup.index, hidx6] at hcong
  have h1fix : ((1 : S) : S ⧸ C₀) ∈ MulAction.fixedPoints V (S ⧸ C₀) := by
    rw [MulAction.mem_fixedPoints]
    rintro ⟨w, hw⟩
    show (((w * 1 : S)) : S ⧸ C₀) = ((1 : S) : S ⧸ C₀)
    rw [QuotientGroup.eq, mul_one, mul_one]
    exact inv_mem (zpowers_le.mpr hvC₀ hw)
  have hfix2 : 1 < Nat.card (MulAction.fixedPoints V (S ⧸ C₀)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints V (S ⧸ C₀)) :=
      Nat.card_pos_iff.mpr ⟨⟨⟨_, h1fix⟩⟩, inferInstance⟩
    unfold Nat.ModEq at hcong
    omega
  have : Nontrivial (MulAction.fixedPoints V (S ⧸ C₀)) :=
    Finite.one_lt_card_iff_nontrivial.mp hfix2
  obtain ⟨⟨y, hy⟩, hy1⟩ := exists_ne (⟨_, h1fix⟩ : MulAction.fixedPoints V (S ⧸ C₀))
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have ha : a ∉ C₀ := by
    intro h1
    apply hy1
    apply Subtype.ext
    show ((a : S) : S ⧸ C₀) = ((1 : S) : S ⧸ C₀)
    rw [QuotientGroup.eq, mul_one]
    exact inv_mem h1
  have hva : a⁻¹ * v * a ∈ C₀ := by
    have h1 : (((v * a : S)) : S ⧸ C₀) = ((a : S) : S ⧸ C₀) :=
      (MulAction.mem_fixedPoints.mp hy) ⟨v, mem_zpowers v⟩
    rw [QuotientGroup.eq] at h1
    have h2 := inv_mem h1
    rwa [show ((v * a)⁻¹ * a)⁻¹ = a⁻¹ * v * a by group] at h2
  set C₁ := C₀.map (MulAut.conj a).toMonoidHom with hC₁
  have hmem₁ : ∀ s, s ∈ C₁ ↔ a⁻¹ * s * a ∈ C₀ := fun s => by
    rw [hC₁, mem_map_equiv, MulAut.conj_symm_apply]
  have hcard₁ : Nat.card C₁ = Nat.card C₀ := card_map_of_injective (MulAut.conj a).injective
  have hidx₁ : C₁.index = 6 := by
    have h1 := C₁.card_mul_index
    rw [hS, hcard₁] at h1
    have hpos : 0 < Nat.card C₀ := Nat.card_pos
    nlinarith
  have hinf := Subgroup.index_inf_le (H := C₀) (K := C₁)
  rw [hidx6, hidx₁] at hinf
  have hci₂ := (C₀ ⊓ C₁).card_mul_index
  rw [hS] at hci₂
  have h10 : 10 ≤ Nat.card ↥(C₀ ⊓ C₁) := by nlinarith
  set c := τ a * a⁻¹ with hcdef
  have hc1 : c ≠ 1 := fun h1 => ha ((hmem a).mpr (mul_inv_eq_one.mp h1))
  have hcH : ∀ h ∈ C₀ ⊓ C₁, c * h = h * c := by
    intro h hh
    have h0 : τ h = h := (hmem h).mp (mem_inf.mp hh).1
    have h1 : τ (a⁻¹ * h * a) = a⁻¹ * h * a := (hmem _).mp ((hmem₁ h).mp (mem_inf.mp hh).2)
    rw [map_mul, map_mul, map_inv, h0] at h1
    calc c * h = τ a * a⁻¹ * h := rfl
      _ = τ a * (a⁻¹ * h * a) * a⁻¹ := by group
      _ = τ a * ((τ a)⁻¹ * h * τ a) * a⁻¹ := by rw [h1]
      _ = h * c := by rw [hcdef]; group
  have hvH : v ∈ C₀ ⊓ C₁ := mem_inf.mpr ⟨hvC₀, (hmem₁ v).mpr hva⟩
  have hcv : c ∈ centralizer ({v} : Set S) := mem_centralizer_singleton_iff.mpr (hcH v hvH)
  have hc8' : orderOf c ∣ 2 ^ 3 := by
    have := Subgroup.orderOf_dvd_natCard (centralizer ({v} : Set S)) hcv
    rwa [hc8 v hv] at this
  have h2c : 2 ∣ Nat.card (zpowers c) := by
    rw [Nat.card_zpowers]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc8'
    rcases i with _ | i
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hi, pow_zero])) hc1
    · rw [hi, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' 2 h2c
  have hc'2 : orderOf (c' : S) = 2 := by rw [Subgroup.orderOf_coe]; exact hc'
  have hc'H : C₀ ⊓ C₁ ≤ centralizer ({(c' : S)} : Set S) := by
    intro h hh
    rw [mem_centralizer_singleton_iff]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp c'.2
    rw [← hk]
    exact ((Commute.zpow_left (hcH h hh : Commute c h) k)).eq.symm
  have := card_le_of_le hc'H
  rw [hc8 _ hc'2] at this
  omega

theorem card_eq_sixty_of_fusionIsBenderGroup {X : Type} [Group X]
    [Finite X] (hX : Open.fusionIsBenderGroup X) (P : Sylow 2 X)
    (hP : Nat.card (P : Subgroup X) = 4) :
    Nat.card X = 60 := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Finite.of_surjective e e.surjective
    have hB := (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
      f hf).map_mulEquiv e.symm
    have h1 := (hB P).2.2.2.2
    rw [hP, pow_one] at h1
    have hf2 : f = 2 := Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by omega)
    subst hf2
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four _
      (GaloisField.card 2 2 (by norm_num))
  · have : Finite (Open.PSU3 2 f) := Finite.of_surjective e e.surjective
    have hB := (Open.bender_psu3_borel_full f hf).map_mulEquiv e.symm
    have h1 := (hB P).2.2.2.2
    rw [hP] at h1
    have h4 : 4 ≤ 2 ^ f := calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have : 4 ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left h4 3
    omega
  · have : Finite (Open.Sz a) := Finite.of_surjective e e.surjective
    have hB := (Open.bender_suzuki_borel_full a ha).map_mulEquiv e.symm
    have h1 := (hB P).2.2.2.2
    rw [hP] at h1
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 8 ^ 2 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    omega

omit [Finite G] in
theorem card_mapSurjective_mk_eq [Finite G] {K : Subgroup G} (R₁ : Sylow 2 ↥K) :
    Nat.card ((R₁.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 K)) :
      Sylow 2 (K ⧸ pPrimeCore 2 K)) : Subgroup (K ⧸ pPrimeCore 2 K)) =
      Nat.card (R₁ : Subgroup K) := by
  set ρ := QuotientGroup.mk' (pPrimeCore 2 K) with hρ
  have hinj : Function.Injective (ρ.comp (R₁ : Subgroup K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    exact Subtype.ext (eq_one_of_mk_eq_one_of_isPGroup R₁.isPGroup' a.2 ha)
  have hr : (ρ.comp (R₁ : Subgroup K).subtype).range =
      ((R₁.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 K)) :
        Sylow 2 (K ⧸ pPrimeCore 2 K)) : Subgroup (K ⧸ pPrimeCore 2 K)) := by
    rw [MonoidHom.range_comp, range_subtype, Sylow.coe_mapSurjective]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem Foote410Config.false_of_nine
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t)
    (htK : t ∉ footeK L t)
    (hnine : ∃ p f : ℕ, p.Prime ∧ p ^ f = 9 ∧
      Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVK, x, hxE, hx1, hxK⟩ :=
    hc.exists_mem_coreActionKernel_footeK h h47 hST hAsc h2An hM htK
  obtain ⟨hK₀M', hVK₀, hsupK⟩ :=
    hc.le_conjugate_of_mem_coreActionKernel h h47 hST hAsc h2An hM htK hxE hx1 hxK
  obtain ⟨ht2, htC, hCt⟩ := hc.ht
  obtain ⟨-, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  have hBen : Open.fusionIsBenderGroup (footeK L t ⧸ pPrimeCore 2 (footeK L t)) := by
    rcases htype with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact h1
    · exact absurd h1 htK
  set K := footeK L t with hK
  set K₀ := oddResidualIn (K ⊓ centralizer ({x} : Set G)) with hK₀
  set M' := conjugate M g with hM'def
  have hM' : IsFooteM L M' := isFooteM_conjugate h hM g
  have hK60 : Nat.card (K ⧸ pPrimeCore 2 K) = 60 := by
    obtain ⟨R₁, hR₁⟩ := hVK
    refine card_eq_sixty_of_fusionIsBenderGroup hBen
      (R₁.mapSurjective (QuotientGroup.mk'_surjective _)) ?_
    rw [card_mapSurjective_mk_eq, ← card_map_of_injective K.subtype_injective, hR₁]
    exact hc.card_inf_footeK h h47 hST hAsc h2An hM htK
  have hK₀K : K₀ ≤ K := (oddResidualIn_le _).trans inf_le_left
  have hK₀60 : Nat.card (K₀ ⧸ pPrimeCore 2 K₀) = 60 := by
    obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hK₀K hsupK
    rw [Nat.card_congr e.toEquiv, hK60]
  obtain ⟨hsimple, ⟨ε'⟩⟩ := hM'.quotient h
  obtain ⟨p, f, -, hpf, hlie⟩ := hnine
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hlie
  set e' := ε'.trans e with he'
  have hF9 : Nat.card F = 3 ^ 2 := by rw [hF, hpf]; norm_num
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, by decide, by norm_num, hF9⟩
  have hS360 : Nat.card (M' ⧸ pPrimeCore 2 M') = 360 := by
    rw [Nat.card_congr e'.toEquiv, GorensteinWalter.psl2_card_formula F hodd, hF9]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc8 : ∀ s : M' ⧸ pPrimeCore 2 M', orderOf s = 2 →
      Nat.card (centralizer ({s} : Set (M' ⧸ pPrimeCore 2 M'))) = 8 := by
    intro s hs
    rw [← card_map_of_injective (f := e'.toMonoidHom) e'.injective, map_centralizer_singleton e' s]
    have hs' : orderOf (e' s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
    obtain ⟨h1, -⟩ := Walter.psl2_centralizer_involution F hF9 (by decide) (by norm_num) hs'
    rw [(h1 (by norm_num)).1]
    norm_num
  have htN' : t ∈ normalizer (M' : Set G) := hc.hQN hc.htQ
  set τ := oddBarConj M' ⟨t, htN'⟩ with hτ
  have hτ1 : τ ≠ 1 := by
    intro h1
    exact hc.hinv ⟨t, mem_inf.mpr ⟨htC, mem_coreActionKernel_of_oddBarConj_eq_one h1⟩, ht2⟩
  set φ' := (QuotientGroup.mk' (pPrimeCore 2 M')).comp (Subgroup.inclusion hK₀M') with hφ'
  have hKt : K ≤ centralizer ({t} : Set G) := hKB.trans hBs
  have hfix : ∀ k : ↥K₀, τ (φ' k) = φ' k := by
    intro k
    rw [hφ', MonoidHom.comp_apply, QuotientGroup.mk'_apply, hτ, oddBarConj_apply_mk]
    congr 1
    apply Subtype.ext
    show t * (k : G) * t⁻¹ = (k : G)
    rw [← mem_centralizer_singleton_iff.mp (hKt (hK₀K k.2)), mul_inv_cancel_right]
  have hker : φ'.ker ≤ pPrimeCore 2 K₀ := by
    intro k hk
    rw [MonoidHom.mem_ker, hφ', MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    have hkO : (k : G) ∈ oddCoreIn M' := (mem_pPrimeCore_iff_mem_oddCoreIn _).mp hk
    rw [mem_pPrimeCore_iff_mem_oddCoreIn]
    exact le_oddCoreIn inf_le_left
      (fun y hy => mem_normalizer_inf' (le_normalizer hy)
        (mem_normalizer_oddCoreIn (le_normalizer (hK₀M' hy))))
      (Odd.of_dvd_nat (odd_card_oddCoreIn M') (card_dvd_of_le inf_le_right))
      (mem_inf.mpr ⟨k.2, hkO⟩)
  have h60 : 60 ≤ Nat.card φ'.range := by
    have hc1 : Nat.card ↥K₀ = Nat.card φ'.range * Nat.card φ'.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ').toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ'.ker
    have hc2 : Nat.card ↥K₀ = Nat.card (K₀ ⧸ pPrimeCore 2 K₀) * Nat.card (pPrimeCore 2 K₀) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hc3 : Nat.card φ'.ker ≤ Nat.card (pPrimeCore 2 K₀) := card_le_of_le hker
    rw [hK₀60] at hc2
    have hpos : 0 < Nat.card (pPrimeCore 2 K₀) := Nat.card_pos
    have h4 : Nat.card φ'.range * Nat.card φ'.ker ≤
        Nat.card φ'.range * Nat.card (pPrimeCore 2 K₀) := Nat.mul_le_mul_left _ hc3
    rw [← hc1, hc2] at h4
    exact Nat.le_of_mul_le_mul_right h4 hpos
  have hrange : φ'.range ≤ MonoidHom.eqLocus τ.toMonoidHom
      (MonoidHom.id (M' ⧸ pPrimeCore 2 M')) := by
    rintro _ ⟨k, rfl⟩
    exact hfix k
  have hV4 := hc.card_inf_footeK h h47 hST hAsc h2An hM htK
  obtain ⟨v, hvV, hv1⟩ : ∃ v ∈ Q ⊓ K, v ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Q ⊓ K ≤ ⊥ := fun v hv => (mem_bot).mpr (hall v hv)
    have := card_le_of_le this
    rw [card_bot, hV4] at this
    omega
  have hv2 : v ^ 2 = 1 := hc.hQ2 v (mem_inf.mp hvV).1
  set w := φ' ⟨v, hVK₀ hvV⟩ with hw
  have hw2 : orderOf w = 2 := by
    have hvv : (⟨v, hVK₀ hvV⟩ : ↥K₀) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hv2)
    refine orderOf_eq_prime (by rw [hw, ← map_pow, hvv, map_one]) ?_
    intro hw1
    have hk := MonoidHom.mem_ker.mpr hw1
    rw [hφ', MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    have hvO : v ∈ oddCoreIn M' := (mem_pPrimeCore_iff_mem_oddCoreIn _).mp hk
    exact hv1 (eq_one_of_two_element_of_odd (odd_card_oddCoreIn M') hvO
      ⟨1, by rw [pow_one]; exact orderOf_eq_prime hv2 hv1⟩)
  exact false_of_mulAut_fixedPoints_ge_sixty hS360 hc8 hτ1 (h60.trans (card_le_of_le hrange))
    hw2 (hfix _)

end CFSG.ComponentClassification.FooteLit
