module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigGood3

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

theorem le_oddCoreIn_of_pump_of_bound (hK : K ∈ kStarComponents N) {u b : G}
    (huQ : u ∈ coreActionKernel K) (hu2 : orderOf u = 2)
    (hP : conjClosure (twoLayerIn (K ⊓ centralizer ({u} : Set G)))
        (twoLayerIn (centralizer ({u} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({u} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({u} : Set G)))
    (hbK : b ∈ K) (hb2 : orderOf b = 2) (hub : u * b = b * u) {V X : Subgroup G}
    (hVQ : V ≤ coreActionKernel K) (hVu : V ≤ centralizer ({u} : Set G))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({u} : Set G))
    (hXV : ⁅X, V⁆ = X) :
    X ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  have hbu : b ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hub.symm
  have hSp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  exact le_oddCoreIn_of_component_dichotomy hu2 hb2 hub hVu hX hXV
    (component_dichotomy_of_pump_of_le hK huQ hu2 hP
      (S₁ := zpowers b) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hbK) (zpowers_le.mpr hbu)) hVQ hVu)

theorem component_dichotomy_of_le_pump_sup (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ∈ kStarComponents N) (hK₂ : K₂ ∈ kStarComponents N) (hK₁K : K₁ ≠ K)
    (hK₂K : K₂ ≠ K) {a b : G} (haK : a ∈ K) (ha2 : orderOf a = 2) (hbK : b ∈ K)
    (hab : a * b = b * a) {R : Subgroup G}
    (hRK : R ≤ twoLayerIn (K₁ ⊓ centralizer ({a} : Set G)) ⊔
      twoLayerIn (K₂ ⊓ centralizer ({a} : Set G))) :
    ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({a} : Set G)) →
      zpowers b ≤ coreActionKernel M ∨
        ⁅M, R⁆ ≤ oddCoreIn (centralizer ({a} : Set G)) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hba : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hold : ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({a} : Set G)) →
      R ≤ coreActionKernel M ∨
        ⁅M, zpowers b⁆ ≤ oddCoreIn (centralizer ({a} : Set G)) := by
    intro M hM
    rcases pump_moves h32 hG hN hK₁ hK hK₁K haK ha2 hM with h1 | h1
    · rcases pump_moves h32 hG hN hK₂ hK hK₂K haK ha2 hM with h2 | h2
      · exact Or.inl (hRK.trans (sup_le h1 h2))
      · have hbQ : b ∈ coreActionKernel K₂ :=
          mem_coreActionKernel_of_ne hK hK₂ (Ne.symm hK₂K) hbK
        exact Or.inr (commutator_le_oddCoreIn_of_le_pump h32 hG hN hK₂ hK hK₂K haK ha2
          (S := zpowers b) (zpowers_le.mpr hbQ) (zpowers_le.mpr hba) h2)
    · have hbQ : b ∈ coreActionKernel K₁ :=
        mem_coreActionKernel_of_ne hK hK₁ (Ne.symm hK₁K) hbK
      exact Or.inr (commutator_le_oddCoreIn_of_le_pump h32 hG hN hK₁ hK hK₁K haK ha2
        (S := zpowers b) (zpowers_le.mpr hbQ) (zpowers_le.mpr hba) h1)
  exact component_dichotomy_of_pump_swap hab hold

theorem le_oddCoreIn_of_le_pump_sup (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ∈ kStarComponents N) (hK₂ : K₂ ∈ kStarComponents N) (hK₁K : K₁ ≠ K)
    (hK₂K : K₂ ≠ K) {a b : G} (haK : a ∈ K) (ha2 : orderOf a = 2) (hbK : b ∈ K)
    (hb2 : orderOf b = 2) (hab : a * b = b * a) {R X : Subgroup G}
    (hRa : R ≤ centralizer ({a} : Set G))
    (hRK : R ≤ twoLayerIn (K₁ ⊓ centralizer ({a} : Set G)) ⊔
      twoLayerIn (K₂ ⊓ centralizer ({a} : Set G)))
    (hX : X ≤ oddCoreIn (centralizer ({b} : Set G)) ⊓ centralizer ({a} : Set G))
    (hXR : ⁅X, R⁆ = X) :
    X ≤ oddCoreIn (centralizer ({a} : Set G)) :=
  le_oddCoreIn_of_component_dichotomy ha2 hb2 hab hRa hX hXR
    (component_dichotomy_of_le_pump_sup hq hR1 hG hN hK hK₁ hK₂ hK₁K hK₂K haK ha2 hbK hab
      hRK)

theorem theta_inf_centralizer_le_of_bound (hK : K ∈ kStarComponents N) {V : Subgroup G}
    (hV : IsKleinFour V) (hVQ : V ≤ coreActionKernel K)
    (hbound : ∀ w ∈ V, w ≠ 1 →
      conjClosure (twoLayerIn (K ⊓ centralizer ({w} : Set G)))
          (twoLayerIn (centralizer ({w} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({w} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({w} : Set G)))
    {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2) (hbV : V ≤ centralizer ({b} : Set G)) :
    theta V b ⊓ centralizer (V : Set G) ≤
      oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) := by
  have hSp : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hlocal : ∀ w ∈ V, w ≠ 1 → ∀ M : Subgroup G,
      IsTwoComponentIn M (centralizer ({w} : Set G)) →
        zpowers b ≤ coreActionKernel M ∨
          ⁅M, V⁆ ≤ oddCoreIn (centralizer ({w} : Set G)) := by
    intro w hw hw1 M hM
    have hw2 : orderOf w = 2 := orderOf_eq_two_of_isKleinFour hV hw hw1
    have hVw : V ≤ centralizer ({w} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (comm_of_isKleinFour hV x hx w hw)
    have hbw : b ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hbV hw)).symm)
    exact component_dichotomy_of_pump_of_le hK (hVQ hw) hw2 (hbound w hw hw1)
      (S₁ := zpowers b) (S₂ := V) hSp
      (le_inf (zpowers_le.mpr hbK) (zpowers_le.mpr hbw)) hVQ hVw M hM
  exact theta_inf_centralizer_le_of_component_dichotomy hV hb2 hbV hlocal

omit [Finite G] in
theorem mem_isKleinFour_cases [Finite G] {V : Subgroup G} (hV : IsKleinFour V) {u u' : G}
    (hu : u ∈ V) (hu' : u' ∈ V) (hu1 : u ≠ 1) (hu'1 : u' ≠ 1) (huu' : u ≠ u') {w : G}
    (hw : w ∈ V) : w = 1 ∨ w = u ∨ w = u' ∨ w = u * u' := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have huu : u * u = 1 := by rw [← pow_two]; exact sq_eq_one_of_isKleinFour hV hu
  have hp1 : u * u' ≠ 1 := fun h => huu' (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right huu])
  have hpu : u * u' ≠ u := fun h => hu'1 (by simpa using congrArg (u⁻¹ * ·) h)
  have hpu' : u * u' ≠ u' := fun h => hu1 (by simpa using congrArg (· * u'⁻¹) h)
  have hsub : ({w, 1, u, u', u * u'} : Set G) ⊆ V := by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact hw
    · exact V.one_mem
    · exact hu
    · exact hu'
    · exact V.mul_mem hu hu'
  have hcard : ({w, 1, u, u', u * u'} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_insert_of_notMem, Set.ncard_singleton]
    · simp [hpu'.symm]
    · simp [huu', hpu.symm]
    · simp [Ne.symm hu1, Ne.symm hu'1, hp1.symm]
    · simp [h1, h2, h3, h4]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hV4 : (V : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hV.card_four
  omega

theorem bound_of_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) (hK'K₃ : K' ≠ K₃) {V : Subgroup G} (hV : IsKleinFour V) {u u' : G}
    (huV : u ∈ V) (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1)
    (hu'1 : u' ≠ 1) (huu' : u ≠ u') :
    ∀ w ∈ V, w ≠ 1 →
      conjClosure (twoLayerIn (K ⊓ centralizer ({w} : Set G)))
          (twoLayerIn (centralizer ({w} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({w} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({w} : Set G)) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hu2 := orderOf_eq_two_of_isKleinFour hV huV hu1
  have hu'2 := orderOf_eq_two_of_isKleinFour hV hu'V hu'1
  intro w hw hw1
  rcases mem_isKleinFour_cases hV huV hu'V hu1 hu'1 huu' hw with rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · exact h32 G hG N hN K' hK' K hK hKK'.symm w huK' hu2
  · exact h32 G hG N hN K₃ hK₃ K hK hKK₃.symm w hu'K₃ hu'2
  · have hcomm : u * u' = u' * u := comm_of_isKleinFour hV u huV u' hu'V
    have hw2 : orderOf (u * u') = 2 :=
      orderOf_eq_two_of_isKleinFour hV (V.mul_mem huV hu'V) hw1
    have hwQ : u * u' ∈ coreActionKernel K :=
      mul_mem (mem_coreActionKernel_of_ne hK' hK hKK'.symm huK')
        (mem_coreActionKernel_of_ne hK₃ hK hKK₃.symm hu'K₃)
    have hz2 : IsPGroup 2 (zpowers u') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu'2, pow_one])
    have hrank := two_le_pRank_inf_centralizer hK' hz2
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hK₃ hK' hK'K₃.symm hu'K₃))
    have huY : u ∈ K' ⊓ centralizer ((zpowers u' : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq]
      exact mem_inf.mpr ⟨huK', mem_centralizer_singleton_iff.mpr hcomm⟩
    obtain ⟨F, hFY, hF, huF⟩ := exists_isKleinFour_mem hrank huY hu2
    have hFK' : F ≤ K' := hFY.trans inf_le_left
    have hFw : F ≤ centralizer ({u * u'} : Set G) := by
      intro x hx
      have hxu' : x ∈ centralizer ({u'} : Set G) := by
        have := (hFY hx).2
        rwa [centralizer_zpowers_eq] at this
      have hxu : x * u = u * x := comm_of_isKleinFour hF x hx u huF
      rw [mem_centralizer_singleton_iff] at hxu' ⊢
      rw [← mul_assoc, hxu, mul_assoc, hxu', ← mul_assoc]
    exact conjClosure_le_of_isKleinFour hq hR1 hG hN hK hK' hKK' hwQ hw2 hF hFK' hFw

theorem le_coreActionKernel_of_cross {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) {V : Subgroup G} (hV : IsKleinFour V) {u u' : G} (huV : u ∈ V)
    (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1) (hu'1 : u' ≠ 1)
    (huu' : u ≠ u') : V ≤ coreActionKernel K := by
  intro w hw
  have hu := mem_coreActionKernel_of_ne hK' hK hKK'.symm huK'
  have hu' := mem_coreActionKernel_of_ne hK₃ hK hKK₃.symm hu'K₃
  rcases mem_isKleinFour_cases hV huV hu'V hu1 hu'1 huu' hw with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact hu
  · exact hu'
  · exact mul_mem hu hu'

theorem le_pump_sup_of_cross {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) {V : Subgroup G} (hV : IsKleinFour V) {u u' : G} (huV : u ∈ V)
    (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1) (hu'1 : u' ≠ 1)
    (huu' : u ≠ u') {a : G} (haK : a ∈ K) (ha2 : orderOf a = 2)
    (haV : V ≤ centralizer ({a} : Set G)) :
    V ≤ twoLayerIn (K' ⊓ centralizer ({a} : Set G)) ⊔
      twoLayerIn (K₃ ⊓ centralizer ({a} : Set G)) := by
  have hu2 := orderOf_eq_two_of_isKleinFour hV huV hu1
  have hu'2 := orderOf_eq_two_of_isKleinFour hV hu'V hu'1
  have huA : u ∈ twoLayerIn (K' ⊓ centralizer ({a} : Set G)) :=
    mem_pump_of_two hK' (mem_coreActionKernel_of_ne hK hK' hKK' haK) ha2 ⟨huK', haV huV⟩ (k := 1)
      (by rw [hu2, pow_one])
  have hu'A : u' ∈ twoLayerIn (K₃ ⊓ centralizer ({a} : Set G)) :=
    mem_pump_of_two hK₃ (mem_coreActionKernel_of_ne hK hK₃ hKK₃ haK) ha2 ⟨hu'K₃, haV hu'V⟩
      (k := 1) (by rw [hu'2, pow_one])
  intro w hw
  rcases mem_isKleinFour_cases hV huV hu'V hu1 hu'1 huu' hw with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mem_sup_left huA
  · exact mem_sup_right hu'A
  · exact mul_mem (mem_sup_left huA) (mem_sup_right hu'A)

theorem inf_inf_le_oddCoreIn_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hKK' : K ≠ K') {V : Subgroup G} (hV : IsKleinFour V)
    (hVQ : V ≤ coreActionKernel K) {u : G} (huV : u ∈ V) (huK' : u ∈ K') (hu1 : u ≠ 1)
    {a b : G} (haK : a ∈ K) (ha2 : orderOf a = 2) (hbK : b ∈ K) (hb2 : orderOf b = 2)
    (hab : a * b = b * a) (haV : V ≤ centralizer ({a} : Set G))
    (hbV : V ≤ centralizer ({b} : Set G)) :
    oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) ⊓
        centralizer ({a} : Set G) ≤ oddCoreIn (centralizer ({a} : Set G)) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 := orderOf_eq_two_of_isKleinFour hV huV hu1
  have hVc := comm_of_isKleinFour hV
  set Y₁ := oddCoreIn (centralizer ({b} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) ⊓
    centralizer ({a} : Set G) with hY₁
  have hzu : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2, pow_one])
  have huN : u ∈ normalizer (Y₁ : Set G) :=
    mem_normalizer_inf (mem_normalizer_inf (le_normalizer_oddCoreIn _ (hbV huV))
      (le_normalizer_oddCoreIn _ (le_centralizer_of_le_of_comm le_rfl hVc huV)))
      (le_normalizer (haV huV))
  have hY₁N : zpowers u ≤ normalizer (Y₁ : Set G) := zpowers_le.mpr huN
  have hY₁cop : Nat.Coprime 2 (Nat.card Y₁) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)) (coprime_card_oddCoreIn _)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers u) Y₁ hzu hY₁N hY₁cop
  rw [← hfac]
  refine sup_le ?_ ?_
  ·
    set X := ⁅Y₁, zpowers u⁆ with hX
    have hXY : X ≤ Y₁ := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y₁ _ hY₁N
    have hXX : ⁅X, zpowers u⁆ = X :=
      CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hzu
        (Nat.coprime_two_left.mp hY₁cop) hY₁N
    have huA : u ∈ twoLayerIn (K' ⊓ centralizer ({a} : Set G)) :=
      mem_pump_of_two hK' (mem_coreActionKernel_of_ne hK hK' hKK' haK) ha2 ⟨huK', haV huV⟩
        (k := 1) (by rw [hu2, pow_one])
    exact le_oddCoreIn_of_le_pump_sup hq hR1 hG hN hK hK' hK' hKK'.symm hKK'.symm haK ha2 hbK
      hb2 hab (zpowers_le.mpr (haV huV)) (zpowers_le.mpr (mem_sup_left huA))
      (le_inf (hXY.trans (inf_le_left.trans inf_le_left)) (hXY.trans inf_le_right)) hXX
  ·
    intro y hy
    have hyu : y ∈ centralizer ({u} : Set G) := by
      have := hy.2
      rwa [centralizer_zpowers_eq] at this
    have hbu : b ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_singleton_iff.mp (hbV huV))).symm
    have hVu : V ≤ centralizer ({u} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr (hVc w hw u huV)
    have hV1 : V ≠ ⊥ := fun h => by
      have := hV.card_four
      rw [h, Subgroup.card_bot] at this
      norm_num at this
    have h1 := inf_inf_le_oddCoreIn h32 hG hN hK hK' hKK' huK' hu2
      (zpowers_ne_bot_of_orderOf_eq_two hb2) (isElemAbelian_zpowers
        (sq_eq_one_of_orderOf_eq_two hb2)) (zpowers_le.mpr hbK) (zpowers_le.mpr hbu) hV1
      (isElemAbelian_of_isKleinFour hV) hVQ hVu
    rw [centralizer_zpowers_eq] at h1
    have hyOu : y ∈ oddCoreIn (centralizer ({u} : Set G)) := h1 ⟨⟨hy.1.1.1, hy.1.1.2⟩, hyu⟩
    have hba : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
    have h2 := inf_inf_le_oddCoreIn h32 hG hN hK' hK hKK'.symm haK ha2
      (zpowers_ne_bot_of_orderOf_eq_two hu2) (isElemAbelian_zpowers
        (sq_eq_one_of_orderOf_eq_two hu2)) (zpowers_le.mpr huK') (zpowers_le.mpr (haV huV))
      (zpowers_ne_bot_of_orderOf_eq_two hb2) (isElemAbelian_zpowers
        (sq_eq_one_of_orderOf_eq_two hb2))
      (zpowers_le.mpr (mem_coreActionKernel_of_ne hK hK' hKK' hbK)) (zpowers_le.mpr hba)
    rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h2
    exact h2 ⟨⟨hyOu, hy.1.1.1⟩, hy.1.2⟩

theorem theta_inf_le_theta_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) (hK'K₃ : K' ≠ K₃) {V : Subgroup G} (hV : IsKleinFour V) {u u' : G}
    (huV : u ∈ V) (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1)
    (hu'1 : u' ≠ 1) (huu' : u ≠ u') {a b : G} (haK : a ∈ K) (ha2 : orderOf a = 2)
    (hbK : b ∈ K) (hb2 : orderOf b = 2) (hab : a * b = b * a)
    (haV : V ≤ centralizer ({a} : Set G)) (hbV : V ≤ centralizer ({b} : Set G)) :
    theta V b ⊓ centralizer ({a} : Set G) ≤ theta V a := by
  have hVQ := le_coreActionKernel_of_cross hK hK' hK₃ hKK' hKK₃ hV huV hu'V huK' hu'K₃ hu1 hu'1
    huu'
  have hbound := bound_of_cross hq hR1 hG hN hK hK' hK₃ hKK' hKK₃ hK'K₃ hV huV hu'V huK' hu'K₃ hu1
    hu'1 huu'
  exact theta_inf_le_theta_of_target_dichotomy hV ha2 hb2 hab haV hbV
    (component_dichotomy_of_le_pump_sup hq hR1 hG hN hK hK' hK₃ hKK'.symm hKK₃.symm haK ha2 hbK
      hab
      (le_pump_sup_of_cross hK hK' hK₃ hKK' hKK₃ hV huV hu'V huK' hu'K₃ hu1 hu'1 huu' haK ha2 haV))
    (theta_inf_centralizer_le_of_bound hK hV hVQ hbound hbK hb2 hbV)

theorem theta_inf_le_oddCoreIn_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) (hK'K₃ : K' ≠ K₃) {V : Subgroup G} (hV : IsKleinFour V) {u u' : G}
    (huV : u ∈ V) (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1)
    (hu'1 : u' ≠ 1) (huu' : u ≠ u') {f : G} (hfK : f ∈ K) (hf2 : orderOf f = 2)
    (hfV : V ≤ centralizer ({f} : Set G)) :
    theta V f ⊓ centralizer ({u} : Set G) ≤ oddCoreIn (centralizer ({u} : Set G)) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  set Of := oddCoreIn (centralizer ({f} : Set G)) with hOf
  set X := ⁅Of, V⁆ with hX
  set T := Of ⊓ oddCoreIn (centralizer (V : Set G)) with hT
  set Cv := centralizer ({u} : Set G) with hCv
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVe := isElemAbelian_of_isKleinFour hV
  have hV1 : V ≠ ⊥ := fun h => by
    have := hV.card_four
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  have hv2 : orderOf u = 2 := orderOf_eq_two_of_isKleinFour hV huV hu1
  have hVQ := le_coreActionKernel_of_cross hK hK' hK₃ hKK' hKK₃ hV huV hu'V huK' hu'K₃ hu1 hu'1
    huu'
  have hbound := bound_of_cross hq hR1 hG hN hK hK' hK₃ hKK' hKK₃ hK'K₃ hV huV hu'V huK' hu'K₃ hu1
    hu'1 huu'
  have hVv : V ≤ Cv := fun w hw => mem_centralizer_singleton_iff.mpr (hVc w hw u huV)
  have hfv : f ∈ Cv := mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_singleton_iff.mp (hfV huV)).symm)
  have hfe := isElemAbelian_zpowers (sq_eq_one_of_orderOf_eq_two hf2)
  have hf1 := zpowers_ne_bot_of_orderOf_eq_two hf2
  have hVOf : V ≤ normalizer (Of : Set G) := hfV.trans (le_normalizer_oddCoreIn _)
  have hXOf : X ≤ Of := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Of V hVOf
  have hB : Of ⊓ oddCoreIn (centralizer (V : Set G)) ⊓ Cv ≤ oddCoreIn Cv := by
    have h := inf_inf_le_oddCoreIn h32 hG hN hK hK' hKK' huK' hv2 hf1 hfe (zpowers_le.mpr hfK)
      (zpowers_le.mpr hfv) hV1 hVe hVQ hVv
    rwa [centralizer_zpowers_eq] at h
  have hzv2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hzvV : zpowers u ≤ V := zpowers_le.mpr huV
  have hTX : T ≤ normalizer (X : Set G) := inf_le_left.trans
    (CFSG.SignalizerFunctor.Helpers.normalized_commutator_target_normalizes V Of hVOf)
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVT : V ≤ normalizer (T : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro y
    rw [hT, mem_inf, mem_inf, mem_normalizer_iff.mp (hVOf hw),
      mem_normalizer_iff.mp (le_normalizer_oddCoreIn _ (hVCV hw))]
  have hVX : V ≤ normalizer (X : Set G) := le_normalizer_commutator hVOf
  have hVθ : V ≤ normalizer (theta V f : Set G) :=
    le_normalizer_theta (hfV.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hθ : ((theta V f : Subgroup G) : Set G) = (X : Set G) * (T : Set G) := by
    rw [show theta V f = X ⊔ T from rfl]
    exact coe_mul_of_right_le_normalizer_left X T hTX
  have hθle : theta V f ≤ Of := theta_le_oddCoreIn hfV
  have hcop : Nat.Coprime 2 (Nat.card (theta V f)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hfix := CFSG.SignalizerFunctor.Helpers.normalized_product_fixed_points 2 Nat.prime_two
    (zpowers u) (theta V f) X T hzv2 (hzvV.trans hVθ) (hzvV.trans hVX) (hzvV.trans hVT)
    le_sup_left le_sup_right hcop hθ.symm
  rw [centralizer_zpowers_eq] at hfix
  intro y hy
  have hy' : y ∈ (((theta V f) ⊓ Cv : Subgroup G) : Set G) := hy
  rw [← hfix] at hy'
  obtain ⟨x, hx, t, ht, rfl⟩ := hy'
  refine mul_mem ?_ (hB ⟨ht.1, ht.2⟩)
  set Z := X ⊓ Cv with hZ
  have hVZ : V ≤ normalizer (Z : Set G) := by
    intro w hw
    rw [mem_normalizer_iff]
    intro y
    rw [hZ, mem_inf, mem_inf, mem_normalizer_iff.mp (hVX hw),
      mem_normalizer_iff.mp (le_normalizer (hVv hw))]
  have hZcop : Nat.Coprime 2 (Nat.card Z) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le (inf_le_left.trans hXOf)) (coprime_card_oddCoreIn _)
  have hZodd : Odd (Nat.card Z) := Nat.coprime_two_left.mp hZcop
  have hZfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two V Z hV2 hVZ hZcop
  have hZO : Z ≤ oddCoreIn Cv := by
    rw [← hZfac]
    refine sup_le ?_ ?_
    ·
      have hZZ : ⁅⁅Z, V⁆, V⁆ = ⁅Z, V⁆ :=
        CFSG.ClassicalInvolution.Balance.commutator_commutator_eq_of_isPGroup hV2 hZodd hVZ
      have hZV : ⁅Z, V⁆ ≤ Z := CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Z V hVZ
      have hvf : u * f = f * u := mem_centralizer_singleton_iff.mp hfv |>.symm
      exact le_oddCoreIn_of_pump_of_bound hK (hVQ huV) hv2 (hbound u huV hu1) hfK hf2 hvf hVQ hVv
        (le_inf (hZV.trans (inf_le_left.trans hXOf)) (hZV.trans inf_le_right)) hZZ
    ·
      intro z hz
      have h1 := theta_inf_centralizer_le_of_bound hK hV hVQ hbound hfK hf2 hfV
        ⟨mem_sup_left hz.1.1, hz.2⟩
      exact hB ⟨h1, hz.1.2⟩
  exact hZO ⟨hx.1, hx.2⟩

theorem theta_le_theta_zpowers_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) (hK'K₃ : K' ≠ K₃) {V F : Subgroup G} (hV : IsKleinFour V) {u u' : G}
    (huV : u ∈ V) (hu'V : u' ∈ V) (huK' : u ∈ K') (hu'K₃ : u' ∈ K₃) (hu1 : u ≠ 1)
    (hu'1 : u' ≠ 1) (huu' : u ≠ u') (hF : IsKleinFour F) (hFK : F ≤ K)
    (hFV : F ≤ centralizer (V : Set G)) {e : G} (heK : e ∈ K) (he2 : orderOf e = 2)
    (heV : V ≤ centralizer ({e} : Set G)) (heF : F ≤ centralizer ({e} : Set G)) :
    theta V e ≤ theta (zpowers u) e := by
  set Oe := oddCoreIn (centralizer ({e} : Set G)) with hOe
  set Cv := centralizer ({u} : Set G) with hCv
  have hVc := comm_of_isKleinFour hV
  have hv2 : orderOf u = 2 := orderOf_eq_two_of_isKleinFour hV huV hu1
  have hzv2 : IsPGroup 2 (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hVCV : V ≤ centralizer (V : Set G) := le_centralizer_of_le_of_comm le_rfl hVc
  have hVθ : V ≤ normalizer (theta V e : Set G) :=
    le_normalizer_theta (heV.trans le_normalizer) le_normalizer (hVCV.trans le_normalizer)
  have hθle : theta V e ≤ Oe := theta_le_oddCoreIn heV
  have hcop : Nat.Coprime 2 (Nat.card (theta V e)) := Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le hθle) (coprime_card_oddCoreIn _)
  have hzvθ : zpowers u ≤ normalizer (theta V e : Set G) := (zpowers_le.mpr huV).trans hVθ
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
    Nat.prime_two (zpowers u) (theta V e) hzv2 hzvθ hcop
  rw [centralizer_zpowers_eq] at hfac
  rw [← hfac]
  refine sup_le ?_ ?_
  · exact le_sup_of_le_left (Subgroup.commutator_mono hθle le_rfl)
  · refine le_sup_of_le_right (le_inf (inf_le_left.trans hθle) ?_)
    rw [centralizer_zpowers_eq]
    set Y := theta V e ⊓ Cv with hY
    have hFY : F ≤ normalizer (Y : Set G) := by
      intro x hx
      have hxθ : x ∈ normalizer (theta V e : Set G) :=
        le_normalizer_theta (heF.trans le_normalizer)
          (fun _ h => Subgroup.centralizer_le_normalizer (V : Set G) (hFV h))
          (fun _ h => le_normalizer (hFV h)) hx
      rw [mem_normalizer_iff]
      intro y
      rw [hY, mem_inf, mem_inf, mem_normalizer_iff.mp hxθ,
        mem_normalizer_iff.mp (le_normalizer (show x ∈ Cv from
          mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hFV hx)) u huV).symm))]
    have hYcop : Nat.Coprime 2 (Nat.card Y) := Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left) hcop
    refine (le_iSup_inf_centralizer_of_isKleinFour hF hFY hYcop).trans ?_
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    have hf2 : orderOf f = 2 := orderOf_eq_two_of_isKleinFour hF hf hf1
    have hfV : V ≤ centralizer ({f} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hFV hf)) w hw)
    have hef : f * e = e * f := (mem_centralizer_singleton_iff.mp (heF hf))
    have hbal := theta_inf_le_theta_cross hq hR1 hG hN hK hK' hK₃ hKK' hKK₃ hK'K₃ hV huV hu'V
      huK' hu'K₃ hu1 hu'1 huu' (hFK hf) hf2 heK he2 hef hfV heV
    intro y hy
    exact theta_inf_le_oddCoreIn_cross hq hR1 hG hN hK hK' hK₃ hKK' hKK₃ hK'K₃ hV huV hu'V huK'
      hu'K₃ hu1 hu'1 huu' (hFK hf) hf2 hfV ⟨hbal ⟨hy.1.1, hy.2⟩, hy.1.2⟩

theorem wGroup_zpowers_eq_cross (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' K₃ : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hK₃ : K₃ ∈ kStarComponents N) (hKK' : K ≠ K')
    (hKK₃ : K ≠ K₃) (hK'K₃ : K' ≠ K₃) {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K)
    {u u' : G} (huK' : u ∈ K') (hu2 : orderOf u = 2) (hu'K₃ : u' ∈ K₃) (hu'2 : orderOf u' = 2)
    (huu' : u * u' = u' * u) (hEu : E ≤ centralizer ({u} : Set G))
    (hEu' : E ≤ centralizer ({u'} : Set G)) :
    wGroup E (zpowers u) = wGroup E (zpowers u') := by
  classical
  by_cases hne : u = u'
  · rw [hne]
  set V := closure ({u, u'} : Set G) with hVdef
  have hV : IsKleinFour V :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair hu2 hu'2 huu' hne
  have huV : u ∈ V := subset_closure (Set.mem_insert u _)
  have hu'V : u' ∈ V := subset_closure (Set.mem_insert_of_mem u rfl)
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; norm_num at hu2
  have hu'1 : u' ≠ 1 := fun h => by rw [h, orderOf_one] at hu'2; norm_num at hu'2
  have hV2 := isPGroup_of_isKleinFour hV
  have hVc := comm_of_isKleinFour hV
  have hVe : ∀ e ∈ E, V ≤ centralizer ({e} : Set G) := fun e he => by
    rw [hVdef, closure_le]
    rintro x (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hEu he)).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hEu' he)).symm
  have hEV : E ≤ centralizer (V : Set G) := fun e he => mem_centralizer_iff.mpr fun v hv =>
    mem_centralizer_singleton_iff.mp (hVe e he hv)
  have hEc := comm_of_isKleinFour hE
  have hEe : ∀ e ∈ E, E ≤ centralizer ({e} : Set G) := fun e he x hx =>
    mem_centralizer_singleton_iff.mpr (hEc x hx e he)
  have hθ : ∀ e ∈ E, e ≠ 1 → theta (zpowers u) e = theta (zpowers u') e := fun e he he1 => by
    have he2 := orderOf_eq_two_of_isKleinFour hE he he1
    have h1 : theta (zpowers u) e = theta V e :=
      le_antisymm (theta_mono (zpowers_le.mpr huV) hV2 hVc (hVe e he))
        (theta_le_theta_zpowers_cross hq hR1 hG hN hK hK' hK₃ hKK' hKK₃ hK'K₃ hV huV hu'V huK'
          hu'K₃ hu1 hu'1 hne hE hEK hEV (hEK he) he2 (hVe e he) (hEe e he))
    have h2 : theta (zpowers u') e = theta V e :=
      le_antisymm (theta_mono (zpowers_le.mpr hu'V) hV2 hVc (hVe e he))
        (theta_le_theta_zpowers_cross hq hR1 hG hN hK hK₃ hK' hKK₃ hKK' hK'K₃.symm hV hu'V huV
          hu'K₃ huK' hu'1 hu1 (Ne.symm hne) hE hEK hEV (hEK he) he2 (hVe e he) (hEe e he))
    rw [h1, h2]
  refine le_antisymm (iSup₂_le fun e he => iSup_le fun he1 => ?_)
    (iSup₂_le fun e he => iSup_le fun he1 => ?_)
  · rw [hθ e he he1]
    exact theta_le_wGroup he he1
  · rw [← hθ e he he1]
    exact theta_le_wGroup he he1

theorem le_normalizer_wGroup_of_third_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K' V B : Subgroup G} (hP : SigPair N K K' V B)
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ kStarComponents N) (hK₃K : K₃ ≠ K) (hK₃K' : K₃ ≠ K') :
    K' ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hK₃W := le_normalizer_wGroup_of_ne_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE
    hEB hEK hBN hK₃ hK₃K hK₃K'
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hE2 := isPGroup_of_isKleinFour hE
  have hKQ₃ : K ≤ coreActionKernel K₃ := le_coreActionKernel_of_ne hK₃ hK hK₃K
  have hK'Q₃ : K' ≤ coreActionKernel K₃ := le_coreActionKernel_of_ne hK₃ hK' hK₃K'
  have hthird : ∀ v : G, v ∈ K' → orderOf v = 2 → E ≤ centralizer ({v} : Set G) →
      ∃ t ∈ K₃ ⊓ centralizer (E : Set G), orderOf t = 2 ∧ v * t = t * v := by
    intro v hvK' hv2 hEv
    have hzv : IsPGroup 2 (zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
    have hEzv : E ≤ centralizer ((zpowers v : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq]; exact hEv
    have hS2 := isPGroup_sup_of_le_centralizer hE2 hzv hEzv
    have hrank := two_le_pRank_inf_centralizer hK₃ hS2
      (sup_le (hEK.trans hKQ₃) (zpowers_le.mpr (hK'Q₃ hvK')))
    obtain ⟨t, htY, ht2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank)
    have htS : t ∈ centralizer ((E ⊔ zpowers v : Subgroup G) : Set G) := htY.2
    have htE : t ∈ centralizer (E : Set G) := centralizer_le (by exact_mod_cast le_sup_left) htS
    have htv : t ∈ centralizer ((zpowers v : Subgroup G) : Set G) :=
      centralizer_le (by exact_mod_cast le_sup_right) htS
    rw [centralizer_zpowers_eq] at htv
    exact ⟨t, ⟨htY.1, htE⟩, ht2, (mem_centralizer_singleton_iff.mp htv).symm⟩
  have hEcen : ∀ x : G, x ∈ centralizer (E : Set G) → E ≤ centralizer ({x} : Set G) :=
    fun x hx e he => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hx) e he)
  have hstep3 : ∀ t ∈ K₃ ⊓ centralizer (E : Set G), orderOf t = 2 →
      ∀ t' ∈ K₃ ⊓ centralizer (E : Set G), orderOf t' = 2 → t * t' = t' * t →
      wGroup E (zpowers t) = wGroup B V → wGroup E (zpowers t') = wGroup B V := by
    intro t ht ht2 t' ht' ht'2 htt' hgt
    by_cases hne' : t = t'
    · rwa [← hne']
    have hT := UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair ht2 ht'2 htt' hne'
    set T := closure ({t, t'} : Set G) with hTdef
    have htT : t ∈ T := subset_closure (Set.mem_insert t _)
    have ht'T : t' ∈ T := subset_closure (Set.mem_insert_of_mem t rfl)
    have hTK₃ : T ≤ K₃ := by
      rw [hTdef, closure_le]
      rintro x (rfl | rfl)
      · exact ht.1
      · exact ht'.1
    have hTE : ∀ e ∈ E, T ≤ centralizer ({e} : Set G) := fun e he => by
      rw [hTdef, closure_le]
      rintro x (rfl | rfl)
      · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp ht.2) e he).symm
      · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp ht'.2) e he).symm
    have hET : E ≤ centralizer (T : Set G) := fun e he => mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (hTE e he hx)
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
    have ht'1 : t' ≠ 1 := fun h => by rw [h, orderOf_one] at ht'2; norm_num at ht'2
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK₃ hK₃K.symm hT hTK₃ hE hEK hET ht'T ht'1,
      wGroup_eq_wGroup_zpowers h32 hG hN hK hK₃ hK₃K.symm hT hTK₃ hE hEK hET htT ht1]
    exact hgt
  have hconj3 : ∀ t : G, wGroup E (zpowers t) = wGroup B V →
      ∀ m ∈ K₃ ⊓ centralizer (E : Set G), wGroup E (zpowers (m * t * m⁻¹)) = wGroup B V := by
    intro t hgt m hm
    have hEm : E.map (MulAut.conj m).toMonoidHom = E := map_conj_eq_of_mem_centralizer hm.2
    have hWm : (wGroup B V).map (MulAut.conj m).toMonoidHom = wGroup B V :=
      mem_normalizer_iff_map_conj_eq.mp (hK₃W hm.1)
    calc wGroup E (zpowers (m * t * m⁻¹))
        = (wGroup E (zpowers t)).map (MulAut.conj m).toMonoidHom := by
          rw [map_wGroup, hEm, MonoidHom.map_zpowers]
          rfl
      _ = wGroup B V := by rw [hgt, hWm]
  obtain ⟨v₀, hv₀, hv₀1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv₀2 := orderOf_eq_two_of_isKleinFour hV hv₀ hv₀1
  have hEv₀ : E ≤ centralizer ({v₀} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hEV he)) v₀ hv₀).symm
  have hgv₀ : wGroup E (zpowers v₀) = wGroup B V := by
    rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK hEV hv₀ hv₀1, hWE]
  obtain ⟨t₀, ht₀, ht₀2, hv₀t₀⟩ := hthird v₀ (hVK' hv₀) hv₀2 hEv₀
  have hgt₀ : wGroup E (zpowers t₀) = wGroup B V := by
    rw [← wGroup_zpowers_eq_cross hq hR1 hG hN hK hK' hK₃ hne hK₃K.symm hK₃K'.symm hE hEK
      (hVK' hv₀) hv₀2 ht₀.1 ht₀2 hv₀t₀ hEv₀ (hEcen t₀ ht₀.2)]
    exact hgv₀
  have hgood3 : ∀ t ∈ K₃ ⊓ centralizer (E : Set G), orderOf t = 2 →
      wGroup E (zpowers t) = wGroup B V := by
    intro t ht ht2
    have hzt₀ : IsPGroup 2 (zpowers t₀) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₀2, pow_one])
    have hzt : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
    obtain ⟨P, hPY, hP2, ht₀P, k, hkY, htk⟩ :=
      exists_pGroup_conj_le (zpowers_le.mpr ht₀) hzt₀ (zpowers_le.mpr ht) hzt
    have ht₀P' : t₀ ∈ P := ht₀P (mem_zpowers t₀)
    have hkt : k * t * k⁻¹ ∈ P := htk ⟨t, mem_zpowers t, rfl⟩
    have hkt2 : orderOf (k * t * k⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact ht2
    have hPne : P ≠ ⊥ := fun h => by
      have := ht₀P'
      rw [h, mem_bot] at this
      rw [this, orderOf_one] at ht₀2
      norm_num at ht₀2
    obtain ⟨z, hzP, hz2, hzc⟩ := exists_central_involution_of_isPGroup hP2 hPne
    have h1 := hstep3 t₀ ht₀ ht₀2 z (hPY hzP) hz2 (hzc t₀ ht₀P').symm hgt₀
    have h2 := hstep3 z (hPY hzP) hz2 (k * t * k⁻¹) (hPY hkt) hkt2 (hzc _ hkt) h1
    have h3 := hconj3 (k * t * k⁻¹) h2 k⁻¹ (inv_mem hkY)
    have e : k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t := by group
    rwa [e] at h3
  have hgood' : ∀ v ∈ K' ⊓ centralizer (E : Set G), orderOf v = 2 →
      wGroup E (zpowers v) = wGroup B V := by
    intro v hv hv2
    obtain ⟨t, ht, ht2, hvt⟩ := hthird v hv.1 hv2 (hEcen v hv.2)
    rw [wGroup_zpowers_eq_cross hq hR1 hG hN hK hK' hK₃ hne hK₃K.symm hK₃K'.symm hE hEK hv.1 hv2
      ht.1 ht2 hvt (hEcen v hv.2) (hEcen t ht.2)]
    exact hgood3 t ht ht2
  rw [← inf_centralizer_sup_oddCoreIn_eq hE2 (hEK.trans (le_coreActionKernel_of_ne hK' hK
    hne.symm))]
  refine sup_le ?_ ?_
  · intro g hg
    have hEg : E.map (MulAut.conj g).toMonoidHom = E := map_conj_eq_of_mem_centralizer hg.2
    set Vg := V.map (MulAut.conj g).toMonoidHom with hVgdef
    have hVg4 := isKleinFour_map_conj hV g
    have hVgK' : Vg ≤ K' := by
      rintro _ ⟨v, hv, rfl⟩
      exact mul_mem (mul_mem hg.1 (hVK' hv)) (inv_mem hg.1)
    have hEVg : E ≤ centralizer (Vg : Set G) := by
      rw [← hEg, hVgdef, ← map_centralizer (MulAut.conj g) V]
      exact map_mono hEV
    have hv₀g : g * v₀ * g⁻¹ ∈ Vg := ⟨v₀, hv₀, rfl⟩
    have hv₀g2 : orderOf (g * v₀ * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hv₀2
    have hv₀g1 : g * v₀ * g⁻¹ ≠ 1 := fun h => by
      rw [h, orderOf_one] at hv₀g2; norm_num at hv₀g2
    have hv₀E : v₀ ∈ centralizer (E : Set G) := mem_centralizer_iff.mpr fun e he =>
      (mem_centralizer_iff.mp (hEV he)) v₀ hv₀ |>.symm
    have hv₀gE : g * v₀ * g⁻¹ ∈ centralizer (E : Set G) :=
      mul_mem (mul_mem hg.2 hv₀E) (inv_mem hg.2)
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hEg, wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hVg4 hVgK' hE
        hEK hEVg hv₀g hv₀g1, hWE]
      exact hgood' _ ⟨hVgK' hv₀g, hv₀gE⟩ hv₀g2
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK'.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

@[expose] def Lemma39TwoRestFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      ((∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
            Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) →
        K ≤ normalizer (wGroup B V : Set G)) ∧
      ((∀ E : Subgroup G, IsKleinFour E → E ≤ B → E ≤ K →
          ¬ (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) →
        K' ≤ normalizer (wGroup B V : Set G))

theorem lemma39RestFor_of_two (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : Lemma39TwoRestFor) :
    Lemma39RestFor := by
  intro G _ _ hG N hN K K' V B hP hW
  by_cases h2 : (kStarComponents N).ncard = 2
  · exact ⟨fun _ => (h G hG N hN h2 K K' V B hP hW).1, (h G hG N hN h2 K K' V B hP hW).2⟩
  obtain ⟨K₃, hK₃, hK₃K, hK₃K'⟩ := exists_third_kStar_of_ncard_ne_two hP.1 hP.2.1 hP.2.2.1 h2
  exact ⟨fun h2' => absurd h2' h2,
    fun _ => le_normalizer_wGroup_of_third_right hq hR1 hG hN hP hK₃ hK₃K hK₃K'⟩

theorem lemma315bInputFor_simple_of_two_residues (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39TwoRestFor) (hgood : GoodInvolutionsTwoFor)
    (hsingle : SingleComponentExcludedFor) (hpair : SigPairExistsTwoFor) :
    Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_residues hq hR1 hF (lemma39RestFor_of_two hq hR1 h39) hgood hsingle
    hpair

end CFSG.ComponentClassification.Sol76.Sig
