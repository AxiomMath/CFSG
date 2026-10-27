module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleClassical
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLForm
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups

@[expose] def NonSLComponentUnique (K : Type) [Field K] (G : Type) [Group G] : Prop :=
  ∀ L L' : Subgroup G, CFSG.IsComponent L → CFSG.IsComponent L' →
    ¬ Nonempty (L ≃* SL(2, K)) → ¬ Nonempty (L' ≃* SL(2, K)) → L = L'

theorem nonSLComponentUnique_of_mulEquiv {K : Type} [Field K] {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (h : NonSLComponentUnique K H) : NonSLComponentUnique K G := by
  intro L L' hL hL' hn hn'
  refine Subgroup.map_injective e.injective (h _ _ (LocalCores.isComponent_map_mulEquiv e hL)
    (LocalCores.isComponent_map_mulEquiv e hL') ?_ ?_)
  · rintro ⟨f⟩
    exact hn ⟨(L.equivMapOfInjective _ e.injective).trans f⟩
  · rintro ⟨f⟩
    exact hn' ⟨(L'.equivMapOfInjective _ e.injective).trans f⟩

theorem nonSLComponentUnique_of_eq_or_SL {K : Type} [Field K] {G : Type} [Group G]
    {B : Subgroup G}
    (h : ∀ L : Subgroup G, CFSG.IsComponent L → L = B ∨ Nonempty (L ≃* SL(2, K))) :
    NonSLComponentUnique K G := by
  intro L L' hL hL' hn hn'
  rcases h L hL with rfl | h1
  · rcases h L' hL' with rfl | h2
    · rfl
    · exact absurd h2 hn'
  · exact absurd h1 hn

theorem nonSLComponentUnique_of_forall_SL {K : Type} [Field K] {G : Type} [Group G]
    (h : ∀ L : Subgroup G, CFSG.IsComponent L → Nonempty (L ≃* SL(2, K))) :
    NonSLComponentUnique K G :=
  fun L _ hL _ hn _ => absurd (h L hL) hn

theorem slComponentForm_of_forall_SL {K : Type} [Field K] {G : Type} [Group G]
    (h : ∀ L : Subgroup G, CFSG.IsComponent L → Nonempty (L ≃* SL(2, K))) :
    SLComponentForm K G :=
  fun L hL => Or.inl (h L hL)

theorem pRank_le_one_of_mulEquiv_SL {K : Type} [Field K] (hK : ringChar K ≠ 2) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (e : L ≃* SL(2, K)) : CFSG.Open.pRank 2 L ≤ 1 := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  refine SectionRank.pRank_le (by norm_num) fun E hEL hE => ?_
  have key : ∀ u : G, ∀ hu : u ∈ E, u ≠ 1 → e ⟨u, hEL hu⟩ = -1 := by
    intro u hu hu1
    have hsq : (⟨u, hEL hu⟩ : L) ^ 2 = 1 := Subtype.ext (by simpa using hE.2 u hu)
    have hne : e ⟨u, hEL hu⟩ ≠ 1 := by
      intro h
      apply hu1
      have : (⟨u, hEL hu⟩ : L) = 1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
    have hcoe := LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (e ⟨u, hEL hu⟩)
      (by rw [← map_pow, hsq, map_one]) hne
    exact Subtype.ext (hcoe.trans (by simp))
  have hinj : Function.Injective (fun v : E => if v = 1 then (0 : Fin 2) else 1) := by
    intro v w hvw
    by_cases hv : v = 1 <;> by_cases hw : w = 1
    · rw [hv, hw]
    · simp [hv, hw] at hvw
    · simp [hv, hw] at hvw
    · have hv' : (v : G) ≠ 1 := fun h => hv (Subtype.ext h)
      have hw' : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
      have h3 : (⟨v, hEL v.2⟩ : L) = ⟨w, hEL w.2⟩ :=
        e.injective ((key v v.2 hv').trans (key w w.2 hw').symm)
      exact Subtype.ext (show (v : G) = w from congrArg (fun z : L => (z : G)) h3)
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

theorem ringChar_dvd_card_SL (K : Type) [Field K] [Finite K] :
    ringChar K ∣ Nat.card SL(2, K) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
  rw [SL2MinimalFaithful.card_specialLinearGroup_fin_two K]
  refine Dvd.dvd.mul_right ?_ _
  rw [Nat.card_eq_fintype_card, hcard]
  exact dvd_pow_self _ n.ne_zero

@[expose] def BigComponentUniqueAt (r : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ a : T, orderOf a = 2 → ∀ L L' : Subgroup T,
    CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set T)) →
    CFSG.Assembly.IsComponentOf L' (centralizer ({a} : Set T)) →
    2 ≤ CFSG.Open.pRank 2 L → 2 ≤ CFSG.Open.pRank 2 L' → L = L' ∧ r ∣ Nat.card L

@[expose] def CentralizerGenerationAt (r : ℕ) (T : Type) [Group T] : Prop :=
  ∀ A R : Subgroup T, CFSG.IsElementaryAbelian 2 A → 2 ^ 2 ≤ Nat.card A → IsPGroup r R →
    R ≠ ⊥ → A ≤ normalizer (R : Set T) →
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), centralizer ({a} : Set T)) = ⊤

theorem false_of_bigComponentUniqueAt {T : Type} [Group T] [Finite T] [IsSimpleGroup T] {r : ℕ}
    [Fact r.Prime] (hU : BigComponentUniqueAt r T) (hG : CentralizerGenerationAt r T)
    {X A : Subgroup T} (hXq : CFSG.IsQuasisimple X) (hXr : 2 ≤ CFSG.Open.pRank 2 X)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hAc : Nat.card A = 4) (hXA : ⁅X, A⁆ = ⊥)
    (hXc : ∀ a ∈ A, a ≠ 1 → CFSG.Assembly.IsComponentOf X (centralizer ({a} : Set T))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 A := hAe
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hAc]; norm_num)
  obtain ⟨⟨a₀, ha₀⟩, ha₀1'⟩ := exists_ne (1 : A)
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = 2 := fun a ha ha1 =>
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hrX := (hU a₀ (hord a₀ ha₀ ha₀1) X X (hXc a₀ ha₀ ha₀1) (hXc a₀ ha₀ ha₀1) hXr hXr).2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) r hrX
  have hxo : orderOf (x : T) = r := by rw [Subgroup.orderOf_coe, hx]
  have hRp : IsPGroup r (zpowers (x : T)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hR1 : zpowers (x : T) ≠ ⊥ := by
    intro h
    have hmem : (x : T) ∈ zpowers (x : T) := mem_zpowers _
    rw [h, mem_bot] at hmem
    rw [hmem, orderOf_one] at hxo
    exact (Fact.out : r.Prime).one_lt.ne' hxo.symm
  have hXcA : X ≤ centralizer (A : Set T) := commutator_eq_bot_iff_le_centralizer.1 hXA
  have hAR : A ≤ normalizer ((zpowers (x : T) : Subgroup T) : Set T) := by
    refine le_trans ?_ (centralizer_le_normalizer _)
    intro a ha
    rw [mem_centralizer_iff]
    intro y hy
    have hyX : y ∈ X := zpowers_le.2 x.2 hy
    exact (mem_centralizer_iff.1 (hXcA hyX) a ha).symm
  have htop := hG A _ hAe (by simp [hAc]) hRp hR1 hAR
  have hconj : ∀ a ∈ A, a ≠ 1 → ∀ g ∈ centralizer ({a} : Set T), conjSub g X = X := by
    intro a ha ha1 g hg
    have hc := isComponentOf_map_conj (hXc a ha ha1) g
    have hga : g * a * g⁻¹ = a := by
      rw [mem_centralizer_singleton_iff] at hg
      rw [hg, mul_inv_cancel_right]
    rw [map_conj_centralizer_singleton, hga] at hc
    have hr : 2 ≤ CFSG.Open.pRank 2 (conjSub g X) :=
      hXr.trans (SectionRank.pRank_le_map (by norm_num) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective X)
    exact (hU a (hord a ha ha1) _ _ hc (hXc a ha ha1) hr hXr).1
  have hnorm : ∀ a ∈ A, a ≠ 1 → centralizer ({a} : Set T) ≤ normalizer (X : Set T) :=
    fun a ha ha1 g hg => mem_normalizer_of_conjSub_le (hconj a ha ha1 g hg).le
      (hconj a ha ha1 g⁻¹ (inv_mem hg)).le
  have hN : normalizer (X : Set T) = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup₂_le fun a ha => iSup_le fun ha1 => hnorm a ha ha1
  have hXn : X.Normal := normalizer_eq_top_iff.1 hN
  rcases hXn.eq_bot_or_eq_top with h | h
  · exact (nontrivial_iff_ne_bot X).1 (LocalCores.isQuasisimple_nontrivial hXq) h
  ·
    have hZ : center T = ⊥ := by
      rcases (inferInstance : (center T).Normal).eq_bot_or_eq_top with hZ | hZ
      · exact hZ
      · exfalso
        obtain ⟨-, -, a, b, hab⟩ := hXq
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        apply Subtype.ext
        have hb : (b : T) ∈ center T := by rw [hZ]; exact mem_top _
        exact mem_center_iff.1 hb a
    have ha₀Z : a₀ ∈ center T := by
      rw [mem_center_iff]
      intro g
      have hgX : g ∈ X := by rw [h]; exact mem_top g
      exact (mem_centralizer_iff.1 (hXcA hgX) a₀ ha₀).symm
    rw [hZ, mem_bot] at ha₀Z
    exact ha₀1 ha₀Z

theorem singleComponentCleanAt_of_bigComponentUniqueAt {P : (S : Type) → [Group S] → Prop}
    (h : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → P T →
      ∃ r : ℕ, r.Prime ∧ BigComponentUniqueAt r T ∧ CentralizerGenerationAt r T) :
    SingleComponentCleanAt P := by
  intro T _ _ hT hP X Y hXq hYq hXr hYr hXY hXc hYc
  obtain ⟨r, hr, hU, hG⟩ := h T hT hP
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hT
  obtain ⟨A, hAY, hAe, hAc⟩ := exists_fourGroup_of_two_le_pRank hYr
  refine false_of_bigComponentUniqueAt hU hG hXq hXr hAe hAc
    (eq_bot_iff.2 ((commutator_mono le_rfl hAY).trans hXY.le)) fun a ha ha1 => ?_
  have hord : orderOf a = 2 :=
    orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  exact isComponentOf_of_isTwoComponentIn (hXc a (hAY ha) hord) hXq

theorem bigComponentUniqueAt_of_mulEquiv {T T' : Type} [Group T] [Group T'] [Finite T]
    [Finite T'] (e : T ≃* T') {r : ℕ} (h : BigComponentUniqueAt r T') :
    BigComponentUniqueAt r T := by
  intro a ha L L' hL hL' hr hr'
  have hmap : ∀ M : Subgroup T, CFSG.Assembly.IsComponentOf M (centralizer ({a} : Set T)) →
      CFSG.Assembly.IsComponentOf (M.map e.toMonoidHom) (centralizer ({e a} : Set T')) := by
    intro M hM
    have := (isComponentOf_map_iff (f := e.toMonoidHom) e.injective).2 hM
    rwa [map_centralizer_singleton_of_injective (f := e.toMonoidHom) e.injective,
      MonoidHom.range_eq_top.2 e.surjective, top_inf_eq] at this
  have hp : ∀ M : Subgroup T, 2 ≤ CFSG.Open.pRank 2 M →
      2 ≤ CFSG.Open.pRank 2 (M.map e.toMonoidHom) :=
    fun M hM => hM.trans (SectionRank.pRank_le_map (by norm_num) e.toMonoidHom e.injective M)
  obtain ⟨h1, h2⟩ := h (e a) (by rw [MulEquiv.orderOf_eq]; exact ha) _ _ (hmap L hL)
    (hmap L' hL') (hp L hr) (hp L' hr')
  exact ⟨Subgroup.map_injective e.injective h1,
    by rwa [card_map_of_injective (f := e.toMonoidHom) e.injective] at h2⟩

theorem centralizerGenerationAt_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    {r : ℕ} (h : CentralizerGenerationAt r T') : CentralizerGenerationAt r T := by
  intro A R hA hAc hRp hR1 hAR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 A := hA
  have htop := h (A.map e.toMonoidHom) (R.map e.toMonoidHom) (CFSG.IsElementaryAbelian.map _)
    (by rwa [card_map_of_injective (f := e.toMonoidHom) e.injective]) (hRp.map e.toMonoidHom)
    (by rwa [Ne, map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective])
    ((map_mono hAR).trans (le_normalizer_map _))
  set S := ⨆ a ∈ A, ⨆ (_ : a ≠ 1), centralizer ({a} : Set T)
  have hS : S.map e.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup₂_le fun a' ha' => iSup_le fun ha'1 => ?_
    obtain ⟨a, ha, rfl⟩ := mem_map.1 ha'
    have ha1 : a ≠ 1 := fun h1 => ha'1 (by rw [h1, map_one])
    have hC : centralizer ({e.toMonoidHom a} : Set T') =
        (centralizer ({a} : Set T)).map e.toMonoidHom := by
      rw [map_centralizer_singleton_of_injective (f := e.toMonoidHom) e.injective,
        MonoidHom.range_eq_top.2 e.surjective, top_inf_eq]
    rw [hC]
    exact map_mono (le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl))
  have := congrArg (Subgroup.comap e.toMonoidHom) hS
  rwa [comap_map_eq_self_of_injective e.injective, comap_top] at this

theorem bigComponentUniqueAt_of_forms {C : Type} [Group C] [Finite C] {K : Type} [Field K]
    [Finite K] (hK : ringChar K ≠ 2)
    (h : ∀ c : C, orderOf c = 2 → SLComponentForm K (centralizer ({c} : Set C)) ∧
      NonSLComponentUnique K (centralizer ({c} : Set C))) :
    BigComponentUniqueAt (ringChar K) C := by
  intro c hc L L' hL hL' hr hr'
  obtain ⟨hform, huniq⟩ := h c hc
  have hLc := (isComponentOf_iff_isComponent_subgroupOf hL.1).1 hL
  have hL'c := (isComponentOf_iff_isComponent_subgroupOf hL'.1).1 hL'
  have hnSL : ∀ M : Subgroup C, ∀ hM : M ≤ centralizer ({c} : Set C),
      2 ≤ CFSG.Open.pRank 2 M →
        ¬ Nonempty (M.subgroupOf (centralizer ({c} : Set C)) ≃* SL(2, K)) := by
    rintro M hM hMr ⟨f⟩
    have := pRank_le_one_of_mulEquiv_SL hK ((subgroupOfEquivOfLe hM).symm.trans f)
    omega
  refine ⟨?_, ?_⟩
  · have heq := huniq _ _ hLc hL'c (hnSL L hL.1 hr) (hnSL L' hL'.1 hr')
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hL.1, inf_of_le_left hL'.1] at heq
    exact heq
  · rcases hform _ hLc with hSL | ⟨hdvd, -⟩
    · exact absurd hSL (hnSL L hL.1 hr)
    · rw [← Nat.card_congr (subgroupOfEquivOfLe hL.1).toEquiv]
      exact (ringChar_dvd_card_SL K).trans hdvd

@[expose] def OddExcInnerDiagNonSLUnique (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → Nat.card K = p ^ f →
    ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
        (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) → orderOf α = 2 →
      NonSLComponentUnique K (fixedSubgroup α)

theorem conj_innerDiag {τ : Tag} {K : Type} [Field K]
    (hZ : center (adjointGroup τ K) = ⊥) {c : adjointGroup τ K} (hc : orderOf c = 2) :
    (∀ h : adjointGroup τ K, ((MulAut.conj c) h : ModGL τ K) = (c : ModGL τ K) *
      rootDiagUnit τ (1 : Fin τ.rank → Kˣ) * (h : ModGL τ K) *
        (rootDiagUnit τ (1 : Fin τ.rank → Kˣ))⁻¹ * (c : ModGL τ K)⁻¹) ∧
      orderOf (MulAut.conj c) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun h => ?_, ?_⟩
  · simp [rootDiagUnit_one, MulAut.conj_apply]
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
    · intro h1
      have hcZ : c ∈ center (adjointGroup τ K) := by
        rw [mem_center_iff]
        intro g
        have := congrArg (fun φ : MulAut (adjointGroup τ K) => φ g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc g * c = c * g * c⁻¹ * c := by rw [this]
          _ = c * g := by group
      rw [hZ, mem_bot] at hcZ
      rw [hcZ, orderOf_one] at hc
      exact absurd hc (by norm_num)

theorem bigComponentUniqueAt_adjointGroup {τ : Tag} (hform : OddExcInnerDiagSLForm τ)
    (huniq : OddExcInnerDiagNonSLUnique τ) {K : Type} [Field K] [Finite K]
    [Finite (ModGL τ K)] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (hZ : center (adjointGroup τ K) = ⊥) :
    BigComponentUniqueAt (ringChar K) (adjointGroup τ K) := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      exact absurd hK (Finite.one_lt_card).ne'
    · exact h0
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine bigComponentUniqueAt_of_forms hK2 fun c hc => ?_
  obtain ⟨hαg, hαo⟩ := conj_innerDiag hZ hc
  let e : centralizer ({c} : Set (adjointGroup τ K)) ≃* fixedSubgroup (MulAut.conj c) :=
    MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizer c).symm
  exact ⟨slComponentForm_of_mulEquiv e (hform K p f hp hp2 hK _ c 1 hαg hαo).2,
    nonSLComponentUnique_of_mulEquiv e (huniq K p f hp hp2 hK _ c 1 hαg hαo)⟩

theorem centralizerGenerationAt_adjointGroup
    (τ : Tag) (K : Type) [Field K] [Finite K] [IsSimpleGroup (adjointGroup τ K)]
    (hK2 : ringChar K ≠ 2) : CentralizerGenerationAt (ringChar K) (adjointGroup τ K) := by
  intro A R hA hAc hRp hR1 hAR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 A := hA
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set ι := (adjointGroup τ K).subtype
  have hι : Function.Injective ι := (adjointGroup τ K).subtype_injective
  have : CFSG.IsElementaryAbelian 2 (A.map ι) := CFSG.IsElementaryAbelian.map ι
  have hgen := ordinary_root_invariant_prime_subgroup_centralizer_generation τ K (ringChar K) 2
    hK2 (A.map ι) (map_subtype_le A) (by rwa [card_map_of_injective hι]) (R.map ι)
    (map_subtype_le R) (hRp.map ι) (by rwa [Ne, map_eq_bot_iff_of_injective _ hι])
    ((map_mono hAR).trans (le_normalizer_map _))
  set S := ⨆ a ∈ A, ⨆ (_ : a ≠ 1), centralizer ({a} : Set (adjointGroup τ K))
  have hS : (⊤ : Subgroup (adjointGroup τ K)).map ι ≤ S.map ι := by
    have h1 : (⊤ : Subgroup (adjointGroup τ K)).map ι = adjointGroup τ K := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [h1]
    refine le_trans hgen.symm.le ?_
    refine iSup₂_le fun a' ha' => iSup_le fun ha'1 => ?_
    obtain ⟨a, ha, rfl⟩ := mem_map.1 ha'
    have ha1 : a ≠ 1 := fun h1 => ha'1 (by rw [h1, map_one])
    have hC : adjointGroup τ K ⊓ centralizer ({ι a} : Set (ModGL τ K)) =
        (centralizer ({a} : Set (adjointGroup τ K))).map ι := by
      rw [map_centralizer_singleton_of_injective hι, range_subtype]
    rw [hC]
    exact map_mono (le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl))
  exact eq_top_iff.2 ((map_le_map_iff_of_injective hι).1 hS)

end CFSG.ComponentClassification.Sol76.Sig
