module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Constrained
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ : Subgroup X}

theorem isElemAbelian_sup_zpowers_of_mem_centralizer (hp : p.Prime) {J : Subgroup X}
    (hJ : IsElemAbelian p J) {t : X} (ht : t ^ p = 1)
    (htC : t ∈ Subgroup.centralizer (J : Set X)) (htJ : t ∉ J) :
    IsElemAbelian p (J ⊔ Subgroup.zpowers t) ∧
      p * Nat.card J ≤ Nat.card (J ⊔ Subgroup.zpowers t : Subgroup X) := by
  have : Fact p.Prime := ⟨hp⟩
  have hJt : IsElemAbelian p (J ⊔ Subgroup.zpowers t) :=
    elementary_abelian_sup_of_commuting p hJ (isElemAbelian_zpowers ht)
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr htC))
  refine ⟨hJt, prime_mul_card_le_of_lt (elementary_isPGroup p _ hJt)
    (lt_of_le_of_ne le_sup_left fun heq => htJ ?_)⟩
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem two_le_pRank_of_mem_centralizer_zpowers (hp : p.Prime) {H : Subgroup X} {a b : X}
    (ha : orderOf a = p) (hb : orderOf b = p)
    (hab : b ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X))
    (hbn : b ∉ Subgroup.zpowers a) (haH : a ∈ H) (hbH : b ∈ H) : 2 ≤ Open.pRank p H := by
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  obtain ⟨hE, hcard⟩ := isElemAbelian_sup_zpowers_of_mem_centralizer hp
    (isElemAbelian_zpowers hap) hbp hab hbn
  rw [Nat.card_zpowers, ha] at hcard
  exact le_pRank_of_isElemAbelian_of_pow_le_card hp hE
    (sup_le (Subgroup.zpowers_le.mpr haH) (Subgroup.zpowers_le.mpr hbH))
    (by rw [pow_two]; exact hcard)

theorem three_le_pRank_of_mem_centralizer_zpowers (hp : p.Prime) {H : Subgroup X} {a b c : X}
    (ha : orderOf a = p) (hb : orderOf b = p) (hc : orderOf c = p)
    (hab : b ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X))
    (hbn : b ∉ Subgroup.zpowers a)
    (hac : c ∈ Subgroup.centralizer
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) : Set X))
    (hcn : c ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers b) (haH : a ∈ H) (hbH : b ∈ H)
    (hcH : c ∈ H) : 3 ≤ Open.pRank p H := by
  have hap : a ^ p = 1 := ha ▸ pow_orderOf_eq_one a
  have hbp : b ^ p = 1 := hb ▸ pow_orderOf_eq_one b
  have hcp : c ^ p = 1 := hc ▸ pow_orderOf_eq_one c
  obtain ⟨hE, hcard⟩ := isElemAbelian_sup_zpowers_of_mem_centralizer hp
    (isElemAbelian_zpowers hap) hbp hab hbn
  obtain ⟨hE', hcard'⟩ := isElemAbelian_sup_zpowers_of_mem_centralizer hp hE hcp hac hcn
  rw [Nat.card_zpowers, ha] at hcard
  refine le_pRank_of_isElemAbelian_of_pow_le_card hp hE'
    (sup_le (sup_le (Subgroup.zpowers_le.mpr haH) (Subgroup.zpowers_le.mpr hbH))
      (Subgroup.zpowers_le.mpr hcH)) ?_
  calc p ^ 3 = p * (p * p) := by ring
    _ ≤ p * Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) :=
      Nat.mul_le_mul_left p hcard
    _ ≤ _ := hcard'

theorem le_centralizer_of_ne_isComponentOf {K L : Subgroup X} (hK : IsComponentOf K ⊤)
    (hL : IsComponentOf L ⊤) (hKL : K ≠ L) : K ≤ Subgroup.centralizer (L : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (ComponentClassification.LocalComponents.commute_of_ne K L hK hL hKL)

omit [Finite X] in
theorem isComponentOf_map_conj_top {K : Subgroup X} (hK : IsComponentOf K ⊤) (g : X) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.isComponent_iff_open _).mp (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g)
    ((CFSG.isComponent_iff_open K).mpr hK))

omit [Finite X] in
theorem map_map_conj_eq_map_conj_mul (K : Subgroup X) (g g' : X) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g').toMonoidHom =
      K.map (MulAut.conj (g' * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite X] in
theorem normal_sup_of_forall_isComponentOf {K L : Subgroup X} (hK : IsComponentOf K ⊤)
    (hL : IsComponentOf L ⊤) (hall : ∀ M : Subgroup X, IsComponentOf M ⊤ → M = K ∨ M = L) :
    (K ⊔ L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hmem : g * n * g⁻¹ ∈ (K ⊔ L).map (MulAut.conj g).toMonoidHom := ⟨n, hn, by simp⟩
  rw [Subgroup.map_sup] at hmem
  refine (sup_le ?_ ?_ : K.map (MulAut.conj g).toMonoidHom ⊔ L.map (MulAut.conj g).toMonoidHom ≤
    K ⊔ L) hmem
  · rcases hall _ (isComponentOf_map_conj_top hK g) with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right
  · rcases hall _ (isComponentOf_map_conj_top hL g) with h | h
    · rw [h]
      exact le_sup_left
    · rw [h]
      exact le_sup_right

theorem exists_orderOf_eq_mem_centralizer_of_le_normalizer (hp : p.Prime) {S T : Subgroup X}
    (hS : IsPGroup p S) (hTS : T ≤ S) (hTn : S ≤ Subgroup.normalizer (T : Set X)) (hT : T ≠ ⊥) :
    ∃ z ∈ T, orderOf z = p ∧ z ∈ Subgroup.centralizer (S : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have : (T.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr hTn
  have hT' : T.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hT
    rw [Subgroup.eq_bot_iff_forall] at hbot ⊢
    intro x hx
    exact congrArg Subtype.val (hbot ⟨x, hTS hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hT'
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hS.to_subgroup (T.subgroupOf S ⊓ Subgroup.center S))
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hW (Subgroup.card_eq_one.mp (by simpa using hn))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p (hn ▸ dvd_pow_self p hn0)
  refine ⟨((w : S) : X), Subgroup.mem_subgroupOf.mp w.2.1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2.2 ⟨s, hs⟩)

namespace D2Reduced

theorem center_eq_bot (h : D2Reduced p X R A X₀) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    Subgroup.center K = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hKc : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).mpr hK
  have hZ : (Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype =
      CFSG.layer X ⊓ Subgroup.centralizer (CFSG.layer X : Set X) := by
    ext g
    rw [CFSG.LocalCores.mem_map_center_iff, Subgroup.mem_inf]
  have : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hn : ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype).Normal := by
    rw [hZ]
    infer_instance
  have : IsMulCommutative ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype) :=
    Subgroup.map_isMulCommutative _ _
  have hnil : Group.IsNilpotent ((Subgroup.center (CFSG.layer X)).map (CFSG.layer X).subtype) :=
    CommGroup.isNilpotent
  have hF : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X p h.core_eq_bot]
    exact h.pCore_eq_bot
  have hle : (Subgroup.center K).map K.subtype ≤ ⊥ :=
    hF ▸ (CFSG.LocalCores.center_component_le_center_layer hKc).trans (le_sSup ⟨hn, hnil⟩)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact Subtype.ext (Subgroup.mem_bot.mp (hle ⟨z, hz, rfl⟩))

theorem false_of_three_components (h : D2Reduced p X R A X₀) {K₁ K₂ K₃ : Subgroup X}
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (h₃ : IsComponentOf K₃ ⊤)
    (h₁₂ : K₁ ≠ K₂) (h₁₃ : K₁ ≠ K₃) (h₂₃ : K₂ ≠ K₃) : False := by
  have hp := h.prime
  obtain ⟨t₁, ⟨-, ht₁K⟩, ht₁, ht₁Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₁
  obtain ⟨t₂, ⟨-, ht₂K⟩, ht₂, ht₂Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₂
  obtain ⟨t₃, ⟨-, ht₃K⟩, ht₃, ht₃Z⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₃
  have c12 := le_centralizer_of_ne_isComponentOf h₁ h₂ h₁₂
  have c13 := le_centralizer_of_ne_isComponentOf h₁ h₃ h₁₃
  have c23 := le_centralizer_of_ne_isComponentOf h₂ h₃ h₂₃
  have hz1 : Subgroup.zpowers t₁ ≤ Subgroup.centralizer (K₂ : Set X) :=
    (Subgroup.zpowers_le.mpr ht₁K).trans c12
  have hz2 : Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ ≤ Subgroup.centralizer (K₃ : Set X) :=
    sup_le ((Subgroup.zpowers_le.mpr ht₁K).trans c13) ((Subgroup.zpowers_le.mpr ht₂K).trans c23)
  have hrank : 3 ≤ Open.pRank p (⊤ : Subgroup X) :=
    three_le_pRank_of_mem_centralizer_zpowers hp ht₁ ht₂ ht₃
      (Subgroup.le_centralizer_iff.mp hz1 ht₂K) (fun hmem => ht₂Z (hz1 hmem))
      (Subgroup.le_centralizer_iff.mp hz2 ht₃K) (fun hmem => ht₃Z (hz2 hmem))
      (Subgroup.mem_top _) (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hR : Open.pRank p (⊤ : Subgroup X) = 2 := by
    rw [← pRank_sylow_eq_globalRank p hp R]
    exact h.pRank_eq
  omega

theorem le_normalizer (h : D2Reduced p X R A X₀) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    (R : Subgroup X) ≤ Subgroup.normalizer (K : Set X) := by
  intro r hr
  obtain ⟨k, hk⟩ : ∃ k : ℕ, r ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨r, hr⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  obtain ⟨m, hm⟩ : Odd (p ^ k) := (h.prime.eq_two_or_odd'.resolve_left h.ne_two).pow
  by_contra hrn
  have hK₁ := isComponentOf_map_conj_top hK r
  have hK₂ := isComponentOf_map_conj_top hK₁ r
  have hsq : r * r ∈ Subgroup.normalizer (K : Set X) := by
    by_contra hsq
    refine h.false_of_three_components hK hK₁ hK₂ ?_ ?_ ?_
    · intro heq
      exact hrn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
    · intro heq
      rw [map_map_conj_eq_map_conj_mul] at heq
      exact hsq (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
    · intro heq
      exact hrn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (Subgroup.map_injective (MulAut.conj r).injective heq).symm)
  have hr' : r = (r * r) ^ (m + 1) := by
    calc r = r ^ (p ^ k) * r := by rw [hk, one_mul]
      _ = (r * r) ^ (m + 1) := by
        rw [hm, ← pow_succ, ← sq, ← pow_mul]
        congr 1
  exact hrn (hr' ▸ Subgroup.pow_mem _ hsq _)

theorem inf_eq_bot_of_ne_isComponentOf (h : D2Reduced p X R A X₀) {K L : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤) (hKL : K ≠ L) : K ⊓ L = ⊥ := by
  have hLC : L ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.le_centralizer_iff.mp (le_centralizer_of_ne_isComponentOf hK hL hKL)
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzL⟩
  have hz : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLC hzL) g g.2)
  rw [h.center_eq_bot hK] at hz
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hz))

theorem inf_ne_bot_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : (R : Subgroup X) ⊓ K ≠ ⊥ := by
  obtain ⟨t, ⟨htR, htK⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component h.prime h.ne_two h.core_eq_bot R hK
  intro hbot
  have hmem : t ∈ (⊥ : Subgroup X) := hbot ▸ ⟨htR, htK⟩
  rw [Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at ht
  exact h.prime.one_lt.ne ht

theorem le_normalizer_inf_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    (R : Subgroup X) ≤ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
  (le_inf Subgroup.le_normalizer (h.le_normalizer hK)).trans
    Subgroup.inf_normalizer_le_normalizer_inf

theorem exists_mem_A_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    ∃ z ∈ K, z ∈ A ∧ z ∈ (R : Subgroup X) ∧ orderOf z = p := by
  obtain ⟨z, ⟨hzR, hzK⟩, hz, hzC⟩ := exists_orderOf_eq_mem_centralizer_of_le_normalizer
    h.prime R.isPGroup' inf_le_left (h.le_normalizer_inf_of_isComponentOf hK)
    (h.inf_ne_bot_of_isComponentOf hK)
  exact ⟨z, hzK, h.mem_A_of_mem_center hzR hzC hz, hzR, hz⟩

theorem le_of_ne_isComponentOf (h : D2Reduced p X R A X₀) {K L : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤) (hKL : K ≠ L) : K ≤ X₀ := by
  obtain ⟨z, hzL, hzA, -, hz⟩ := h.exists_mem_A_of_isComponentOf hL
  have hz1 : Subgroup.zpowers z ≠ ⊥ := by
    intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    rw [hbot, orderOf_one] at hz
    exact h.prime.one_lt.ne hz
  exact ((le_centralizer_of_ne_isComponentOf hK hL hKL).trans
    (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hzL))).trans
    ((Subgroup.centralizer_le_normalizer _).trans
      (h.normalizer_le_of_le_A _ (Subgroup.zpowers_le.mpr hzA) hz1))

theorem eq_of_isComponentOf (h : D2Reduced p X R A X₀) {K L : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤) : K = L := by
  by_contra hKL
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hall : ∀ M : Subgroup X, IsComponentOf M ⊤ → M = K ∨ M = L := by
    intro M hM
    by_contra hne
    rw [not_or] at hne
    exact h.false_of_three_components hK hL hM hKL (Ne.symm hne.1) (Ne.symm hne.2)
  have hN : (K ⊔ L).Normal := normal_sup_of_forall_isComponentOf hK hL hall
  obtain ⟨zK, hzKK, -, hzKR, hzK⟩ := h.exists_mem_A_of_isComponentOf hK
  obtain ⟨zL, hzLL, -, hzLR, hzL⟩ := h.exists_mem_A_of_isComponentOf hL
  have hKC : K ≤ Subgroup.centralizer (L : Set X) := le_centralizer_of_ne_isComponentOf hK hL hKL
  have hzLK : zL ∉ Subgroup.zpowers zK := by
    intro hmem
    have : zL ∈ K ⊓ L := ⟨(Subgroup.zpowers_le.mpr hzKK) hmem, hzLL⟩
    rw [h.inf_eq_bot_of_ne_isComponentOf hK hL hKL, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hzL
    exact hp.one_lt.ne hzL
  have hrank : 2 ≤ Open.pRank p ((R : Subgroup X) ⊓ (K ⊔ L)) :=
    two_le_pRank_of_mem_centralizer_zpowers hp hzK hzL
      (Subgroup.le_centralizer_iff.mp ((Subgroup.zpowers_le.mpr hzKK).trans hKC) hzLL) hzLK
      ⟨hzKR, Subgroup.mem_sup_left hzKK⟩ ⟨hzLR, Subgroup.mem_sup_right hzLL⟩
  have hN₀ : Subgroup.normalizer (((R : Subgroup X) ⊓ (K ⊔ L) : Subgroup X) : Set X) ≤ X₀ :=
    h.normalizer_le_of_rank _ (inf_le_left.trans h.sylow_le) R.isPGroup'.to_inf_left hrank
  exact not_le_of_normalizer_inf_le R hN₀ h.ne_top
    (sup_le (h.le_of_ne_isComponentOf hK hL hKL) (h.le_of_ne_isComponentOf hL hK (Ne.symm hKL)))

theorem normal_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : K.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hKg : K.map (MulAut.conj g).toMonoidHom = K :=
    h.eq_of_isComponentOf (isComponentOf_map_conj_top hK g) hK
  have hmem : g * n * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := ⟨n, hn, by simp⟩
  rwa [hKg] at hmem

theorem not_le_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : ¬ K ≤ X₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : K.Normal := h.normal_of_isComponentOf hK
  exact not_le_of_normalizer_inf_le R
    (h.normalizer_le_of_normal inf_le_left (h.le_normalizer_inf_of_isComponentOf hK)
      (h.inf_ne_bot_of_isComponentOf hK)) h.ne_top

theorem centralizer_eq_bot_of_isComponentOf (h : D2Reduced p X R A X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : Subgroup.centralizer (K : Set X) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X p h.core_eq_bot]
    exact h.pCore_eq_bot
  have hE : CFSG.layer X = K :=
    le_antisymm (sSup_le fun M hM =>
      (h.eq_of_isComponentOf ((CFSG.isComponent_iff_open M).mp hM) hK).le)
      (le_layer_of_isComponentOf hK)
  have hFs : CFSG.generalizedFitting X = K := by
    rw [CFSG.generalizedFitting, hF, hE, bot_sup_eq]
  have hC : Subgroup.centralizer (K : Set X) ≤ K := hFs ▸ CFSG.centralizer_generalizedFitting_le X
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzK : z ∈ K := hC hz
  have hZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hz g g.2)
  rw [h.center_eq_bot hK] at hZ
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hZ)

end D2Reduced

end CFSG.AGLEmbeddingD2
