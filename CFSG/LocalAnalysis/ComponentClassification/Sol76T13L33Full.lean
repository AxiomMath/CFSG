module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L315a

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient}

omit [Finite G] in
theorem le_normalizer_inf' {A B X : Subgroup G} (hA : X ≤ normalizer (A : Set G))
    (hB : X ≤ normalizer (B : Set G)) : X ≤ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_iff.mpr fun y => ?_
  exact and_congr (mem_normalizer_iff.mp (hA hx) y) (mem_normalizer_iff.mp (hB hx) y)

theorem exists_commute_mem_coset {J : Subgroup G} {b : G} (hbN : b ∈ normalizer (J : Set G))
    (hb2 : orderOf b = 2) {j : G} (hj : j ∈ J) (hjb : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn J) :
    ∃ c ∈ J, c * b = b * c ∧ c * j⁻¹ ∈ oddCoreIn J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := J ⊔ zpowers b with hY
  set bY : ↥Y := ⟨b, mem_sup_right (mem_zpowers b)⟩ with hbY
  set jY : ↥Y := ⟨j, mem_sup_left hj⟩ with hjY
  set A := zpowers bY with hA
  have hbY2 : orderOf bY = 2 := by rw [← orderOf_coe]; exact hb2
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbY2, pow_one])
  set α : ↥A →* MulAut ↥Y := MulAut.conj.comp A.subtype with hα
  have hαx : ∀ (x : ↥A) (y : ↥Y), α x y = (x : ↥Y) * y * (x : ↥Y)⁻¹ := fun _ _ => rfl
  set H : Subgroup ↥Y := (oddCoreIn J).subgroupOf Y with hH
  have hOY : oddCoreIn J ≤ Y := (map_subtype_le _).trans le_sup_left
  have hcop : ¬ 2 ∣ Nat.card H := by
    have h1 : Nat.card H = Nat.card (oddCoreIn J) :=
      Nat.card_congr (subgroupOfEquivOfLe hOY).toEquiv
    rw [h1]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn J)
  have hbO : b ∈ normalizer (oddCoreIn J : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hbN)
  have hbmem : ∀ y : ↥Y, y * jY⁻¹ ∈ H → bY * y * bY⁻¹ * jY⁻¹ ∈ H := by
    intro y hy
    have hy' : (y : G) * j⁻¹ ∈ oddCoreIn J := mem_subgroupOf.mp hy
    have h1 : b * ((y : G) * j⁻¹) * b⁻¹ ∈ oddCoreIn J := (mem_normalizer_iff.mp hbO _).mp hy'
    have h2 : b * (y : G) * b⁻¹ * j⁻¹ = b * ((y : G) * j⁻¹) * b⁻¹ * (b * j * b⁻¹ * j⁻¹) := by
      group
    refine mem_subgroupOf.mpr ?_
    show b * (y : G) * b⁻¹ * j⁻¹ ∈ oddCoreIn J
    rw [h2]
    exact mul_mem h1 hjb
  have hbb : bY * bY = 1 := by rw [← pow_two, ← hbY2, pow_orderOf_eq_one]
  have hk : ∀ k : ℤ, bY ^ k = 1 ∨ bY ^ k = bY := by
    intro k
    obtain ⟨m, hm⟩ | ⟨m, hm⟩ := Int.even_or_odd k
    · left
      rw [hm, ← two_mul, zpow_mul, zpow_two, hbb, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, zpow_two, hbb, one_zpow, one_mul, zpow_one]
  have hinvt : ∀ x : ↥A, ∀ y : ↥Y, y * jY⁻¹ ∈ H → α x y * jY⁻¹ ∈ H := by
    rintro ⟨x, hx⟩ y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [hαx]
    show bY ^ k * y * (bY ^ k)⁻¹ * jY⁻¹ ∈ H
    rcases hk k with h | h
    · rw [h, one_mul, inv_one, mul_one]
      exact hy
    · rw [h]
      exact hbmem y hy
  obtain ⟨c, hc, hfix⟩ :=
    (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA2 α H hcop jY).1 hinvt
  have hcb : bY * c * bY⁻¹ = c := hfix ⟨bY, mem_zpowers bY⟩
  have hcO : (c : G) * j⁻¹ ∈ oddCoreIn J := mem_subgroupOf.mp hc
  refine ⟨c, ?_, ?_, hcO⟩
  · have h1 := mul_mem ((map_subtype_le _) hcO) hj
    rwa [inv_mul_cancel_right] at h1
  · have h' : b * (c : G) * b⁻¹ = c := congrArg Subtype.val hcb
    calc (c : G) * b = b * (c : G) * b⁻¹ * b := by rw [h']
      _ = b * c := by group

theorem le_sup_coreActionKernel_of_card {J K : Subgroup G} (hKq : IsQuasisimple ↥K)
    (hJQ : J ≤ normalizer (coreActionKernel J : Set G))
    (hKQ : K ≤ normalizer (coreActionKernel J : Set G))
    (hKJQ : K ≤ J ⊔ coreActionKernel J) (hmove : ¬ K ≤ coreActionKernel J)
    (hcard : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥K ⧸ center ↥K)) :
    J ≤ K ⊔ coreActionKernel J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := coreActionKernel J with hQ
  have hle : K ⊔ Q ≤ J ⊔ Q := sup_le hKJQ le_sup_right
  have hKZ : Q.subgroupOf K ≤ center ↥K := by
    have hn : (Q.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKQ
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hKq hn.isSubnormal with
      h | h
    · exfalso
      apply hmove
      intro k hk
      have hk' : (⟨k, hk⟩ : ↥K) ∈ Q.subgroupOf K := by rw [h]; exact mem_top _
      exact mem_subgroupOf.mp hk'
    · exact h
  have hZJ : Open.fusionZStar ↥J ≤ Q.subgroupOf J := by
    intro z hz
    rw [mem_fusionZStar_iff_forall] at hz
    refine mem_subgroupOf.mpr ⟨le_normalizer z.2, fun j hj => ?_⟩
    have h1 := hz ⟨j⁻¹, inv_mem hj⟩
    have h2 : (j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹) ∈ oddCoreIn J := mem_map_of_mem J.subtype h1
    have h3 : j⁻¹ * ((j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹)) * j⁻¹⁻¹ ∈ oddCoreIn J :=
      (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J (inv_mem hj)) _).mp h2
    rw [show j⁻¹ * ((j⁻¹ * (z : G))⁻¹ * ((z : G) * j⁻¹)) * j⁻¹⁻¹ = j⁻¹ * (z : G)⁻¹ * j * z by
      group] at h3
    exact h3
  have hcardsup : ∀ {X : Subgroup G}, X ≤ normalizer (Q : Set G) →
      Nat.card ↥(X ⊔ Q) = Nat.card ↥Q * (Q.subgroupOf X).index := by
    intro X hX
    have := Subgroup.normal_subgroupOf_of_le_normalizer hX
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hX
    have h1 := Subgroup.card_mul_index (Q.subgroupOf (X ⊔ Q))
    have h2 : Nat.card ↥(Q.subgroupOf (X ⊔ Q)) = Nat.card ↥Q :=
      Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
    have h3 : (Q.subgroupOf (X ⊔ Q)).index = (Q.subgroupOf X).index :=
      (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient X Q hX).toEquiv).symm
    rw [← h1, h2, h3]
  have hidx1 : (Q.subgroupOf J).index ≤ (Open.fusionZStar ↥J).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hZJ)
  have hidx2 : (center ↥K).index ≤ (Q.subgroupOf K).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hKZ)
  have hidx3 : (Open.fusionZStar ↥J).index = (center ↥K).index := hcard
  have heq : K ⊔ Q = J ⊔ Q := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardsup hKQ, hcardsup hJQ]
    exact Nat.mul_le_mul_left _ (hidx1.trans (hidx3.le.trans hidx2))
  rw [heq]
  exact le_sup_left

omit [Finite G] in
theorem sup_oddCoreIn_eq_of_forall_coreActionKernel {B J : Subgroup G} (hBJ : B ≤ J)
    (hJperf : ⁅J, J⁆ = J) (hdec : ∀ j ∈ J, ∃ b ∈ B, b⁻¹ * j ∈ coreActionKernel J) :
    B ⊔ oddCoreIn J = J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π₂ := QuotientGroup.mk' (pPrimeCore 2 ↥J) with hπ₂
  set Bbar := (B.subgroupOf J).map π₂ with hBbar
  have hZc : ∀ z : ↥J, (z : G) ∈ coreActionKernel J →
      π₂ z ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
    intro z hz
    refine (mk_mem_center_iff _ z).mpr fun x => ?_
    rw [mem_pPrimeCore_iff_mem_oddCoreIn]
    have h1 : (x : G) * (z : G)⁻¹ * (x : G)⁻¹ * z ∈ oddCoreIn J := by
      have h := hz.2 (x : G)⁻¹ (inv_mem x.2)
      rwa [inv_inv] at h
    have h2 : (x : G)⁻¹ * ((x : G) * (z : G)⁻¹ * (x : G)⁻¹ * z) * (x : G)⁻¹⁻¹ ∈ oddCoreIn J :=
      (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J (inv_mem x.2)) _).mp h1
    have h3 : (((x * z)⁻¹ * (z * x) : ↥J) : G) =
        (x : G)⁻¹ * ((x : G) * (z : G)⁻¹ * (x : G)⁻¹ * z) * (x : G)⁻¹⁻¹ := by
      push_cast
      group
    rw [h3]
    exact h2
  have hJp : ⁅(⊤ : Subgroup ↥J), (⊤ : Subgroup ↥J)⁆ = (⊤ : Subgroup ↥J) := by
    apply map_injective J.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hJperf
  have hQperf : ⁅(⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)), (⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J))⁆ =
      (⊤ : Subgroup (↥J ⧸ pPrimeCore 2 ↥J)) := by
    rw [← map_top_of_surjective π₂ (QuotientGroup.mk'_surjective _), ← map_commutator, hJp]
  have hmemB : ∀ k : ↥J, (k : G) ∈ B → π₂ k ∈ Bbar := fun k hk =>
    mem_map_of_mem π₂ (show k ∈ B.subgroupOf J from hk)
  have hsurj : ∀ m : ↥J, ∃ k : ↥J, (k : G) ∈ B ∧ ((k⁻¹ * m : ↥J) : G) ∈ coreActionKernel J := by
    intro m
    obtain ⟨b, hb, hbm⟩ := hdec m m.2
    exact ⟨⟨b, hBJ hb⟩, hb, hbm⟩
  have hBtop : Bbar = ⊤ := by
    rw [eq_top_iff, ← hQperf, commutator_le]
    intro q₁ _ q₂ _
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) q₁
    obtain ⟨m₂, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) q₂
    obtain ⟨k₁, hk₁B, hk₁⟩ := hsurj m₁
    obtain ⟨k₂, hk₂B, hk₂⟩ := hsurj m₂
    have e₁ : π₂ m₁ = π₂ k₁ * π₂ (k₁⁻¹ * m₁) := by rw [← map_mul, mul_inv_cancel_left]
    have e₂ : π₂ m₂ = π₂ k₂ * π₂ (k₂⁻¹ * m₂) := by rw [← map_mul, mul_inv_cancel_left]
    rw [e₁, e₂, commutatorElement_mul_mem_center_right (hZc _ hk₂),
      commutatorElement_mul_mem_center_left (hZc _ hk₁), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hmemB k₁ hk₁B) (hmemB k₂ hk₂B)) (inv_mem (hmemB k₁ hk₁B)))
      (inv_mem (hmemB k₂ hk₂B))
  have htop : B.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
    have h := congrArg (Subgroup.comap π₂) hBtop
    rwa [hBbar, comap_map_eq, QuotientGroup.ker_mk', comap_top] at h
  have h2 := congrArg (Subgroup.map J.subtype) htop
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hBJ, ← MonoidHom.range_eq_map,
    range_subtype] at h2
  exact h2

theorem lemma33CentralInputFor_of_steps (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hq : QuasisimpleTwoPartInput)
    (h𝒜 : ∀ (G : Type) [Group G] [Finite G], 𝒜 G → KStarKProper G) :
    Lemma33CentralInputFor 𝒜 := by
  intro G _ _ hG N hN K hK a haN ha haK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set M := normalizer (D : Set G) with hM
  set Ca := centralizer ({a} : Set G) with hCa
  set La := twoLayerIn Ca with hLa
  have h316 := lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N hN
  have hKM : IsTwoComponentIn K M := by
    have h : K ∈ kStarComponents M := by
      rw [kStarComponents_normalizer_eq hbal hG hN]
      exact hK
    exact h.1
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_mem_kStarComponents h315a hG hN hK
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1.1 hK.1.2
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hKMle : K ≤ M := hKD.trans le_normalizer
  have hOK : oddCoreIn K ≤ centralizer (K : Set G) :=
    ((oddCoreIn_le_of_isTwoComponentIn (isTwoComponentIn_of_le hK.1 hKD
      (solomonKStarOf_le N))).trans (h315a G hG N hN)).trans (centralizer_le hKD)
  have hZK : Open.fusionZStar ↥K = center ↥K := by
    refine fusionZStar_eq_center_of_le' (Subgroup.isPerfect_iff.mpr hKperf).commutator_eq_top
      fun x hx => ?_
    have hx' : (x : G) ∈ oddCoreIn K := ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.mp (hOK hx')) y y.2)
  have hKL : K ≤ La :=
    (le_solomonKStarOf_centralizer hK.1 hK.2 (isPGroup_zpowers_of_orderOf_eq_two ha)
      (ne_one_of_orderOf_eq_two ha) haK).trans (solomonKStarOf_le_twoLayerIn Ca)
  have haQ : a ∈ coreActionKernel K :=
    Sol78.mem_coreActionKernel_of_commute fun k hk => mem_centralizer_singleton_iff.mp (haK hk)
  have hOCa : oddCoreIn Ca ≤ M :=
    le_normalizer_of_coprime h32 h315a h315c hbal hprod hG hN hK (coprime_card_oddCoreIn Ca)
      (haK.trans (le_normalizer_oddCoreIn Ca))
  have hKtl : twoLayerIn (K ⊓ Ca) = K := by
    rw [inf_eq_left.mpr haK, twoLayerIn_eq_self_of_isTwoComponentIn hK.1]
  have hKq' : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2
  have hnc := exists_noncentral_involution_coreQuot hq (h𝒜 G hG) hK.1 hK.2
  have hKres : oddResidualIn K = K := oddResidualIn_eq_self_of_isPComponent hK.1.1 hK.1.2
  have key : ∀ J ∈ pumpSet K Ca, J = K := by
    intro J hJ
    have hJC : IsTwoComponentIn J Ca := hJ.1.1
    have hmove : ¬ K ≤ coreActionKernel J := by
      rw [← hKtl]
      exact hJ.2
    have hJperf : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJC.1 hJC.2
    have hequiv := solomonEquiv_of_not_le_coreActionKernel ha hK.1 hK.2.1 haK hKL hJC hmove
    obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
    have hcard : Nat.card (↥J ⧸ Open.fusionZStar ↥J) = Nat.card (↥K ⧸ center ↥K) := by
      rw [← hZK]
      exact (Nat.card_congr e.toEquiv).symm
    set Q := coreActionKernel J with hQ
    have hJQ : J ≤ normalizer (Q : Set G) := fun j hj =>
      FooteLit.mem_normalizer_coreActionKernel (le_normalizer hj)
    have hKJ : K ≤ normalizer (J : Set G) :=
      hKL.trans (FooteLit.twoLayerIn_le_normalizer hJC.1 hJC.2)
    have hKQ : K ≤ normalizer (Q : Set G) := fun k hk =>
      FooteLit.mem_normalizer_coreActionKernel (hKJ hk)
    have hLJQ : La ≤ J ⊔ Q := twoLayerIn_le_of_forall fun P hP => by
      by_cases hPJ : P = J
      · rw [hPJ]
        exact le_sup_left
      · exact (GSThmB.B5a.le_coreActionKernel_of_ne hJC.1 hP.1 hJC.2 hP.2 (Ne.symm hPJ)).trans
          le_sup_right
    have hKJQ : K ≤ J ⊔ Q := hKL.trans hLJQ
    have hJKQ : J ≤ K ⊔ Q := le_sup_coreActionKernel_of_card hKq hJQ hKQ hKJQ hmove hcard
    have hOJM : oddCoreIn J ≤ M := (oddCoreIn_le_of_isTwoComponentIn hJC).trans hOCa
    have hinv : ∀ b ∈ K, orderOf b = 2 → b ∈ Q ⊔ (J ⊓ M) := by
      intro b hb hb2
      have hbQJ : b ∈ Q ⊔ J := by
        rw [sup_comm]
        exact hKJQ hb
      obtain ⟨q, hqQ, j, hj, hbqj⟩ := exists_mul_of_mem_sup_normalizer hJQ hbQJ
      have hqO : q ∈ normalizer (oddCoreIn J : Set G) :=
        mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hqQ.1)
      have hfix : b * j * b⁻¹ * j⁻¹ ∈ oddCoreIn J := by
        have h1 : j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q ∈ oddCoreIn J := hqQ.2 j⁻¹ (inv_mem hj)
        have h2 : q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ ∈ oddCoreIn J :=
          (mem_normalizer_iff.mp hqO _).mp h1
        rw [hbqj, show q * j * j * (q * j)⁻¹ * j⁻¹ = q * (j⁻¹⁻¹ * q⁻¹ * j⁻¹ * q) * q⁻¹ by
          group]
        exact h2
      obtain ⟨c, -, hcb, hcO⟩ := exists_commute_mem_coset (hKJ hb) hb2 hj hfix
      have hcM : c ∈ M := h316.2 K hK b hb hb2 (mem_centralizer_singleton_iff.mpr hcb)
      have hjM : j ∈ M := by
        have h1 := mul_mem (inv_mem (hOJM hcO)) hcM
        rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
      rw [hbqj]
      exact mul_mem (mem_sup_left hqQ) (mem_sup_right ⟨hj, hjM⟩)
    have hKQJM : K ≤ Q ⊔ (J ⊓ M) :=
      le_of_forall_involution le_rfl (sup_eq_left.mpr (map_subtype_le _)) hKres hKq' hnc
        (le_normalizer_sup hKQ (le_normalizer_inf' hKJ (hKMle.trans le_normalizer))) hinv
    have hJQJM : J ≤ Q ⊔ (J ⊓ M) := hJKQ.trans (sup_le hKQJM le_sup_left)
    have hdec : ∀ j ∈ J, ∃ b ∈ J ⊓ M, b⁻¹ * j ∈ Q := by
      intro j hj
      obtain ⟨q, hqQ, y, hy, hjqy⟩ :=
        exists_mul_of_mem_sup_normalizer (inf_le_left.trans hJQ) (hJQJM (inv_mem hj))
      refine ⟨y⁻¹, inv_mem hy, ?_⟩
      have hj' : j = (q * y)⁻¹ := by rw [← hjqy, inv_inv]
      rw [hj', show y⁻¹⁻¹ * (q * y)⁻¹ = q⁻¹ by group]
      exact inv_mem hqQ
    have hJM : J ≤ M :=
      calc J = J ⊓ M ⊔ oddCoreIn J :=
            (sup_oddCoreIn_eq_of_forall_coreActionKernel inf_le_left hJperf hdec).symm
        _ ≤ M := sup_le inf_le_right hOJM
    have hJMC : IsTwoComponentIn J (M ⊓ Ca) :=
      ⟨le_inf hJM hJC.1, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hJM hJC.1)
        inf_le_right hJC.2⟩
    have hKMC : IsTwoComponentIn K (M ⊓ Ca) :=
      ⟨le_inf hKMle haK, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKMle haK)
        inf_le_left hKM.2⟩
    by_contra hne
    exact hmove (GSThmB.B5a.le_coreActionKernel_of_ne hJMC.1 hKMC.1 hJMC.2 hKMC.2 hne)
  obtain ⟨J, hJ⟩ := pumpSet_nonempty hK haQ ha
  have hKCa : IsTwoComponentIn K Ca := by
    rw [← key J hJ]
    exact hJ.1.1
  have hcl : conjClosure K La ≤ K := by
    rw [conjClosure_eq_iSup]
    refine iSup₂_le fun l hl => ?_
    have hlK : l⁻¹ ∈ normalizer (K : Set G) :=
      inv_mem (FooteLit.twoLayerIn_le_normalizer hKCa.1 hKCa.2 hl)
    exact (mem_normalizer_iff_map_conj_eq.mp hlK).le
  exact hcl.trans le_sup_right

end CFSG.ComponentClassification.Sol76T13
