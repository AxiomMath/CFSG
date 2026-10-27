module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props313
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props33C
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma316
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]
variable {𝒜 : Thm13Ambient}

theorem le_normalizer_of_coprime (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K : Subgroup G}
    (hK : K ∈ kStarComponents N) {O : Subgroup G} (hO : Nat.Coprime 2 (Nat.card O))
    (hKO : K ≤ normalizer (O : Set G)) : O ≤ normalizer (solomonKStarOf N : Set G) := by
  have hCb := (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N hN).2
  obtain ⟨E, hEK, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) K
  have h2 := two_le_pRank_of_mem_solomonKStar hK.2
  have hlarge : 2 ^ (1 + 1) ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) h2
  have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 1
    Nat.prime_two E O hE hlarge (hEK.trans hKO) hO
  rw [← hgen]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSE, hScard⟩ := hS
  have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hScard]; norm_num)
  obtain ⟨⟨v, hvS⟩, hv1⟩ := exists_ne (1 : S)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hv2 : orderOf v = 2 := orderOf_eq_prime (hE.2 v (hSE hvS)) hv1'
  exact inf_le_right.trans ((centralizer_le (Set.singleton_subset_iff.mpr hvS)).trans
    (hCb K hK v (hEK (hSE hvS)) hv2))

theorem le_of_mem_coreActionKernel {J C M : Subgroup G} (hJ : IsTwoComponentIn J C) {b : G}
    (hb : orderOf b = 2) (hbJ : b ∈ coreActionKernel J) (hCb : centralizer ({b} : Set G) ≤ M)
    (hOM : oddCoreIn J ≤ M) : J ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbb : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hOodd : Odd (Nat.card (oddCoreIn J)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn J)
  have hJO : J ≤ normalizer (oddCoreIn J : Set G) := le_normalizer_oddCoreIn J
  have hbO : b ∈ normalizer (oddCoreIn J : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn hbJ.1)
  have h2 : ∀ y ∈ J, ∀ k : ℕ, y ^ (2 ^ k) = 1 → y ∈ M := by
    intro y hy k hk
    have htb : y * b * y⁻¹ * b ∈ oddCoreIn J := by
      have h1 := hbJ.2 y⁻¹ (inv_mem hy)
      rwa [inv_inv, hbinv] at h1
    obtain ⟨c, hc, hcomm⟩ := exists_conj_commute hOodd hbb hbO (hJO hy) htb hk
    have hcM : c ∈ M := hOM hc
    have h1 : c⁻¹ * y * c ∈ centralizer ({b} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c⁻¹ * y * c * b = c⁻¹ * (y * (c * b * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * b * c⁻¹ * y) * c := by rw [hcomm]
        _ = b * (c⁻¹ * y * c) := by group
    have h3 : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [h3]
    exact mul_mem (mul_mem hcM (hCb h1)) (inv_mem hcM)
  have hres : CatalogueBPrimeJoin.primeResidual 2 ↥J = ⊤ :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJ.1).mp hJ.2).2.1
  have hle : CatalogueBPrimeJoin.primeResidual 2 ↥J ≤ M.subgroupOf J := by
    refine sSup_le fun P hP x hx => ?_
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    rw [mem_subgroupOf]
    refine h2 x x.2 k ?_
    have h1 := congrArg (fun z : P => ((z : ↥J) : G)) hk
    simpa using h1
  rw [hres] at hle
  intro j hj
  have h1 := hle (mem_top (⟨j, hj⟩ : ↥J))
  rwa [mem_subgroupOf] at h1

omit [Finite G] in
theorem isPGroup_zpowers_of_pow {y : G} {k : ℕ} (hy : y ^ (2 ^ k) = 1) :
    IsPGroup 2 (zpowers y) := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy)
  exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])

theorem le_solomonKStarOf_centralizer {K Y : Subgroup G} (hKY : IsTwoComponentIn K Y)
    (hKs : K ∈ solomonKStar G) {a : G} (ha : IsPGroup 2 (zpowers a)) (ha1 : a ≠ 1)
    (haK : K ≤ centralizer ({a} : Set G)) : K ≤ solomonKStarOf (centralizer ({a} : Set G)) := by
  have hka : ∀ k ∈ K, k * a = a * k := fun k hk => mem_centralizer_singleton_iff.mp (haK hk)
  have hUne : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hUQ : zpowers a ≤ coreActionKernel K := by
    rw [zpowers_le]
    exact Sol78.mem_coreActionKernel_of_commute hka
  have h := lemma212Input G K (zpowers a) hKs hUne ha hUQ
  have hCU : centralizer ((zpowers a : Subgroup G) : Set G) = centralizer ({a} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rwa [hCU, inf_eq_left.mpr haK, twoLayerIn_eq_self_of_isTwoComponentIn hKY] at h

omit [Finite G] in
theorem isPGroup_zpowers_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) :
    IsPGroup 2 (zpowers a) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) : a ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at ha
  norm_num at ha

omit [Finite G] in
theorem lemma33CentralInputFor_of_lemma33InputFor (h33 : Lemma33InputFor 𝒜) :
    Lemma33CentralInputFor 𝒜 := by
  intro G _ _ hG N hN K hK a haN ha haK
  have hka : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (mem_centralizer_singleton_iff.mp (haK hk)).symm
  have h3 := h33 G hG N hN K hK a haN ha fun k hk => by
    have h1 : a⁻¹ * k⁻¹ * a * k = 1 := by
      rw [show a⁻¹ * k⁻¹ * a * k = a⁻¹ * k⁻¹ * (a * k) by group, hka k hk]
      group
    rw [h1]
    exact one_mem _
  rwa [inf_eq_left.mpr haK, twoLayerIn_eq_self_of_isTwoComponentIn hK.1] at h3

theorem twoLayerIn_centralizer_le_normalizer (h33 : Lemma33CentralInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜)
    (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {a : G} (ha : orderOf a = 2)
    (haK : K ≤ centralizer ({a} : Set G)) :
    twoLayerIn (centralizer ({a} : Set G)) ≤ normalizer (solomonKStarOf N : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := solomonKStarOf N with hD
  set C := centralizer ({a} : Set G) with hC
  have hCb := (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N hN).2
  have hKD : K ≤ D := le_iSup₂_of_le K hK le_rfl
  have hDM : D ≤ normalizer (D : Set G) := le_normalizer
  have hka : ∀ k ∈ K, a * k = k * a := fun k hk =>
    (mem_centralizer_singleton_iff.mp (haK hk)).symm
  have hKL : K ≤ twoLayerIn C :=
    (le_solomonKStarOf_centralizer hK.1 hK.2 (isPGroup_zpowers_of_orderOf_eq_two ha)
      (ne_one_of_orderOf_eq_two ha) haK).trans (solomonKStarOf_le_twoLayerIn C)
  obtain ⟨b, hbK, hb2⟩ := exists_orderOf_eq_two_of_mem_solomonKStar hK.2
  have haN : a ∈ normalizer (D : Set G) :=
    hCb K hK b hbK hb2 (mem_centralizer_singleton_iff.mpr (hka b hbK))
  have h3 := h33 G hG N hN K hK a haN ha haK
  have hOL : oddCoreIn (twoLayerIn C) ≤ normalizer (D : Set G) :=
    le_normalizer_of_coprime h32 h315a h315c hbal hprod hG hN hK (coprime_card_oddCoreIn _)
      (hKL.trans (le_normalizer_oddCoreIn _))
  rw [twoLayerIn, map_le_iff_le_comap]
  refine sSup_le fun P hP => ?_
  rw [← map_le_iff_le_comap]
  have hJ : IsTwoComponentIn (P.map C.subtype) C := ⟨map_subtype_le _, by
    rw [← comap_subtype, comap_map_eq_self_of_injective C.subtype_injective]; exact hP⟩
  by_cases hmove : K ≤ coreActionKernel (P.map C.subtype)
  · refine le_of_mem_coreActionKernel hJ hb2 (hmove hbK) (hCb K hK b hbK hb2) ?_
    refine le_normalizer_of_coprime h32 h315a h315c hbal hprod hG hN hK
      (coprime_card_oddCoreIn _) fun k hk => ?_
    exact mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hmove hk).1)
  · exact (le_conjClosure_of_not_le_coreActionKernel hJ hKL hmove).trans
      (h3.trans (sup_le hOL (hKD.trans hDM)))

theorem exists_orderOf_eq_two_mem_zpowers {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1)
    (ht1 : t ≠ 1) : ∃ a ∈ zpowers t, orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htk)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact ht1 hm
  have hdvd : 2 ∣ Nat.card (zpowers t) := by
    rw [Nat.card_zpowers, hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := zpowers t) 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem twoLayerIn_centralizer_le_normalizer_of_pow (h33 : Lemma33CentralInputFor 𝒜)
    (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜) (h315c : Lemma315cInputFor 𝒜)
    (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K : Subgroup G} (hK : K ∈ kStarComponents N) {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1)
    (ht1 : t ≠ 1) (htK : K ≤ centralizer ({t} : Set G)) :
    twoLayerIn (centralizer ({t} : Set G)) ≤ normalizer (solomonKStarOf N : Set G) := by
  obtain ⟨a, haT, ha2⟩ := exists_orderOf_eq_two_mem_zpowers htk ht1
  have hCt : centralizer ({t} : Set G) ≤ centralizer ({a} : Set G) := by
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp haT
    rw [mem_centralizer_singleton_iff] at hx ⊢
    exact (Commute.zpow_right hx n).eq
  have h1 := twoLayerIn_centralizer_le_normalizer h33 h32 h315a h315c hbal hprod hG hN hK ha2
    (htK.trans hCt)
  have htC : t ∈ centralizer ({a} : Set G) := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp haT
    rw [mem_centralizer_singleton_iff]
    exact (Commute.zpow_right (Commute.refl t) n).eq
  have hT2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_pow htk
  have h2 := GrSLit.pLayer_inf_centralizer_le (Y := centralizer ({a} : Set G)) (A := zpowers t)
    (zpowers_le.mpr htC) hT2
  have hCz : centralizer ((zpowers t : Subgroup G) : Set G) = centralizer ({t} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hCz, inf_eq_right.mpr hCt] at h2
  exact h2.trans h1

theorem kStarComponents_centralizer (h32 : Lemma32InputFor 𝒜) (h315a : Lemma315aInputFor 𝒜)
    (h315c : Lemma315cInputFor 𝒜) (hbal : Lemma316BalancedInputFor 𝒜)
    (hprod : Lemma316ProductInputFor 𝒜) (hG : 𝒜 G) {N : Subgroup G} (hN : IsSolomonChoice N)
    {K : Subgroup G}
    (hK : K ∈ kStarComponents N) {b : G} (hbK : b ∈ K) (hb2 : orderOf b = 2) :
    kStarComponents (centralizer ({b} : Set G)) =
      {J | J ∈ kStarComponents N ∧ J ≤ centralizer ({b} : Set G)} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({b} : Set G) with hC
  set D := solomonKStarOf N with hD
  have hCD : C ≤ normalizer (D : Set G) :=
    (lemma316InputFor_of_inputs h32 h315a h315c hbal hprod G hG N hN).2 K hK b hbK hb2
  ext J
  constructor
  · intro hJ
    have hLH := twoLayerIn_centralizer_le_twoLayerIn_normalizer h32 h315a h315c hbal hG hN hK
      hbK hb2
    exact ⟨hprod G hG N hN K hK b hbK hb2 J hJ.1 hJ.2
      ((le_twoLayerIn_of_isTwoComponentIn hJ.1).trans hLH), hJ.1.1⟩
  · rintro ⟨hJ, hJC⟩
    refine ⟨?_, hJ.2⟩
    have hJD : J ≤ D := le_iSup₂_of_le J hJ le_rfl
    have hJDc : IsTwoComponentIn J D := isTwoComponentIn_of_le hJ.1 hJD (solomonKStarOf_le N)
    have hJY : IsTwoComponentIn J (D ⊓ C) :=
      isTwoComponentIn_of_le hJDc (le_inf hJD hJC) inf_le_left
    have hYn : ((D ⊓ C).subgroupOf C).IsSubnormal :=
      Normal.isSubnormal ((normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun c hc =>
        mem_normalizer_inf (hCD hc) (le_normalizer hc))
    exact ⟨hJC, GrSLit.isPComponent_subgroupOf_of_isSubnormal hJY.1 inf_le_right hYn hJY.2⟩

end CFSG.ComponentClassification.Sol76
