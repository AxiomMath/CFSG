module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUSylow
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUStep
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGoldschmidt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts
open scoped commutatorElement

theorem eq_of_card_eq_two {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : Nat.card H = 2) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  have hxo : orderOf x = 2 := by
    have h1 : orderOf x ∣ 2 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : H)
      rwa [Subgroup.orderOf_mk, hH] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzx : zpowers x = H :=
    eq_of_le_of_card_ge (zpowers_le.mpr hx) (by rw [hH, Nat.card_zpowers, hxo])
  rw [← hzx] at hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hxo] at hy1 ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [Nat.cast_ofNat, h, zpow_zero] at hy1
    exact absurd rfl hy1
  · rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

variable {X : Type} [Group X] [Finite X]

theorem mem_twoResidualOf_top [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (a : X) :
    a ∈ GorensteinWalter.twoResidualOf (⊤ : Subgroup X) := by
  have hcomm : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have h1 : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
        Subgroup.commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact h
  have hperf : Group.IsPerfect ↥(⊤ : Subgroup X) := Subgroup.isPerfect_iff.mpr hcomm
  exact GorensteinWalter.perfect_subgroup_le_twoResidualOf ⊤ ⊤ le_rfl hperf (mem_top a)

theorem card_quotient_R :
    Nat.card (↥R ⧸ S.subgroupOf R) = 12 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf R)
  rw [card_R, Nat.card_congr (subgroupOfEquivOfLe S_le_R).toEquiv, card_S] at h
  omega

theorem exists_index_two
    {K SX : Subgroup X} (hKl : IsL34Type (K ⧸ Open.fusionZStar K))
    (hSN : SX ≤ normalizer (K : Set X)) (hS2 : IsPGroup 2 SX) {v y : X} (hvS : v ∈ SX)
    (hyS : y ∈ SX) (hv : HarrisLit.EndB.IsL34Field K v) (hy : IsL34Unitary K y) :
    ∃ M : Subgroup X, M ≤ SX ∧ M.relIndex SX = 2 ∧
      ∀ w ∈ M, w * w = 1 → Nat.card (commZStar K w) ≠ 168 * Nat.card (zStarIn K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hKl
  obtain ⟨ψ, hψR, hψ⟩ := GrS4.exists_realization_hom hSN hqS hqsurj hqker
  have : (S.subgroupOf R).Normal := S_normal
  set θ : ↥SX →* ↥R ⧸ S.subgroupOf R :=
    (QuotientGroup.mk' (S.subgroupOf R)).comp (ψ.codRestrict R hψR) with hθ
  have hθ1 : ∀ x, θ x = 1 ↔ ψ x ∈ S := fun x => by
    rw [hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf]
    rfl
  have hθeq : ∀ x x', θ x = θ x' ↔ (ψ x)⁻¹ * ψ x' ∈ S := fun x x' => by
    rw [hθ, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    rfl
  have hreal : ∀ (x : ↥SX) e, q (betaHat K (hSN x.2) e) = (ψ x)⁻¹ * q e * ((ψ x)⁻¹)⁻¹ :=
    fun x e => by rw [inv_inv]; exact hψ x e
  have hfield : ∀ x : ↥SX, (x : X) * x = 1 →
      Nat.card (commZStar K x) = 168 * Nat.card (zStarIn K) →
      ∃ c ∈ R, (ψ x)⁻¹ = c * r₂ * c⁻¹ := by
    intro x hx2 hcnt
    have h1 := card_centralizer_of_count (hSN x.2) hqS hqsurj hqker (hreal x) (n := 168)
      (by rw [card_subtype_eq_card_commZStar]; exact hcnt)
    exact exists_conj_r₂_of_card (R.inv_mem (hψR x))
      (realization_mul_self (hSN x.2) hx2 hqsurj (R.inv_mem (hψR x)) (hreal x)) h1
  set v' : ↥SX := ⟨v, hvS⟩ with hv'
  set y' : ↥SX := ⟨y, hyS⟩ with hy'
  obtain ⟨cv, hcvR, hcv⟩ :=
    hfield v' hv.2.1 (by rw [← card_subtype_eq_card_commZStar]; exact hv.2.2.2)
  have hy72 := card_centralizer_of_count (hSN hyS) hqS hqsurj hqker (hreal y') hy.2.2.2
  have hyρ2 := realization_mul_self (hSN hyS) hy.2.1 hqsurj (R.inv_mem (hψR y')) (hreal y')
  obtain ⟨cy, hcyR, hcy⟩ :=
    eq_conj_of_isConj (exists_conj_r₄_of_card (R.inv_mem (hψR y')) hyρ2 hy72)
  have hcy' : (ψ y')⁻¹ = cy * r₄ * cy⁻¹ := hcy
  have hexcl : ∀ x : ↥SX, (∃ c ∈ R, (ψ x)⁻¹ = c * r₂ * c⁻¹) → θ x ≠ 1 ∧ θ x ≠ θ y' := by
    rintro x ⟨c, hcR, hc⟩
    constructor
    · intro h1
      have h2 := S.inv_mem ((hθ1 x).mp h1)
      rw [hc] at h2
      exact not_mem_S_r₂ (conj_mem_S' hcR h2)
    · intro h
      have h1 := (hθeq x y').mp h
      have h2 : (ψ y')⁻¹ * r₄ ∈ S := by rw [hcy']; exact conj_r₄_mul_r₄_mem_S hcyR
      have h3 : (ψ x)⁻¹ * r₄ ∈ S := by
        have := S.mul_mem h1 h2
        rwa [show (ψ x)⁻¹ * ψ y' * ((ψ y')⁻¹ * r₄) = (ψ x)⁻¹ * r₄ by group] at this
      rw [hc] at h3
      exact conj_r₂_mul_r₄_not_mem_S hcR h3
  obtain ⟨he₁, he₁₂⟩ := hexcl v' ⟨cv, hcvR, hcv⟩
  have he₂ : θ y' ≠ 1 := by
    intro h1
    have h2 := S.inv_mem ((hθ1 y').mp h1)
    rw [hcy'] at h2
    exact not_mem_S_r₄ (conj_mem_S' hcyR h2)
  have hy'2 : y' * y' = 1 := Subtype.ext hy.2.1
  have he₂2 : θ y' * θ y' = 1 := by rw [← map_mul, hy'2, map_one]
  have hΨ2 : IsPGroup 2 θ.range := hS2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hΨ2
  have hdvd : 2 ^ n ∣ 12 := hn ▸ card_quotient_R ▸ Subgroup.card_subgroup_dvd_card θ.range
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  have hv'R : θ v' ∈ θ.range := ⟨v', rfl⟩
  have hy'R : θ y' ∈ θ.range := ⟨y', rfl⟩
  have hcard : Nat.card θ.range = 4 := by
    interval_cases n
    · exfalso
      have h1 := eq_bot_of_card_eq θ.range (by rw [hn, pow_zero])
      rw [h1, mem_bot] at hv'R
      exact he₁ hv'R
    · exact absurd (eq_of_card_eq_two (by rw [hn, pow_one]) hv'R hy'R he₁ he₂) he₁₂
    · rw [hn]
      norm_num
  set M₀ : Subgroup ↥SX := (zpowers (θ y')).comap θ with hM₀
  have hidx : M₀.index = 2 := by
    rw [hM₀, index_comap]
    have h1 := relIndex_mul_card (zpowers (θ y')) θ.range
    rw [inf_eq_left.mpr (zpowers_le.mpr hy'R), hcard, Nat.card_zpowers] at h1
    have ho : orderOf (θ y') = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact he₂2) he₂
    rw [ho] at h1
    omega
  refine ⟨M₀.map SX.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [relIndex, ← comap_subtype, comap_map_eq_self_of_injective SX.subtype_injective]
    exact hidx
  · rintro _ ⟨w, hwM, rfl⟩ hw2 hcnt
    have hw2' : (w : X) * w = 1 := hw2
    obtain ⟨hw1, hwy⟩ := hexcl w (hfield w hw2' hcnt)
    rcases eq_one_or_eq_of_mem_zpowers he₂2 (mem_comap.mp hwM) with h | h
    · exact hw1 h
    · exact hwy h

theorem not_extremal (h13 : Sol76T13.SolomonThm13Simple)
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hbK : b ∈ K) {v : X} (hv : HarrisLit.EndB.IsL34Field K v) (hvb : v * b = b * v)
    {SX : Subgroup X} (hSX : SX ≤ centralizer ({b} : Set X)) {r : X}
    (hrv : r * v = v * r) (hr8 : r ^ 8 = b) {M : Subgroup X} (hMS : M ≤ SX)
    (hMfield : ∀ w ∈ M, w * w = 1 → Nat.card (commZStar K w) ≠ 168 * Nat.card (zStarIn K))
    {g : X} (hgM : g⁻¹ * v * g ∈ M) (hext : IsExtremalIn SX (g⁻¹ * v * g)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2
  have hNK := centralizer_le_normalizer h13 hnab hKP hb hK hKmax hKl
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  set w := g⁻¹ * v * g with hwdef
  set r' := g⁻¹ * r * g with hr'def
  have hr'w : r' * w = w * r' := by
    calc r' * w = g⁻¹ * (r * v) * g := by rw [hr'def, hwdef]; group
      _ = g⁻¹ * (v * r) * g := by rw [hrv]
      _ = w * r' := by rw [hr'def, hwdef]; group
  have hpow : ∀ n : ℕ, (g⁻¹ * r * g) ^ n = g⁻¹ * r ^ n * g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  have hr'16 : r' ^ (2 ^ 4) = 1 := by
    rw [hr'def, hpow, show 2 ^ 4 = 8 * 2 from rfl, pow_mul, hr8, pow_two, hbb]
    group
  set C := centralizer ({w} : Set X) with hC
  have hr'C : r' ∈ C := mem_centralizer_singleton_iff.mpr hr'w
  have hZ2 : IsPGroup 2 ↥((zpowers r').subgroupOf C) := by
    have h1 : IsPGroup 2 (zpowers r') := by
      have hdvd : orderOf r' ∣ 2 ^ 4 := orderOf_dvd_of_pow_eq_one hr'16
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
    exact h1.comap_subtype (K := C)
  obtain ⟨P', hP'⟩ := hZ2.exists_le_sylow
  obtain ⟨-, P, hP⟩ := hext
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq ↥C P P'
  have hmem : (⟨r', hr'C⟩ : ↥C) ∈ ((h • P : Sylow 2 ↥C) : Subgroup ↥C) :=
    hP' (mem_subgroupOf.mpr (mem_zpowers r'))
  rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨s, hsP, hs⟩ := hmem
  rw [hP, mem_subgroupOf] at hsP
  have hsr : (s : X) = (h : X)⁻¹ * r' * h := by
    have h1 := congrArg Subtype.val hs
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [← h1]
    group
  set g' := g * (h : X) with hg'
  have hg'r : g'⁻¹ * r * g' ∈ SX := by
    rw [hg', show (g * (h : X))⁻¹ * r * (g * h) = (h : X)⁻¹ * r' * h by rw [hr'def]; group,
      ← hsr]
    exact (mem_inf.mp hsP).1
  have hg'v : g'⁻¹ * v * g' = w := by
    have hhw : (h : X) * w = w * h := (mem_centralizer_singleton_iff.mp h.2)
    rw [hg']
    calc (g * (h : X))⁻¹ * v * (g * h) = (h : X)⁻¹ * w * h := by rw [hwdef]; group
      _ = (h : X)⁻¹ * (w * h) := by group
      _ = (h : X)⁻¹ * (h * w) := by rw [hhw]
      _ = w := by group
  have hc : g'⁻¹ * b * g' ∈ coreActionKernel K :=
    mem_coreActionKernel_of_pow_eight hKperf hKl hbb hr8 (hNK (hSX hg'r))
  have hcb : g'⁻¹ * b * g' * b = b * (g'⁻¹ * b * g') := by
    have hpow' : (g'⁻¹ * r * g') ^ 8 = g'⁻¹ * b * g' := by
      have : ∀ n : ℕ, (g'⁻¹ * r * g') ^ n = g'⁻¹ * r ^ n * g' := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, ih, pow_succ]; group
      rw [this, hr8]
    have h1 : g'⁻¹ * b * g' ∈ SX := hpow' ▸ pow_mem hg'r 8
    exact mem_centralizer_singleton_iff.mp (hSX h1)
  have hwK : g'⁻¹ * v * g' ∈ normalizer (K : Set X) := by
    rw [hg'v]
    exact hNK (hSX (hMS hgM))
  have hcnt := card_commZStar_conj h13 hnab hKP hb hK hKmax hKl hbK hv hvb hc hcb hwK
  rw [hg'v] at hcnt
  have hw2 : w * w = 1 := by
    rw [hwdef]
    calc g⁻¹ * v * g * (g⁻¹ * v * g) = g⁻¹ * (v * v) * g := by group
      _ = 1 := by rw [hv.2.1]; group
  exact hMfield w hgM hw2 hcnt

theorem false_of_isSolomonMaximal
    (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    {b y v : X} {K : Subgroup X} (hT : GSUnbalancingTriple b y K) (hbK : b ∈ K)
    (hKl : IsL34Type (K ⧸ Open.fusionZStar K))
    (h16 : Nat.card (zStarIn K) = 16 * Nat.card (oddIn K)) (hy : IsL34Unitary K y)
    (hvb : v * b = b * v) (hvy : v * y = y * v) (hv : HarrisLit.EndB.IsL34Field K v)
    (hKmax : IsSolomonMaximal K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb, -, hby, hKb, hKc, -, -⟩ := hT
  have hK : IsTwoComponentIn K (centralizer ({b} : Set X)) := ⟨hKb, hKc⟩
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2
  have hNK := centralizer_le_normalizer h13 hnab hKP hb hK hKmax hKl
  obtain ⟨W, hW2, hWC, hvW, hyW, r, hrW, hrv, hr8⟩ :=
    exists_order_sixteen hKperf hKl h16 hb hbK hKb hv hy hvy hvb hby.symm
  obtain ⟨Q, hQ⟩ := (hW2.comap_subtype (K := centralizer ({b} : Set X))).exists_le_sylow
  set SX : Subgroup X := (Q : Subgroup ↥(centralizer ({b} : Set X))).map
    (centralizer ({b} : Set X)).subtype with hSXdef
  have hSXC : SX ≤ centralizer ({b} : Set X) := map_subtype_le _
  have hSX : IsSylowTwoIn SX (centralizer ({b} : Set X)) := by
    refine ⟨hSXC, Q, ?_⟩
    rw [hSXdef, ← comap_subtype, comap_map_eq_self_of_injective (Subtype.val_injective)]
  have hWS : W ≤ SX := fun x hx => ⟨⟨x, hWC hx⟩, hQ (mem_comap.mpr hx), rfl⟩
  have hvS : v ∈ SX := hWS hvW
  have hyS : y ∈ SX := hWS hyW
  have hrS : r ∈ SX := hWS hrW
  have hS2 : IsPGroup 2 SX := isPGroup_of_isSylowTwoIn hSX
  obtain ⟨T, hT⟩ := exists_sylow_eq h13 hnab hKP hb hK hKmax hKl hbK h16 hv hSX hvS hrS hr8
  obtain ⟨M, hMS, hMidx, hMfield⟩ :=
    exists_index_two hKl (hSXC.trans hNK) hS2 hvS hyS hv hy
  have hvT : v ∈ (T : Subgroup X) := hT ▸ hvS
  have hv2 : orderOf v = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact hv.2.1) fun h1 => hv.2.2.1 ?_
    rw [h1]
    exact one_mem _
  rcases goldschmidtTransferInput_holds X T v hvT hv2 with h | h
  · obtain ⟨g, hgM, hext⟩ := h M (hT ▸ hMS) (hT ▸ hMidx)
    rw [hT] at hext
    exact not_extremal h13 hnab hKP hb hK hKmax hKl hbK hv hvb hSXC hrv hr8 hMS hMfield hgM hext
  · exact h (mem_twoResidualOf_top hnab v)

end CFSG.ComponentClassification.TBLit.L34FU

namespace CFSG.ComponentClassification.TBLit

open CFSG.ComponentClassification.Sol76

theorem l34FieldUnitaryExclusion_of_maximal
    (h13 : Sol76T13.SolomonThm13Simple)
    (hM : L34FieldUnitaryMaximalStep) :
    L34FieldUnitaryExclusion := by
  intro X _ _ _ hnab hKP hz hU b y v K hT hbK hKl h16 hy hvb hvy hv
  exact L34FU.false_of_isSolomonMaximal h13 hnab hKP hT hbK hKl h16 hy hvb hvy hv
    (hM X hnab hKP hz hU b y v K hT hbK hKl h16 hy hvb hvy hv)

end CFSG.ComponentClassification.TBLit
