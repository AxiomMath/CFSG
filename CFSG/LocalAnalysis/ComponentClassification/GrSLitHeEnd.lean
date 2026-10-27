module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeInner
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeEnd

variable {G : Type*} [Group G]

theorem pow_four_or_pow_three_of_l34 {Q : Type} [Group Q]
    (hQ : IsL34Type Q) {y : Q} (hy : y ^ 12 = 1) : y ^ 4 = 1 ∨ y ^ 3 = 1 := by
  obtain ⟨θ⟩ := CatFactsSmall.nonempty_equiv_psl34_of_lieModel hQ
  have hcent := (PSL3Four.facts_of_equiv_S.{0, 0} θ).2.1
  have hno : ∀ t s : Q, orderOf t = 2 → orderOf s = 3 → s * t = t * s → False := by
    intro t s ht hs hst
    have hmem : s ∈ centralizer ({t} : Set Q) := mem_centralizer_singleton_iff.mpr hst
    have h3 := orderOf_dvd_natCard (⟨s, hmem⟩ : centralizer ({t} : Set Q))
    rw [Subgroup.orderOf_mk, hs, hcent t ht] at h3
    norm_num at h3
  have hd : orderOf y ∈ Nat.divisors 12 :=
    Nat.mem_divisors.mpr ⟨orderOf_dvd_of_pow_eq_one hy, by norm_num⟩
  have h12 : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [h12] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hcomm : ∀ a b : ℕ, y ^ a * y ^ b = y ^ b * y ^ a := fun a b => by
    rw [← pow_add, ← pow_add, add_comm]
  rcases hd with h | h | h | h | h | h
  · left; rw [← orderOf_dvd_iff_pow_eq_one, h]; norm_num
  · left; rw [← orderOf_dvd_iff_pow_eq_one, h]; norm_num
  · right; rw [← orderOf_dvd_iff_pow_eq_one, h]
  · left; rw [← orderOf_dvd_iff_pow_eq_one, h]
  · exact (hno (y ^ 3) (y ^ 2) (by rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h])
      (by rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]) (hcomm 2 3)).elim
  · exact (hno (y ^ 6) (y ^ 4) (by rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h])
      (by rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]) (hcomm 4 6)).elim

theorem normalizer_le_normalizer_centralizer (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (centralizer (K : Set G) : Set G) := by
  intro h hh
  have key : ∀ g ∈ normalizer (K : Set G), ∀ c ∈ centralizer (K : Set G),
      g * c * g⁻¹ ∈ centralizer (K : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff] at hc ⊢
    intro k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      rwa [inv_inv] at this
    have h1 := hc _ hk'
    calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * k := by group
  refine mem_normalizer_iff.mpr fun c => ⟨key h hh c, fun hc => ?_⟩
  have := key h⁻¹ (inv_mem hh) _ hc
  rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this

theorem conj_mem_center_iff {K : Subgroup G} {c : G} (hc : c ∈ normalizer (K : Set G)) (z : G) :
    z ∈ (center ↥K).map K.subtype ↔ c * z * c⁻¹ ∈ (center ↥K).map K.subtype := by
  constructor
  · intro hz
    exact Walter.conj_mem_map_of_characteristic hc hz
  · intro hz
    have h := Walter.conj_mem_map_of_characteristic (inv_mem hc) hz
    rwa [show c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z by group] at h

theorem two_le_pRank_of_pair [Finite G] {H : Subgroup G} {y₁ y₂ : G} (h₁ : y₁ ∈ H)
    (h₂ : y₂ ∈ H) (hy₁ : y₁ * y₁ = 1) (hy₂ : y₂ * y₂ = 1) (hy₁1 : y₁ ≠ 1) (hy₂1 : y₂ ≠ 1)
    (hne : y₁ ≠ y₂) (hc : y₁ * y₂ = y₂ * y₁) : 2 ≤ CFSG.pRank 2 ↥H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : ∀ y : G, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hyy hy1 =>
    orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  refine RankSmallSources.two_le_pRank_of_commuting (z := ⟨y₁, h₁⟩) (u := ⟨y₂, h₂⟩)
    (by rw [Subgroup.orderOf_mk]; exact hord y₁ hy₁ hy₁1)
    (by rw [Subgroup.orderOf_mk]; exact hord y₂ hy₂ hy₂1) (Subtype.ext hc) fun hmem => ?_
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : y₁ ^ k = y₂ := by simpa using congrArg Subtype.val hk
  rw [← zpow_mod_orderOf, hord y₁ hy₁ hy₁1, Nat.cast_ofNat] at hk'
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hk'
    exact hy₂1 hk'.symm
  · rw [h, zpow_one] at hk'
    exact hne hk'

end HeEnd

open HeEnd

@[expose] def HeldKNormalAt {X : Type} [Group X] [Finite X] (L : Subgroup X) : Prop :=
  ∀ u : X, HeldTwoA L u →
    ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).Normal ∧
    ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({u} : Set X) →
      (K₁.subgroupOf (centralizer ({u} : Set X))).Normal →
      Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u)) → K₁ = gsFixedLayer L u

theorem heldLemma36
    (hB : HeldTwoBCentralizerFact) (hLay : HeldTwoALayerFact) (hFour : HeldTwoAFourFact)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L)
    (hKN : HeldKNormalAt L) {v : X}
    (hvL : v ∈ L) (hv : orderOf v = 2) {K₁ : Subgroup X} (hK₁v : K₁ ≤ centralizer ({v} : Set X))
    (hK₁n : (K₁.subgroupOf (centralizer ({v} : Set X))).Normal)
    (hK₁ : ∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) : HeldTwoA L v := by
  refine ⟨hvL, hv, fun hv0 => ?_⟩
  obtain ⟨-, -, -, ⟨eL⟩, hrank⟩ := id hset
  obtain ⟨u, hu, ⟨φ⟩⟩ := id hK₁
  obtain ⟨hHp, x, hxH, hx12, w₁, hw₁H, w₂, hw₂H, hw₁A, hw₂A, hHN, hv₁, hv₂, hgen⟩ :=
    hB X L ⟨eL⟩ v hvL hv hv0
  obtain ⟨hKp, hKt⟩ := hLay X L ⟨eL⟩ u hu
  have hK₁p : Group.IsPerfect ↥K₁ := by
    have : Group.IsPerfect ↥(gsFixedLayer L u) := isPerfect_iff.mpr hKp
    exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hK₁t : IsL34Type (↥K₁ ⧸ center ↥K₁) :=
    LieType.CurtisTits.lieModel_of_mulEquiv (Sol78.centerQuotCongr φ).symm hKt
  have hHK : L ⊓ centralizer ({v} : Set X) ≤ normalizer (K₁ : Set X) :=
    inf_le_right.trans (le_normalizer_of_normal_subgroupOf (hK := hK₁n) hK₁v)
  have hx := L34Out.le_sup_centralizer_of_perfect hK₁p hK₁t hHp hHK hxH
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left K₁ (centralizer (K₁ : Set X))
    (centralizer_le_normalizer _)] at hx
  obtain ⟨k, hk, c, hc, hkc⟩ := hx
  have hcomm : Commute k c := mem_centralizer_iff.mp hc k hk
  have hpow : ∀ n : ℕ, x ^ n = k ^ n * c ^ n := fun n => by rw [← hkc, hcomm.mul_pow]
  have hZ : ∀ n : ℕ, ((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ center ↥K₁) ^ n = 1 ↔
      k ^ n ∈ centralizer (K₁ : Set X) := by
    intro n
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_center_iff, mem_centralizer_iff]
    constructor
    · intro h g hg
      have h1 := congrArg Subtype.val (h ⟨g, hg⟩)
      simpa using h1
    · intro h g
      exact Subtype.ext (by simpa using h g g.2)
  have hk12 : ((⟨k, hk⟩ : ↥K₁) : ↥K₁ ⧸ center ↥K₁) ^ 12 = 1 := by
    rw [hZ]
    have h1 : k ^ 12 = (c ^ 12)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hpow, hx12]
    rw [h1]
    exact inv_mem (pow_mem hc 12)
  have hxC : ∀ n : ℕ, k ^ n ∈ centralizer (K₁ : Set X) →
      x ^ n ∈ (L ⊓ centralizer ({v} : Set X)) ⊓ centralizer (K₁ : Set X) := fun n hn =>
    mem_inf.mpr ⟨pow_mem hxH n, by rw [hpow]; exact mul_mem hn (pow_mem hc n)⟩
  have hx43 : x ^ 4 ∈ (L ⊓ centralizer ({v} : Set X)) ⊓ centralizer (K₁ : Set X) ∨
      x ^ 3 ∈ (L ⊓ centralizer ({v} : Set X)) ⊓ centralizer (K₁ : Set X) :=
    (HeEnd.pow_four_or_pow_three_of_l34 hK₁t hk12).imp (fun h => hxC 4 ((hZ 4).mp h))
      (fun h => hxC 3 ((hZ 3).mp h))
  have hHN' : L ⊓ centralizer ({v} : Set X) ≤ normalizer (centralizer (K₁ : Set X) : Set X) :=
    hHK.trans (normalizer_le_normalizer_centralizer K₁)
  have hnorm : (((L ⊓ centralizer ({v} : Set X)) ⊓ centralizer (K₁ : Set X)).subgroupOf
      (L ⊓ centralizer ({v} : Set X))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨hnH, hnC⟩ := mem_inf.mp hn
    refine mem_inf.mpr ⟨mul_mem (mul_mem g.2 hnH) (inv_mem g.2), ?_⟩
    exact (mem_normalizer_iff.mp (hHN' g.2) n).mp hnC
  obtain ⟨hw₁C, hw₂C⟩ := hHN _ inf_le_left hnorm hx43
  have key : ∀ w : X, HeldTwoA L w → w ∈ L ⊓ centralizer ({v} : Set X) →
      w ∈ centralizer (K₁ : Set X) → v ∉ centralizer (gsFixedLayer L w : Set X) →
      K₁ ≤ centralizer (gsFixedLayer L w : Set X) := by
    intro w hwA hwH hwK hvw
    obtain ⟨hKwn, -⟩ := hKN w hwA
    obtain ⟨hKwp, hKwt⟩ := hLay X L ⟨eL⟩ w hwA
    have hN : centralizer ({w} : Set X) ≤ normalizer (gsFixedLayer L w : Set X) :=
      le_normalizer_of_normal_subgroupOf (hK := hKwn)
        ((gsFixedLayer_le_inf L w).trans inf_le_right)
    have hK₁w : K₁ ≤ centralizer ({w} : Set X) := fun k hk =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hwK k hk)
    have hvw' : v ∈ centralizer ({w} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (mem_inf.mp hwH).2).symm
    rcases HeInner.le_centralizer_or_mem_centralizer hKwp hKwt (isPerfect_iff.mp hK₁p) hK₁t
        (hK₁w.trans hN) (hN hvw') (fun k hk => (mem_centralizer_singleton_iff.mp (hK₁v hk)).symm)
      with h | h
    · exact h
    · exact absurd h hvw
  have hK₁L : K₁ ≤ centralizer (L : Set X) := by
    rw [← le_centralizer_iff, ← hgen]
    exact sup_le (le_centralizer_iff.mp (key w₁ hw₁A hw₁H (mem_inf.mp hw₁C).2 hv₁))
      (le_centralizer_iff.mp (key w₂ hw₂A hw₂H (mem_inf.mp hw₂C).2 hv₂))
  obtain ⟨y₁, hy₁, y₂, hy₂, h1, h2, h3, h4, h5, h6⟩ := hFour X L ⟨eL⟩ u hu
  have hmul : ∀ a b : ↥(gsFixedLayer L u),
      ((φ.symm a : ↥K₁) : X) * (φ.symm b : X) = ((φ.symm (a * b) : ↥K₁) : X) := fun a b => by
    rw [map_mul, coe_mul]
  have hsq : ∀ (y : X) (hy : y ∈ gsFixedLayer L u), y * y = 1 →
      ((φ.symm ⟨y, hy⟩ : ↥K₁) : X) * (φ.symm ⟨y, hy⟩ : X) = 1 := fun y hy hyy => by
    rw [hmul, show (⟨y, hy⟩ : ↥(gsFixedLayer L u)) * ⟨y, hy⟩ = 1 from Subtype.ext hyy, map_one,
      coe_one]
  have hne1 : ∀ (y : X) (hy : y ∈ gsFixedLayer L u), y ≠ 1 →
      ((φ.symm ⟨y, hy⟩ : ↥K₁) : X) ≠ 1 := fun y hy hy1 h => by
    have h' : φ.symm ⟨y, hy⟩ = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact hy1 (congrArg Subtype.val h')
  have hrank2 := HeEnd.two_le_pRank_of_pair (hK₁L (φ.symm ⟨y₁, hy₁⟩).2)
    (hK₁L (φ.symm ⟨y₂, hy₂⟩).2) (hsq y₁ hy₁ h1) (hsq y₂ hy₂ h2) (hne1 y₁ hy₁ h3)
    (hne1 y₂ hy₂ h4) (fun h => h5 (congrArg Subtype.val (φ.symm.injective (Subtype.ext h))))
    (by rw [hmul, hmul, show (⟨y₁, hy₁⟩ : ↥(gsFixedLayer L u)) * ⟨y₂, hy₂⟩ =
      ⟨y₂, hy₂⟩ * ⟨y₁, hy₁⟩ from Subtype.ext h6])
  omega

theorem heldCor37 (hClass : HeldTwoAClassFact)
    (hPair : HeldTwoAPairFact) (hGen : HeldTwoAGenerationFact) {X : Type} [Group X] [Finite X]
    {L : Subgroup X} (hset : HeldEndSetting X L) (hKN : HeldKNormalAt L)
    (h36 : ∀ v ∈ L, orderOf v = 2 → ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({v} : Set X) →
      (K₁.subgroupOf (centralizer ({v} : Set X))).Normal →
      (∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) → HeldTwoA L v)
    {u : X} (hu : HeldTwoA L u) : centralizer ({u} : Set X) ≤ normalizer (L : Set X) := by
  obtain ⟨-, -, -, ⟨eL⟩, -⟩ := id hset
  intro c hc
  obtain ⟨hKn, -⟩ := hKN u hu
  have hKC : gsFixedLayer L u ≤ centralizer ({u} : Set X) :=
    (gsFixedLayer_le_inf L u).trans inf_le_right
  have hcK : c ∈ normalizer (gsFixedLayer L u : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact mem_subgroupOf.mp (hKn.conj_mem ⟨x, hKC hx⟩ (mem_subgroupOf.mpr hx) ⟨c, hc⟩)
    · intro hx
      have hxC : x ∈ centralizer ({u} : Set X) := by
        have h3 := mul_mem (mul_mem (inv_mem hc) (hKC hx)) hc
        rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at h3
      have h1 := hKn.conj_mem ⟨c * x * c⁻¹, hKC hx⟩ (mem_subgroupOf.mpr hx) ⟨c, hc⟩⁻¹
      have h4 := mem_subgroupOf.mp h1
      simp only [coe_mul, coe_inv, inv_inv] at h4
      rwa [show c⁻¹ * (c * x * c⁻¹) * c = x by group] at h4
  have hcu : c * u * c⁻¹ = u := by
    rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
  obtain ⟨w, hwK, hwA, hwZ, huwZ⟩ := hPair X L ⟨eL⟩ u hu
  have hw'K : c * w * c⁻¹ ∈ gsFixedLayer L u := (mem_normalizer_iff.mp hcK w).mp hwK
  have hw'L : c * w * c⁻¹ ∈ L := (mem_inf.mp (gsFixedLayer_le_inf L u hw'K)).1
  have hw'o : orderOf (c * w * c⁻¹) = 2 := by
    rw [← (SemiconjBy.orderOf_eq c (show SemiconjBy c w (c * w * c⁻¹) by
      unfold SemiconjBy; group))]
    exact hwA.2.1
  have hw'Z : c * w * c⁻¹ ∉ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype :=
    fun h => hwZ ((conj_mem_center_iff hcK w).mpr h)
  have huw'Z : u * (c * w * c⁻¹) ∉
      (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype := by
    intro h
    apply huwZ
    rw [conj_mem_center_iff hcK]
    rwa [show c * (u * w) * c⁻¹ = (c * u * c⁻¹) * (c * w * c⁻¹) by group, hcu]
  obtain ⟨hKwn, -⟩ := hKN w hwA
  have hKwC : gsFixedLayer L w ≤ centralizer ({w} : Set X) :=
    (gsFixedLayer_le_inf L w).trans inf_le_right
  have hKcC : (gsFixedLayer L w).map (MulAut.conj c).toMonoidHom ≤
      centralizer ({c * w * c⁻¹} : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hKwC hy)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * w * c⁻¹) = c * (y * w) * c⁻¹ := by group
      _ = c * (w * y) * c⁻¹ := by rw [h1]
      _ = c * w * c⁻¹ * (c * y * c⁻¹) := by group
  have hKcn : (((gsFixedLayer L w).map (MulAut.conj c).toMonoidHom).subgroupOf
      (centralizer ({c * w * c⁻¹} : Set X))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hye⟩ := hn
    have hgC : c⁻¹ * (g : X) * c ∈ centralizer ({w} : Set X) := by
      have hg := mem_centralizer_singleton_iff.mp g.2
      rw [mem_centralizer_singleton_iff]
      calc c⁻¹ * (g : X) * c * w = c⁻¹ * ((g : X) * (c * w * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * w * c⁻¹) * g) * c := by rw [hg]
        _ = w * (c⁻¹ * g * c) := by group
    have h1 := hKwn.conj_mem ⟨y, hKwC hy⟩ (mem_subgroupOf.mpr hy) ⟨_, hgC⟩
    refine ⟨_, mem_subgroupOf.mp h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul, coe_inv] at hye ⊢
    rw [← hye]
    group
  have hKciso : Nonempty (↥((gsFixedLayer L w).map (MulAut.conj c).toMonoidHom) ≃*
      ↥(gsFixedLayer L w)) :=
    ⟨((gsFixedLayer L w).equivMapOfInjective _ (MulAut.conj c).injective).symm⟩
  have hw'A : HeldTwoA L (c * w * c⁻¹) :=
    h36 _ hw'L hw'o _ hKcC hKcn ⟨w, hwA, hKciso⟩
  have hiso : Nonempty (↥((gsFixedLayer L w).map (MulAut.conj c).toMonoidHom) ≃*
      ↥(gsFixedLayer L (c * w * c⁻¹))) := by
    obtain ⟨l, hlL, hl⟩ := hClass X L ⟨eL⟩ w (c * w * c⁻¹) hwA hw'A
    have hLl : L.map (MulAut.conj l).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer hlL)
    have hmap := GSLit.map_gsFixedLayer (MulAut.conj l) L w
    rw [hLl, MulAut.conj_apply, ← hl] at hmap
    obtain ⟨e1⟩ := hKciso
    exact ⟨e1.trans (((gsFixedLayer L w).equivMapOfInjective _
      (MulAut.conj l).injective).trans (MulEquiv.subgroupCongr hmap))⟩
  have hKceq := (hKN _ hw'A).2 _ hKcC hKcn hiso
  have hgen1 := hGen X L ⟨eL⟩ u w hu hwA hwK hwZ huwZ
  have hgen2 := hGen X L ⟨eL⟩ u _ hu hw'A hw'K hw'Z huw'Z
  have hKmap : (gsFixedLayer L u).map (MulAut.conj c).toMonoidHom = gsFixedLayer L u :=
    mem_normalizer_iff_map_conj_eq.mp hcK
  rw [mem_normalizer_iff_map_conj_eq]
  calc L.map (MulAut.conj c).toMonoidHom =
        (gsFixedLayer L u ⊔ gsFixedLayer L w).map (MulAut.conj c).toMonoidHom := by
        rw [hgen1]
    _ = (gsFixedLayer L u).map (MulAut.conj c).toMonoidHom ⊔
        (gsFixedLayer L w).map (MulAut.conj c).toMonoidHom := map_sup _ _ _
    _ = gsFixedLayer L u ⊔ gsFixedLayer L (c * w * c⁻¹) := by
        rw [hKmap, hKceq]
    _ = L := hgen2

theorem heldEndStep_of_steps (hKN : HeldKNormalStep)
    (hEnd : HeldZStarEndStep) (hB : HeldTwoBCentralizerFact) (hLay : HeldTwoALayerFact)
    (hFour : HeldTwoAFourFact) (hClass : HeldTwoAClassFact) (hPair : HeldTwoAPairFact)
    (hGen : HeldTwoAGenerationFact) : HeldEndStep := by
  intro X _ _ L hset hW hstd he hrank
  have hS : HeldEndSetting X L := ⟨hset, hW, hstd, he, hrank⟩
  have h36 : ∀ v ∈ L, orderOf v = 2 → ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({v} : Set X) →
      (K₁.subgroupOf (centralizer ({v} : Set X))).Normal →
      (∃ u : X, HeldTwoA L u ∧ Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u))) → HeldTwoA L v :=
    fun _ hvL hv _ h1 h2 h3 => heldLemma36 hB hLay hFour hS (hKN X L hS) hvL hv h1 h2 h3
  exact hEnd X L hS (fun u hu => hKN X L hS u hu) h36
    (fun _ hu => heldCor37 hClass hPair hGen hS (hKN X L hS) h36 hu)

end CFSG.ComponentClassification.GrSLit
