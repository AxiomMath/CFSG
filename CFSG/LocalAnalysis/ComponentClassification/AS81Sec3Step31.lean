module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Lemma815

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Blueprint

namespace Sec3

variable {G : Type} [Group G]

theorem map_center_eq_centerIn (H : Subgroup G) : (center H).map H.subtype = centerIn H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, mem_centralizer_iff.mpr fun w hw =>
      congrArg Subtype.val ((mem_center_iff.mp hy) ⟨w, hw⟩)⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun w =>
      Subtype.ext (mem_centralizer_iff.mp hxc w w.2), rfl⟩

theorem card_centerIn (H : Subgroup G) : Nat.card (centerIn H) = Nat.card (center H) := by
  rw [← map_center_eq_centerIn, card_map_of_injective H.subtype_injective]

theorem centralizer_zpowers (x : G) :
    centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem commutator_eq_top_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (h : commutator H = ⊤) : commutator K = ⊤ := by
  have h1 : (commutator H).map e.toMonoidHom = commutator K := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ e.surjective]
  rw [← h1, h, map_top_of_surjective _ e.surjective]

theorem card_center_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (center H) = Nat.card (center K) :=
  Nat.card_congr ((MulEquiv.subgroupMap e (center _)).toEquiv.trans
    (MulEquiv.subgroupCongr (Subgroup.map_center_eq e)).toEquiv)

theorem card_centerIn_of_extraspecial {Q : Subgroup G} (hext : CFSG.IsExtraspecialPGroup 2 Q) :
    Nat.card (centerIn Q) = 2 := by
  rw [card_centerIn]
  exact hext.2.2.2

theorem centerIn_eq_zpowers [Finite G] {Q : Subgroup G} {z : G}
    (hext : CFSG.IsExtraspecialPGroup 2 Q) (hz : z ∈ centerIn Q) (hz1 : z ≠ 1) :
    centerIn Q = zpowers z := by
  refine (eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm
  rw [card_centerIn_of_extraspecial hext]
  have h1 : Nat.card (zpowers z) ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one, zpowers_eq_bot]
    exact hz1
  have h0 : 0 < Nat.card (zpowers z) := Nat.card_pos
  omega

theorem eq_of_mem_zpowers {z y : G} (hz : orderOf z = 2) (hy : y ∈ zpowers z) (hy1 : y ≠ 1) :
    y = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hz] at hy1 ⊢
  have h : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h
  · rw [h, zpow_zero] at hy1
    exact absurd rfl hy1
  · rw [h, zpow_one]

theorem mem_normalizer_centerIn {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G)) :
    n ∈ normalizer (centerIn H : Set G) := by
  have key : ∀ m ∈ normalizer (H : Set G), ∀ c ∈ centerIn H, m * c * m⁻¹ ∈ centerIn H := by
    intro m hm c ⟨hcH, hcC⟩
    refine ⟨(mem_normalizer_iff.mp hm c).mp hcH, mem_centralizer_iff.mpr fun h hh => ?_⟩
    have hh' : m⁻¹ * h * m ∈ H := by
      have := (mem_normalizer_iff.mp hm (m⁻¹ * h * m)).mpr
      apply this
      simpa [mul_assoc] using hh
    have hc' := mem_centralizer_iff.mp hcC _ hh'
    calc h * (m * c * m⁻¹) = m * ((m⁻¹ * h * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * h * m)) * m⁻¹ := by rw [hc']
      _ = m * c * m⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key n hn c, fun hc => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hc
  simpa [mul_assoc] using this

theorem mem_normalizer_centralizer {H : Subgroup G} {n : G} (hn : n ∈ normalizer (H : Set G)) :
    n ∈ normalizer (centralizer (H : Set G) : Set G) := by
  have key : ∀ m ∈ normalizer (H : Set G), ∀ c ∈ centralizer (H : Set G),
      m * c * m⁻¹ ∈ centralizer (H : Set G) := by
    intro m hm c hc
    refine mem_centralizer_iff.mpr fun h hh => ?_
    have hh' : m⁻¹ * h * m ∈ H := by
      apply (mem_normalizer_iff.mp hm (m⁻¹ * h * m)).mpr
      simpa [mul_assoc] using hh
    have hc' := mem_centralizer_iff.mp hc _ hh'
    calc h * (m * c * m⁻¹) = m * ((m⁻¹ * h * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * h * m)) * m⁻¹ := by rw [hc']
      _ = m * c * m⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key n hn c, fun hc => ?_⟩
  have := key n⁻¹ (inv_mem hn) _ hc
  simpa [mul_assoc] using this

theorem centerIn_map_of_injective {H G' : Type} [Group H] [Group G'] (f : H →* G')
    (hf : Function.Injective f) (X : Subgroup H) : centerIn (X.map f) = (centerIn X).map f := by
  apply le_antisymm
  · rintro _ ⟨⟨a, ha, rfl⟩, hac⟩
    refine ⟨a, ⟨ha, mem_centralizer_iff.mpr fun b hb => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hac (f b) ⟨b, hb, rfl⟩
  · rintro _ ⟨a, ⟨ha, hac⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hac b hb]

theorem four_le_card_of_isSylowOf [Finite G] {R H : Subgroup G} (hR : IsSylowOf 2 R H)
    (h2 : 2 ≤ Open.pRank 2 H) : 4 ≤ Nat.card R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEH, -, hE⟩ := SectionRank.exists_pRank one_lt_two H
  have hdvd : 2 ^ 2 ∣ Nat.card H :=
    (hE ▸ pow_dvd_pow 2 h2 : 2 ^ 2 ∣ Nat.card E).trans (Subgroup.card_dvd_of_le hEH)
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  rw [hR.card_eq]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (Nat.card H).factorization 2 := Nat.pow_le_pow_right (by norm_num) h1

theorem two_le_pRank_of_four_le [Finite G] {R H : Subgroup G} (hRH : R ≤ H)
    (hR : IsElemAbelian 2 R) (h4 : 4 ≤ Nat.card R) : 2 ≤ Open.pRank 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 R := fun r => ⟨1, Subtype.ext (by simpa using hR.2 _ r.2)⟩
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdvd : 2 ^ 2 ∣ Nat.card R := by
    rw [hn]
    refine pow_dvd_pow 2 ?_
    by_contra h
    have : n ≤ 1 := by omega
    have : Nat.card R ≤ 2 := by
      rw [hn]
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        _ = 2 := by norm_num
    omega
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine SectionRank.le_pRank one_lt_two (E := W.map R.subtype)
    ((map_subtype_le W).trans hRH) ?_ ?_
  · refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, -, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, -, rfl⟩⟩ := b
      show (a : G) * b = b * a
      exact congrArg Subtype.val (hR.1.is_comm.comm a b)
    · rintro _ ⟨a, -, rfl⟩
      exact hR.2 _ a.2
  · rw [card_map_of_injective R.subtype_injective, hW]

end Sec3

theorem step31Std_of
    (h75 : AS76b.Asc75Theorem4)
    (h32 : AS76b.Lemma32) : Step31Std := by
  intro G _ _ A A₁ R x hS
  obtain ⟨D, g₀, T₀, hc⟩ := hS.config
  have h := RankTwoExceptional.standard_of_config h75 h32 hS.base.hyp31 hc
  rwa [hS.layer, Sec3.centralizer_zpowers] at h

theorem step31_of (hstd : Step31Std) : Step31 := by
  intro G _ _ A A₁ R x hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hstdA₁, hnn⟩ := hstd G A A₁ R x hS
  have hH := hS.base.hyp
  have hxc : x ∈ centerIn A₁ := by
    rw [hS.center_A₁]
    exact mem_zpowers x
  have hxA : x ∈ A := hS.le hxc.1
  have hx1 : zpowers x ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    intro h
    have h3 := hS.order_x
    rw [h, orderOf_one] at h3
    omega
  have hZ3 : Nat.card (center ↥A₁) = 3 := by
    rw [← Sec3.card_centerIn, hS.center_A₁, Nat.card_zpowers, hS.order_x]
  unfold sec3B
  have hA₁W : A₁ ≤ centralizer ({x} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc.2 a ha)
  have hWlt := card_centralizer_lt_of_rankTwoHypNF hH hS.base.oddCore hx1
  rw [Sec3.centralizer_zpowers] at hWlt
  have hrank := RankTwoL3Even.two_le_pRank_centralizer_subgroupOf (zpowers_le.mpr hxA) hS.le
    hH.rank
  rw [Sec3.centralizer_zpowers] at hrank
  have hH' : RankTwoHypNF ↥(centralizer ({x} : Set G))
      (A₁.subgroupOf (centralizer ({x} : Set G))) :=
    ⟨hstdA₁, hnn, hrank⟩
  let eLL : ↥(A₁.subgroupOf (centralizer ({x} : Set G))) ≃* ↥A₁ := subgroupOfEquivOfLe hA₁W
  have hTL' : Assembly.LowTwoRank.StatedClassicalModel
      (rankTwoQuot (A₁.subgroupOf (centralizer ({x} : Set G)))) .PSL 3 2 2 :=
    SectionRank.statedClassicalModel_of_mulEquiv (RankTwoExceptional.quotCenterCongr eLL)
      hS.typeA₁
  obtain ⟨-, hii, -⟩ := (hS.below _ _ hWlt).1 hH' 2 le_rfl hTL'
  rcases hii rfl with ⟨⟨eS⟩, hZ⟩ | ⟨⟨eE⟩, -⟩
  swap
  · exfalso
    have hcardE : Nat.card (center ↥(A₁.subgroupOf (centralizer ({x} : Set G)))) = 4 := by
      rw [Nat.card_congr eE.toEquiv, Nat.card_prod]
      simp
    rw [Sec3.card_center_congr eLL, hZ3] at hcardE
    omega
  let N := rankTwoX (A₁.subgroupOf (centralizer ({x} : Set G)))
  let eN : ↥N ≃* ↥(N.map (centralizer ({x} : Set G)).subtype) :=
    N.equivMapOfInjective _ (Subgroup.subtype_injective _)
  have hxB : x ∈ N.map (centralizer ({x} : Set G)).subtype :=
    ⟨⟨x, hA₁W hxc.1⟩, subset_normalClosure (mem_subgroupOf.mpr hxc.1), rfl⟩
  refine ⟨?_, Sec3.commutator_eq_top_of_mulEquiv eN
    (RankTwoExceptional.commutator_rankTwoX hstdA₁.1.1),
    ⟨(RankTwoExceptional.quotCenterCongr eN).symm.trans eS⟩⟩
  have hle : zpowers x ≤ centerIn (N.map (centralizer ({x} : Set G)).subtype) :=
    zpowers_le.mpr ⟨hxB, mem_centralizer_iff.mpr fun b hb => by
      obtain ⟨w, -, rfl⟩ := hb
      exact (mem_centralizer_singleton_iff.mp w.2)⟩
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [Sec3.card_centerIn, ← Sec3.card_center_congr eN, Nat.card_zpowers, hS.order_x]
  exact Nat.le_of_dvd (by norm_num) hZ

end CFSG.ComponentClassification.AS81
