module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwoClosure

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def U3SixNineFourInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → U3U1Data G L f t T R₂ U₁ →
    (¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) →
    (∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T) →
    (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁ →
    (∀ c ∈ T, c ^ 2 ∈ szT₁ L T ⊔ zpowers t) →
    ¬ ∀ v ∈ T, v ^ 2 = 1 → v ∉ szT₁ L T ⊔ zpowers t →
      ∃ g ∈ normalizer (szA₁ (szT₁ L T) : Set G) ⊓ normalizer (R₂ : Set G), g⁻¹ * t * g = v

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem inv_mul_sq_not_mem_of_not_isCyclic (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T) {s : G} (hs : s ∈ T) :
    t⁻¹ * s ^ 2 ∉ szT₁ L T := by
  obtain ⟨htT, -, -, hTN₁, -, hMn, -⟩ := h.start_of_card_sylow hS2
  have hcycM := h.isCyclic_quotient_of_card_sylow hS2
  obtain ⟨g₀, hg₀⟩ := hcycM.exists_zpow_surjective
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g₀
  have hbgen : ∀ s ∈ T, ∃ k : ℤ, ((b : G) ^ k)⁻¹ * s ∈ szT₁ L T ⊔ zpowers t := by
    intro s hs
    obtain ⟨k, hk⟩ := hg₀ (QuotientGroup.mk ⟨s, hs⟩)
    refine ⟨k, ?_⟩
    simp only at hk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf] at hk
    simpa using hk
  have hbT : (b : G) ∈ T := b.2
  have htc : ∀ x ∈ T, x * t = t * x := fun x hx => mem_centralizer_singleton_iff.mp (h.le hx)
  intro hst
  obtain ⟨k, hk⟩ := hbgen s hs
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hk
  have hbk : (b : G) ^ k ∈ T := zpow_mem hbT k
  have hyT : y ∈ T := szT₁_le_left L T hy
  have hconj : ((b : G) ^ k)⁻¹ * y * (b : G) ^ k ∈ szT₁ L T :=
    (mem_normalizer_iff''.mp (hTN₁ hbk) y).mp hy
  have h1 : ((b : G) ^ k * (b : G) ^ k)⁻¹ * s ^ 2 ∈ szT₁ L T := by
    have hs' : s = (b : G) ^ k * (y * z) := by rw [hyz]; group
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · rw [hs', hz1, mul_one, sq,
        show ((b : G) ^ k * (b : G) ^ k)⁻¹ * ((b : G) ^ k * y * ((b : G) ^ k * y)) =
          (((b : G) ^ k)⁻¹ * y * (b : G) ^ k) * y by group]
      exact mul_mem hconj hy
    · have e : ((b : G) ^ k * (b : G) ^ k)⁻¹ * ((b : G) ^ k * (y * t)) ^ 2 =
          (((b : G) ^ k)⁻¹ * y * (b : G) ^ k) * y * (t * t) := by
        rw [sq]
        calc ((b : G) ^ k * (b : G) ^ k)⁻¹ * ((b : G) ^ k * (y * t) * ((b : G) ^ k * (y * t))) =
            ((b : G) ^ k)⁻¹ * y * (t * (b : G) ^ k) * y * t := by group
          _ = ((b : G) ^ k)⁻¹ * y * ((b : G) ^ k * t) * y * t := by rw [htc _ hbk]
          _ = (((b : G) ^ k)⁻¹ * y * (b : G) ^ k) * (t * y) * t := by group
          _ = (((b : G) ^ k)⁻¹ * y * (b : G) ^ k) * (y * t) * t := by rw [htc _ hyT]
          _ = _ := by group
      rw [hs', hz1, e, show t * t = 1 by rw [← sq, h.sq_eq_one], mul_one]
      exact mul_mem hconj hy
  have h2 : ((b : G) ^ k * (b : G) ^ k)⁻¹ * t ∈ szT₁ L T := by
    have := mul_mem h1 (inv_mem hst)
    rwa [show ((b : G) ^ k * (b : G) ^ k)⁻¹ * s ^ 2 * (t⁻¹ * s ^ 2)⁻¹ =
      ((b : G) ^ k * (b : G) ^ k)⁻¹ * t by group] at this
  apply hncyc
  refine ⟨b, hbT, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := hbgen x hx
  obtain ⟨y', hy', z', hz', hyz'⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hj
  rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz' with hz1 | hz1
  · exact ⟨j, by rw [← hyz', hz1, mul_one]; exact hy'⟩
  · refine ⟨j + (k + k), ?_⟩
    have hbkk : (b : G) ^ k * (b : G) ^ k ∈ T := mul_mem hbk hbk
    have h3 : ((b : G) ^ k * (b : G) ^ k)⁻¹ * y' * ((b : G) ^ k * (b : G) ^ k) ∈ szT₁ L T :=
      (mem_normalizer_iff''.mp (hTN₁ hbkk) y').mp hy'
    have e : ((b : G) ^ (j + (k + k)))⁻¹ * x =
        (((b : G) ^ k * (b : G) ^ k)⁻¹ * y' * ((b : G) ^ k * (b : G) ^ k)) *
          (((b : G) ^ k * (b : G) ^ k)⁻¹ * t) := by
      have hx' : x = (b : G) ^ j * (y' * z') := by rw [hyz']; group
      rw [hx', hz1, zpow_add, zpow_add]
      group
    rw [e]
    exact mul_mem h3 h2

end U3Start

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

section Certificates

theorem false_of_forall_conj_of_card_sylow (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hncyc : ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T)
    (hS : ∃ S : Sylow 2 G, (S : Subgroup G) = U₁ ⊔ T)
    (hC : (U₁ ⊔ T) ⊓ centralizer (R₂ : Set G) ≤ U₁)
    (hc : ∃ c ∈ T, c ^ 2 ∉ szT₁ L T ⊔ zpowers t)
    (hall : ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t →
      ∃ g ∈ normalizer (R₂ : Set G), g⁻¹ * t * g = w) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hS
  obtain ⟨htT, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hNR, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hTR : T ≤ normalizer (R₂ : Set G) := fun s hs => hNR (hTA hs)
  have hÛR : U₁ ⊔ T ≤ normalizer (R₂ : Set G) :=
    sup_le (hU.le_centralizer.trans (centralizer_le_normalizer _)) hTR
  have hKn : ((centralizer (R₂ : Set G)).subgroupOf (normalizer (R₂ : Set G))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    simp only [coe_mul, coe_inv]
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have hr' : (g : G)⁻¹ * r * g ∈ R₂ := (mem_normalizer_iff''.mp g.2 r).mp hr
    have h1 := mem_centralizer_iff.mp hx _ hr'
    calc r * ((g : G) * x * (g : G)⁻¹) = g * (((g : G)⁻¹ * r * g) * x) * (g : G)⁻¹ := by group
      _ = g * (x * ((g : G)⁻¹ * r * g)) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * x * (g : G)⁻¹) * r := by group
  set K := (centralizer (R₂ : Set G)).subgroupOf (normalizer (R₂ : Set G)) with hK
  set π : normalizer (R₂ : Set G) →* normalizer (R₂ : Set G) ⧸ K := QuotientGroup.mk' K with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hπeq : ∀ x y : normalizer (R₂ : Set G),
      π x = π y ↔ ((x : G)⁻¹ * y) ∈ centralizer (R₂ : Set G) := fun x y => by
    rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hK,
      mem_subgroupOf]
    simp
  have hSN : (S₀ : Subgroup G) ≤ normalizer (R₂ : Set G) := by rw [hS₀]; exact hÛR
  set Pb : Sylow 2 (normalizer (R₂ : Set G) ⧸ K) := (S₀.subtype hSN).mapSurjective hπ with hPb
  have hmemPb : ∀ x : normalizer (R₂ : Set G), (x : G) ∈ U₁ ⊔ T →
      π x ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) := by
    intro x hx
    rw [hPb, Sylow.coe_mapSurjective]
    refine ⟨x, ?_, rfl⟩
    rw [Sylow.coe_subtype]
    show (x : G) ∈ (S₀ : Subgroup G)
    rw [hS₀]
    exact hx
  have hPbmem : ∀ z ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)),
      ∃ a : normalizer (R₂ : Set G), (a : G) ∈ U₁ ⊔ T ∧ π a = z := by
    intro z hz
    rw [hPb, Sylow.coe_mapSurjective] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    rw [Sylow.coe_subtype] at ha
    have ha' : (a : G) ∈ (S₀ : Subgroup G) := ha
    rw [hS₀] at ha'
    exact ⟨a, ha', rfl⟩
  have hcomm : ∀ x ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)),
      ∀ y ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)), x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hPbmem x hx
    obtain ⟨b, hb, rfl⟩ := hPbmem y hy
    have h1 : ((b * a : normalizer (R₂ : Set G)) : G)⁻¹ * ((a * b : normalizer (R₂ : Set G)) : G) ∈
        centralizer (R₂ : Set G) := by
      have := hU.commutator_le h hS2 hR (commutator_mem_commutator (inv_mem ha) (inv_mem hb))
      rw [commutatorElement_def] at this
      simp only [coe_mul, mul_inv_rev, inv_inv] at this ⊢
      have e : (a : G)⁻¹ * (b : G)⁻¹ * (a * b) = (a : G)⁻¹ * (b : G)⁻¹ * a * b := by group
      rw [e]
      exact hU.le_centralizer this
    rw [← map_mul, ← map_mul]
    exact ((hπeq _ _).mpr h1).symm
  obtain ⟨c, hcT, hc2⟩ := hc
  obtain ⟨k, hk⟩ := h.isPGroup ⟨c ^ 2, pow_mem hcT 2⟩
  have hk' : (c ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨n, hn, hn2⟩ := exists_pow_not_mem_sq_mem_of_two_pow hk' hc2
  obtain ⟨v₀, hv₀T, hv₀2, hv₀S⟩ := u3SplitInput G L f t T h hS2 hncyc
  have hv₀2' : v₀ ^ 2 ∈ szT₁ L T ⊔ zpowers t := by rw [hv₀2]; exact one_mem _
  have hm := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 (pow_mem (pow_mem hcT 2) n) hv₀T hn2 hv₀2'
    hn hv₀S
  obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hm
  obtain ⟨w, hwT, hw2, hwS, hcw⟩ : ∃ w ∈ T, w ^ 2 = 1 ∧ w ∉ szT₁ L T ⊔ zpowers t ∧
      (c ^ n) ^ 2 = y * w := by
    have hcn : (c ^ n) ^ 2 = (c ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
    · refine ⟨v₀, hv₀T, hv₀2, hv₀S, ?_⟩
      rw [hcn, show (c ^ 2) ^ n = (c ^ 2) ^ n * v₀⁻¹ * v₀ by group, ← hyz, hz1, mul_one]
    · obtain ⟨htvT, htv2, htvS⟩ := h.mul_outer_of_card_sylow hS2 hv₀T hv₀2 hv₀S
      refine ⟨t * v₀, htvT, htv2, htvS, ?_⟩
      rw [hcn, show (c ^ 2) ^ n = (c ^ 2) ^ n * v₀⁻¹ * v₀ by group, ← hyz, hz1, mul_assoc]
  obtain ⟨g, hgN, hgw⟩ := hall w hwT hw2 hwS
  set tN : normalizer (R₂ : Set G) := ⟨t, hÛR (mem_sup_right htT)⟩ with htN
  set gN : normalizer (R₂ : Set G) := ⟨g, hgN⟩ with hgN'
  set cN : normalizer (R₂ : Set G) := ⟨c ^ n, hÛR (mem_sup_right (pow_mem hcT n))⟩ with hcN
  have hgt : (π gN)⁻¹ * π tN * π gN = π cN ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, hπeq]
    simp only [htN, hgN', hcN, coe_mul, coe_inv, coe_pow]
    rw [hgw, hcw]
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have hr' : w * r * w⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hTR hwT) r).mp hr
    have h1 := hR.commT₁ y hy _ hr'
    calc r * (w⁻¹ * (y * w)) = w⁻¹ * ((w * r * w⁻¹) * y) * w := by group
      _ = w⁻¹ * (y * (w * r * w⁻¹)) * w := by rw [h1]
      _ = w⁻¹ * (y * w) * r := by group
  have htP : π tN ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) := hmemPb tN (mem_sup_right htT)
  have hcP : π cN ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) :=
    hmemPb cN (mem_sup_right (pow_mem hcT n))
  have hx : π tN ∈ centralizer ((Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) : Set _) :=
    mem_centralizer_iff.mpr fun z hz => hcomm z hz _ htP
  have hy' : (π gN)⁻¹ * π tN * π gN ∈
      centralizer ((Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) : Set _) := by
    rw [hgt]
    exact mem_centralizer_iff.mpr fun z hz => hcomm z hz _ (pow_mem hcP 2)
  obtain ⟨m, hmN, hmt⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer Pb (π tN) (π gN) hx hy'
  have hsq : π tN = (m * π cN * m⁻¹) ^ 2 := by
    have h1 : m⁻¹ * π tN * m = π cN ^ 2 := by rw [← hmt, hgt]
    calc π tN = m * (m⁻¹ * π tN * m) * m⁻¹ := by group
      _ = m * π cN ^ 2 * m⁻¹ := by rw [h1]
      _ = (m * π cN * m⁻¹) ^ 2 := by rw [sq, sq]; group
  have hmc : m * π cN * m⁻¹ ∈ (Pb : Subgroup (normalizer (R₂ : Set G) ⧸ K)) :=
    (mem_normalizer_iff.mp hmN _).mp hcP
  obtain ⟨a, ha, hae⟩ := hPbmem _ hmc
  have h1 : t⁻¹ * (a : G) ^ 2 ∈ centralizer (R₂ : Set G) := by
    have := (hπeq tN (a ^ 2)).mp (by rw [map_pow, hae, ← hsq])
    simpa [htN] using this
  have h2 : t⁻¹ * (a : G) ^ 2 ∈ U₁ :=
    hC (mem_inf.mpr ⟨mul_mem (inv_mem (mem_sup_right htT)) (pow_mem ha 2), h1⟩)
  have hTU := hU.le_normalizer h hS2 hR
  obtain ⟨u, hu, s, hs, hus⟩ := exists_mul_eq_of_mem_sup_of_le_normalizer hTU ha
  have htU : t ∈ normalizer (U₁ : Set G) := hTU htT
  have hsu : s * u * s⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (hTU hs) u).mp hu
  have h3 : t⁻¹ * s ^ 2 ∈ szT₁ L T := by
    rw [← hU.inf_eq h hR]
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem htT) (pow_mem hs 2)⟩
    have e : t⁻¹ * s ^ 2 =
        (t⁻¹ * ((s * u * s⁻¹)⁻¹ * u⁻¹) * t) * (t⁻¹ * (a : G) ^ 2) := by
      rw [← hus, sq, sq]; group
    rw [e]
    refine mul_mem ?_ h2
    have := (mem_normalizer_iff''.mp htU _).mp (mul_mem (inv_mem hsu) (inv_mem hu))
    simpa [mul_assoc] using this
  exact h.inv_mul_sq_not_mem_of_not_isCyclic hS2 hncyc hs h3

end Certificates

end U3U1Data

section Certificates

theorem u3SixNineNormInput_of_four (hfour : U3SixNineFourInput) : U3SixNineNormInput := by
  intro G _ _ L f t T R₂ U₁ h hS2 hR hU hncyc hS hC
  by_cases hc : ∃ c ∈ T, c ^ 2 ∉ szT₁ L T ⊔ zpowers t
  · intro hall
    refine hU.false_of_forall_conj_of_card_sylow h hS2 hR hncyc hS hC hc fun w hw hw2 hwS => ?_
    obtain ⟨g, hg, hgw⟩ := hall w hw hw2 hwS
    exact ⟨g, (mem_inf.mp hg).2, hgw⟩
  · push Not at hc
    exact hfour G L f t T R₂ U₁ h hS2 hR hU hncyc hS hC hc

theorem u3SixNineInput_of_four (hfour : U3SixNineFourInput) : U3SixNineInput :=
  u3SixNineInput_of_norm (u3SixNineNormInput_of_four hfour)

end Certificates

end CFSG.SeitzReduction.RankOne
