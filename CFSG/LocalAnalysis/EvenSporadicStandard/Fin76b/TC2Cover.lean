module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

@[expose] noncomputable def actOn (E X : Subgroup G) (hX : X ≤ normalizer (E : Set G)) :
    ↥X →* MulAut ↥E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion hX)

omit [Finite G] in
theorem actOn_apply (E X : Subgroup G) (hX : X ≤ normalizer (E : Set G)) (x : ↥X) (e : ↥E) :
    (((actOn E X hX) x e : ↥E) : G) = (x : G) * e * (x : G)⁻¹ := rfl

omit [Finite G] in
theorem actOn_ker {E X : Subgroup G} (hX : X ≤ normalizer (E : Set G)) {x : ↥X}
    (hx : x ∈ (actOn E X hX).ker) : ∀ e ∈ E, (x : G) * e = e * (x : G) := by
  intro e he
  have h1 := congrArg (fun m : MulAut ↥E => ((m ⟨e, he⟩ : ↥E) : G)) (MonoidHom.mem_ker.1 hx)
  simp only [MulAut.one_apply] at h1
  have h2 : (x : G) * e * (x : G)⁻¹ = e := h1
  calc (x : G) * e = (x : G) * e * (x : G)⁻¹ * (x : G) := by group
    _ = e * (x : G) := by rw [h2]

omit [Finite G] in
theorem actOn_range_le {E X : Subgroup G} (hX : X ≤ normalizer (E : Set G))
    (hXz : X ≤ centralizer ({z} : Set G)) :
    (actOn E X hX).range ≤
      ((centralizer ({z} : Set G)).subgroupOf (normalizer (E : Set G))).map
        E.normalizerMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Subgroup.inclusion hX x, mem_subgroupOf.2 (hXz x.2), rfl⟩

omit [Finite G] in
theorem WFacts.cent_le_normalizer (hW : WFacts L t E) :
    L ⊓ centralizer ({t} : Set G) ≤ normalizer (E : Set G) := by
  intro w hw
  have hwL : w ∈ L := hw.1
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 hw.2
  have hwt' : w⁻¹ * t = t * w⁻¹ := by
    calc w⁻¹ * t = w⁻¹ * (t * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * t) * w⁻¹ := by rw [hwt]
      _ = t * w⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hW.normal w hwL hwt e he
  · intro he
    have := hW.normal w⁻¹ (L.inv_mem hwL) hwt' _ he
    simpa [mul_assoc] using this

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem T_le_normalizer (hzt : ∃ y : G, y * z * y⁻¹ = z * t) : T ≤ normalizer (E : Set G) :=
  fun _ hg => h.mem_normalizer_of_mem_normalizer hzt (Subgroup.le_normalizer hg)

include h in
theorem dvd_card_range_T (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hT : Nat.card ↥T = 512) :
    128 ∣ Nat.card (actOn E T (h.T_le_normalizer hzt)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := actOn E T (h.T_le_normalizer hzt) with hf
  have hker4 : Nat.card f.ker ≤ 4 := by
    have hle : f.ker.map T.subtype ≤ zpowers z ⊔ zpowers t := by
      rintro _ ⟨k, hk, rfl⟩
      have hzmem : z ∈ zpowers z ⊔ zpowers t := mem_sup_left (mem_zpowers z)
      have htmem : t ∈ zpowers z ⊔ zpowers t := mem_sup_right (mem_zpowers t)
      rcases h.C k k.2 (actOn_ker (h.T_le_normalizer hzt) hk) with h1 | h1 | h1 | h1
      · rw [Subgroup.coe_subtype, h1]
        exact one_mem _
      · rw [Subgroup.coe_subtype, h1]
        exact hzmem
      · rw [Subgroup.coe_subtype, h1]
        exact htmem
      · rw [Subgroup.coe_subtype, h1]
        exact mul_mem hzmem htmem
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective T.subtype_injective, h.card_zpowers_sup] at this
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hT] at h1
  have h128 : 128 ≤ Nat.card f.range := by
    have : Nat.card f.ker * Nat.card f.range ≤ 4 * Nat.card f.range :=
      Nat.mul_le_mul_right _ hker4
    omega
  have hp : IsPGroup 2 f.range :=
    h.cfg.T_pgroup.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h128 ⊢
  have h7 : 7 ≤ n := by
    have : 2 ^ 7 ≤ 2 ^ n := by simpa using h128
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  exact (pow_dvd_pow 2 h7)

end OuterE

theorem WFacts.le_card_range_cent (hW : WFacts L t E) (ht2 : orderOf t = 2) :
    960 ≤ Nat.card (actOn E (L ⊓ centralizer ({t} : Set G)) hW.cent_le_normalizer).range := by
  set f := actOn E (L ⊓ centralizer ({t} : Set G)) hW.cent_le_normalizer with hf
  have hker : f.ker.map (L ⊓ centralizer ({t} : Set G)).subtype ≤ zpowers t := by
    rintro _ ⟨k, hk, rfl⟩
    have hkc := actOn_ker hW.cent_le_normalizer hk
    rcases hW.cent k k.2.1 hkc with h1 | h1
    · rw [Subgroup.coe_subtype, h1]
      exact one_mem _
    · rw [Subgroup.coe_subtype, h1]
      exact mem_zpowers t
  have hcard : Nat.card f.ker ≤ 2 := by
    have := Subgroup.card_le_of_le hker
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_zpowers,
      ht2] at this
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hW.card_cent] at h1
  have : Nat.card f.ker * Nat.card f.range ≤ 2 * Nat.card f.range :=
    Nat.mul_le_mul_right _ hcard
  omega

namespace OuterE

variable (h : OuterE G L z t T E)

include h in
theorem exists_cover (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) (α : MulAut ↥E) :
    ∃ n : ↥(normalizer (E : Set G)), (n : G) ∈ centralizer ({z} : Set G) ∧
      E.normalizerMonoidHom n = α := by
  set Wsub : Subgroup (MulAut ↥E) :=
    ((centralizer ({z} : Set G)).subgroupOf (normalizer (E : Set G))).map
      E.normalizerMonoidHom with hWsub
  have hTz : T ≤ centralizer ({z} : Set G) := h.cfg.T_le
  have hCz : L ⊓ centralizer ({t} : Set G) ≤ centralizer ({z} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.2 (h.cfg.z_comm_of_mem_A hw.1)
  have hr1 : (actOn E T (h.T_le_normalizer hzt)).range ≤ Wsub := actOn_range_le _ hTz
  have hr2 : (actOn E (L ⊓ centralizer ({t} : Set G)) hW.cent_le_normalizer).range ≤ Wsub :=
    actOn_range_le _ hCz
  have h960 : 960 ≤ Nat.card Wsub :=
    (hW.le_card_range_cent h.t_order).trans (Subgroup.card_le_of_le hr2)
  have h128 : 128 ∣ Nat.card Wsub :=
    (h.dvd_card_range_T hzt hT).trans (Subgroup.card_dvd_of_le hr1)
  have hdvd : Nat.card Wsub ∣ 1920 := by
    rw [← haut]
    exact Subgroup.card_subgroup_dvd_card Wsub
  have hW1920 : Nat.card Wsub = 1920 := by
    obtain ⟨j, hj⟩ := h128
    rw [hj] at h960 hdvd ⊢
    have hj15 : j ∣ 15 := by
      have : 128 * j ∣ 128 * 15 := by simpa using hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have hj_le : j ≤ 15 := Nat.le_of_dvd (by norm_num) hj15
    have hj8 : 8 ≤ j := by omega
    have hj' : j = 15 := by
      interval_cases j
      all_goals first
        | rfl
        | (exfalso; revert hj15; decide)
    rw [hj']
  have : Finite (MulAut ↥E) := Nat.finite_of_card_ne_zero (by rw [haut]; norm_num)
  have htop : Wsub = ⊤ := Subgroup.eq_top_of_card_eq Wsub (by rw [hW1920, haut])
  have hα : α ∈ Wsub := by
    rw [htop]
    exact mem_top α
  obtain ⟨n, hn, hnα⟩ := hα
  exact ⟨n, mem_subgroupOf.1 hn, hnα⟩

include h in
theorem normalizer_eq_mul (hzt : ∃ y : G, y * z * y⁻¹ = z * t) (hW : WFacts L t E)
    (haut : Nat.card (MulAut ↥E) = 1920) (hT : Nat.card ↥T = 512) {m : G}
    (hm : m ∈ normalizer (E : Set G)) :
    ∃ c ∈ centralizer (E : Set G), ∃ n ∈ normalizer (E : Set G),
      n ∈ centralizer ({z} : Set G) ∧ m = c * n := by
  obtain ⟨n, hnz, hn⟩ := h.exists_cover hzt hW haut hT (E.normalizerMonoidHom ⟨m, hm⟩)
  have hker : (⟨m, hm⟩ * n⁻¹ : ↥(normalizer (E : Set G))) ∈ E.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hn, mul_inv_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  have hc : m * (n : G)⁻¹ ∈ centralizer (E : Set G) := mem_subgroupOf.1 hker
  exact ⟨m * (n : G)⁻¹, hc, n, n.2, hnz, by group⟩

end OuterE

end CFSG.EvenSporadicStandard.Fin76b
