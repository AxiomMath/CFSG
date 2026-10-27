module

public import CFSG.LocalAnalysis.EvenBN.U5.Setting
public import CFSG.LocalAnalysis.ZStar
public import CFSG.RankThree.PartOne.U5K.Hyp.Parabolic

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {T H X : Subgroup G}
    (hT : IsSylowOf p T H) (hXH : X ≤ H) (hX : IsPGroup p X) :
    ∃ c ∈ H, ∀ x ∈ X, c⁻¹ * x * c ∈ T := by
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S Q
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hXH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  refine ⟨s, hs, ?_⟩
  have : (c : G) * s * (c : G)⁻¹ = x := by
    have := congrArg Subtype.val hsx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  rw [Subgroup.subtype_apply, ← this]
  group

section Generic

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {z : G} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).2
  have hz' : z ∈ ((A ⊔ B : Subgroup G) : Set G) := hz
  rw [hset] at hz'
  obtain ⟨a, ha, b, hb, rfl⟩ := hz'
  exact ⟨a, ha, b, hb, rfl⟩

theorem exists_conj_ne_commute [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    ∃ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) ∧ g * t * g⁻¹ ≠ t := by
  by_contra hcon
  push Not at hcon
  have := Fintype.ofFinite G
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hcon
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  ·
    have hcen : t ∈ center G := by
      rw [mem_center_iff]
      intro g
      have h1 := hNt g
      rw [hb, mem_bot, mul_inv_eq_one] at h1
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · rw [hc, mem_bot] at hcen
      exact ht1 hcen
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
  ·
    rw [ht, Subgroup.card_top] at hNodd
    have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
    have hdvd : 2 ∣ Nat.card G := h2 ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 hdvd)

theorem exists_normalizer_conj_eq_of_weakly_closed_in {p : ℕ} [Fact p.Prime] {x g : G}
    {T R : Subgroup G} (hT : IsSylowOf p T (centralizer ({x} : Set G))) (hRT : R ≤ T)
    (hwc : ∀ c : G, (∀ r ∈ R, c⁻¹ * r * c ∈ T) → ∀ r ∈ R, c⁻¹ * r * c ∈ R)
    (hy : ∀ r ∈ R, r * (g⁻¹ * x * g) = (g⁻¹ * x * g) * r) :
    ∃ n ∈ normalizer (R : Set G), n⁻¹ * x * n = g⁻¹ * x * g := by
  set y := g⁻¹ * x * g with hydef
  have hT' : IsSylowOf p (T.map (MulAut.conj g⁻¹).toMonoidHom)
      (centralizer ({y} : Set G)) := by
    have hTle := hT.le
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT ⊢
    obtain ⟨hle, hP, hdvd⟩ := hT
    have hC : (centralizer ({x} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        centralizer ({y} : Set G) := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
        have hw' : w * x = x * w := mem_centralizer_singleton_iff.1 hw
        refine mem_centralizer_singleton_iff.2 ?_
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hydef]
        calc g⁻¹ * w * g * (g⁻¹ * x * g) = g⁻¹ * (w * x) * g := by group
          _ = g⁻¹ * (x * w) * g := by rw [hw']
          _ = g⁻¹ * x * g * (g⁻¹ * w * g) := by group
      · intro hz
        have hz' : z * y = y * z := mem_centralizer_singleton_iff.1 hz
        refine Subgroup.mem_map.2 ⟨g * z * g⁻¹, mem_centralizer_singleton_iff.2 ?_,
          by simp; group⟩
        calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [← hydef, hz']
          _ = x * (g * z * g⁻¹) := by group
    refine ⟨?_, hP.map _, ?_⟩
    · rw [← hC]
      exact Subgroup.map_mono hle
    · rw [← hC, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hdvd
  have hRy : R ≤ centralizer ({y} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (hy r hr)
  obtain ⟨c, hcC, hc⟩ := exists_conj_le_of_isSylowOf hT' hRy
    ((hT.isPGroup).to_le hRT)
  have hmT : ∀ r ∈ R, (c * g⁻¹)⁻¹ * r * (c * g⁻¹) ∈ T := by
    intro r hr
    obtain ⟨s, hs, hsr⟩ := hc r hr
    have : (c * g⁻¹)⁻¹ * r * (c * g⁻¹) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hsr
      rw [mul_inv_rev, inv_inv]
      calc g * c⁻¹ * r * (c * g⁻¹) = g * (c⁻¹ * r * c) * g⁻¹ := by group
        _ = g * (g⁻¹ * s * g) * g⁻¹ := by rw [hsr]
        _ = s := by group
    rw [this]
    exact hs
  have hmR := hwc _ hmT
  have hmN : (c * g⁻¹)⁻¹ ∈ normalizer (R : Set G) :=
    mem_normalizer_of_conj_le fun r hr => by
      have := hmR r hr
      simpa using this
  refine ⟨(c * g⁻¹)⁻¹, hmN, ?_⟩
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
  calc ((c * g⁻¹)⁻¹)⁻¹ * x * (c * g⁻¹)⁻¹ = c * (g⁻¹ * x * g) * c⁻¹ := by group
    _ = y := by rw [← hydef, hcy]; group

end Generic

namespace Data

theorem Hyp.mem_zpowers_of_mem_inf (hd : d.Hyp) {X : Subgroup G} (hXT : X ≤ d.T)
    (hX : CFSG.IsElementaryAbelian 2 X) {x : G} (hxX : x ∈ X)
    (hxL : x ∈ centralizer (d.L : Set G)) : x ∈ zpowers d.t := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  · have hx2 : x ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hxX
    have ho : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    rw [hd.eq_t_of_mem (hXT hxX) hxL ho]
    exact mem_zpowers _

theorem Hyp.card_inf_centralizer_le (hd : d.Hyp) {X : Subgroup G} (hXT : X ≤ d.T)
    (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card (X ⊓ centralizer (d.L : Set G) : Subgroup G) ≤ 2 := by
  have hle : X ⊓ centralizer (d.L : Set G) ≤ zpowers d.t := fun x hx =>
    hd.mem_zpowers_of_mem_inf hXT hX hx.1 hx.2
  calc Nat.card (X ⊓ centralizer (d.L : Set G) : Subgroup G) ≤ Nat.card (zpowers d.t) :=
        Subgroup.card_le_of_le hle
    _ = 2 := hd.card_zpowers_t

theorem Hyp.card_le_of_le_T (hd : d.Hyp) {X : Subgroup G} (hXT : X ≤ d.T)
    (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 ∧ (Nat.card X = 2 * (2 ^ f) ^ 4 → X = d.B₁) := by
  have hXN : X ≤ normalizer (d.L : Set G) := hXT.trans hd.T_le_normalizer
  set ψ : X →* MulAut (hypPSU h 2 1) := d.act.comp (Subgroup.inclusion hXN) with hψ
  have hψ_apply : ∀ x : X, ψ x = d.act ⟨x, hXN x.2⟩ := fun _ => rfl
  have hrT : ψ.range ≤ d.actImage d.T := by
    rintro _ ⟨x, rfl⟩
    exact (d.mem_actImage).2 ⟨x, hXT x.2, hXN x.2, rfl⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    have := (hX.toIsMulCommutative.is_comm).comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hrc : ∀ a ∈ ψ.range, ∀ b ∈ ψ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hcomm x x.2 y y.2))
  have hrs : ∀ a ∈ ψ.range, a * a = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have hx2 : (x : G) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (x : G) x.2
    have : x * x = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← sq, hx2]; rfl)
    rw [this, map_one]
  have hq3 : 3 ≤ 2 ^ f := by have := hd.four_le; omega
  obtain ⟨hrange, hrange_eq⟩ := elemAb_T hd.center_hypPSU hq3 hd.inf_Pi_actImage_T hrT hrc hrs
  have hker : Nat.card ψ.ker ≤ 2 := by
    calc Nat.card ψ.ker = Nat.card (ψ.ker.map X.subtype) :=
          (Subgroup.card_map_of_injective X.subtype_injective).symm
      _ ≤ Nat.card (X ⊓ centralizer (d.L : Set G) : Subgroup G) := by
          refine Subgroup.card_le_of_le ?_
          rintro _ ⟨z, hz, rfl⟩
          exact ⟨z.2, (d.act_eq_one_iff _).1 (MonoidHom.mem_ker.1 hz)⟩
      _ ≤ 2 := hd.card_inf_centralizer_le hXT hX
  have hprod := Subgroup.card_ker_mul_card_range ψ
  refine ⟨?_, fun hcard => ?_⟩
  · rw [← hprod]
    exact Nat.mul_le_mul hker hrange
  ·
    have hpos : 0 < (2 ^ f) ^ 4 := by positivity
    have hr4 : Nat.card ψ.range = (2 ^ f) ^ 4 := by
      refine le_antisymm hrange ?_
      by_contra hlt
      push Not at hlt
      have : Nat.card ψ.ker * Nat.card ψ.range < 2 * (2 ^ f) ^ 4 :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt two_pos)
      rw [hprod, hcard] at this
      exact lt_irrefl _ this
    have hV := hrange_eq hr4
    have hXB : X ≤ d.B₁ := by
      intro x hx
      have hmem : ψ ⟨x, hx⟩ ∈ d.actImage d.A₁ := by
        rw [d.actImage_A₁, ← hV]
        exact ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨a, haA, haN, ha⟩ := (d.mem_actImage).1 hmem
      have hc : a⁻¹ * x ∈ centralizer (d.L : Set G) := by
        refine (d.act_eq_one_iff ⟨a⁻¹ * x, mul_mem (inv_mem haN) (hXN hx)⟩).1 ?_
        have : (⟨a⁻¹ * x, mul_mem (inv_mem haN) (hXN hx)⟩ : normalizer (d.L : Set G)) =
            (⟨a, haN⟩ : normalizer (d.L : Set G))⁻¹ * ⟨x, hXN hx⟩ := rfl
        rw [this, map_mul, map_inv, ha, hψ_apply, inv_mul_cancel]
      have haL : a ∈ d.L := d.A₁_le_P.trans d.P_le_L haA
      have hcT : a⁻¹ * x ∈ d.T := mul_mem (inv_mem (hd.A₁_le_T haA)) (hXT hx)
      have hc2 : (a⁻¹ * x) ^ 2 = 1 := by
        have hx2 : x ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
        have ha2 : a * a = 1 := d.A₁_comm_sq.2 a haA
        set c := a⁻¹ * x with hcdef
        have hac : a * c = c * a := mem_centralizer_iff.1 hc a haL
        have hxc : x = a * c := by rw [hcdef]; group
        calc c ^ 2 = (a * a) * (c * c) := by rw [ha2, one_mul, sq]
          _ = a * (a * c) * c := by group
          _ = a * (c * a) * c := by rw [hac]
          _ = (a * c) * (a * c) := by group
          _ = x ^ 2 := by rw [hxc, sq]
          _ = 1 := hx2
      have hct : a⁻¹ * x ∈ zpowers d.t := by
        by_cases h1 : a⁻¹ * x = 1
        · rw [h1]
          exact one_mem _
        · rw [hd.eq_t_of_mem hcT hc (orderOf_eq_prime hc2 h1)]
          exact mem_zpowers _
      rw [show x = (a⁻¹ * x) * a by
        rw [← mem_centralizer_iff.1 hc a haL]; group]
      exact mul_mem (mem_sup_left hct) (mem_sup_right haA)
    exact Subgroup.eq_of_le_of_card_ge hXB (by rw [hd.card_B₁, hcard])

theorem Hyp.card_le_of_le_centralizer (hd : d.Hyp) {X : Subgroup G}
    (hXC : X ≤ centralizer ({d.t} : Set G)) (hX : CFSG.IsElementaryAbelian 2 X) :
    Nat.card X ≤ 2 * (2 ^ f) ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf hd.T_syl hXC (hX.isPGroup 2 X)
  set X' : Subgroup G := X.map (MulAut.conj c⁻¹).toMonoidHom with hX'
  have hX'T : X' ≤ d.T := by
    rintro _ ⟨x, hx, rfl⟩
    have := hc x hx
    simpa [MulAut.conj_apply] using this
  have hX'e : CFSG.IsElementaryAbelian 2 X' := CFSG.IsElementaryAbelian.map _
  have hcard : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  rw [← hcard]
  exact (hd.card_le_of_le_T hX'T hX'e).1

theorem Hyp.sec3_1_one (hd : d.Hyp) :
    CFSG.IsElementaryAbelian 2 d.B₁ ∧ Nat.card d.B₁ = 2 * (2 ^ f) ^ 4 ∧ d.B₁ ≤ d.T ∧
      (∀ X : Subgroup G, X ≤ centralizer ({d.t} : Set G) → CFSG.IsElementaryAbelian 2 X →
        Nat.card X ≤ 2 * (2 ^ f) ^ 4) ∧
      ∀ X : Subgroup G, X ≤ d.T → CFSG.IsElementaryAbelian 2 X →
        Nat.card X = 2 * (2 ^ f) ^ 4 → X = d.B₁ :=
  ⟨hd.isElementaryAbelian_B₁, hd.card_B₁, hd.B₁_le_T,
    fun _ hXC hX => hd.card_le_of_le_centralizer hXC hX,
    fun _ hXT hX hcard => (hd.card_le_of_le_T hXT hX).2 hcard⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
