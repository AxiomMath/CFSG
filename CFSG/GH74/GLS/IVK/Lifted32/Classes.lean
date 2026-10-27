module

public import CFSG.GH74.GLS.IVK.Lifted32.Lattice

public section

namespace CFSG.GH74.GLS.IVK.Lifted32

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5
open scoped commutatorElement

namespace Cls

section Elementary

variable {G : Type} [Group G]

theorem exists_conj_of_odd {u v : G} (hu : u * u = 1) (hv : v * v = 1)
    (hodd : Odd (orderOf (u⁻¹ * v))) : ∃ n ∈ zpowers (u⁻¹ * v), n * u * n⁻¹ = v := by
  obtain ⟨j, hj⟩ := hodd
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  set w := u⁻¹ * v with hw
  have hvw : v = u * w := by rw [hw, huinv, ← mul_assoc, hu, one_mul]
  have h2 : u * w * u = w⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc u * w * u * w = (u * w) * (u * w) := by group
      _ = 1 := by rw [← hvw]; exact hv
  have hcomm : u * w * u⁻¹ = w⁻¹ := by rw [huinv]; exact h2
  have hpow : w ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one w
  have h3 : u * w ^ j * u⁻¹ = (w⁻¹) ^ j := by rw [← conj_pow, hcomm]
  have e1 : u * (w ^ j)⁻¹ * u⁻¹ = w ^ j := by
    calc u * (w ^ j)⁻¹ * u⁻¹ = (u * w ^ j * u⁻¹)⁻¹ := by group
      _ = ((w⁻¹) ^ j)⁻¹ := by rw [h3]
      _ = w ^ j := by rw [inv_pow, inv_inv]
  have h4 : w ^ j * u * (w ^ j)⁻¹ = w ^ (2 * j) * u := by
    calc w ^ j * u * (w ^ j)⁻¹ = w ^ j * (u * (w ^ j)⁻¹ * u⁻¹) * u := by group
      _ = w ^ j * w ^ j * u := by rw [e1]
      _ = w ^ (2 * j) * u := by rw [← pow_add, two_mul]
  have h5 : w ^ (2 * j) = w⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hpow)
  refine ⟨w ^ j, Subgroup.pow_mem _ (mem_zpowers w) j, ?_⟩
  rw [h4, h5, hvw]
  have : u * w = w⁻¹ * u := by
    calc u * w = (u * w * u⁻¹) * u := by group
      _ = w⁻¹ * u := by rw [hcomm]
  exact this.symm

end Elementary

section Bar0

variable {G : Type} [Group G] {z : G}

theorem toBar_mul {s t : G} (hs : s ∈ Cen z) (ht : t ∈ Cen z) :
    toBar z ⟨s * t, mul_mem hs ht⟩ = toBar z ⟨s, hs⟩ * toBar z ⟨t, ht⟩ := by
  rw [← map_mul]
  rfl

theorem toBar_inv {s : G} (hs : s ∈ Cen z) :
    toBar z ⟨s⁻¹, inv_mem hs⟩ = (toBar z ⟨s, hs⟩)⁻¹ := by
  rw [← map_inv]
  rfl

theorem toBar_pow {s : G} (hs : s ∈ Cen z) (n : ℕ) (hsn : s ^ n ∈ Cen z) :
    toBar z ⟨s ^ n, hsn⟩ = (toBar z ⟨s, hs⟩) ^ n := by
  rw [← map_pow]
  rfl

theorem toBar_conj {k x : G} (hk : k ∈ Cen z) (hx : x ∈ Cen z) :
    toBar z ⟨k * x * k⁻¹, mul_mem (mul_mem hk hx) (inv_mem hk)⟩ =
      toBar z ⟨k, hk⟩ * toBar z ⟨x, hx⟩ * (toBar z ⟨k, hk⟩)⁻¹ := by
  rw [toBar_mul (mul_mem hk hx) (inv_mem hk), toBar_mul hk hx, toBar_inv hk]

end Bar0

section Bar

variable {G : Type} [Group G] [Finite G] {z : G}

theorem odd_orderOf_of_toBar_eq_one {w : G} (hwC : w ∈ Cen z) (h : toBar z ⟨w, hwC⟩ = 1) :
    Odd (orderOf w) := by
  have hker : (⟨w, hwC⟩ : ↥(Cen z)) ∈ (toBar z).ker := h
  have h1 : orderOf (⟨⟨w, hwC⟩, hker⟩ : (toBar z).ker) ∣ Nat.card (toBar z).ker :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
  exact Odd.of_dvd_nat (odd_card_ker_toBar z) h1

end Bar

section Lift

variable {G : Type} [Group G] [Finite G] {z : G} {a : G}

theorem exists_lift_inv {K : Subgroup G} (haC : a ∈ Cen z) (ha2 : a * a = 1)
    (haK : a ∈ normalizer (K : Set G)) {b : CentralizerBar z}
    (hb : b ∈ IVK.Prod3.invCoset (barOf z K) (toBar z ⟨a, haC⟩)) :
    ∃ u ∈ invCoset K a, ∃ huC : u ∈ Cen z, toBar z ⟨u, huC⟩ = b := by
  obtain ⟨⟨kb, hkb, rfl⟩, hb2⟩ := hb
  obtain ⟨k, hkK, hkC, rfl⟩ := Pull.exists_of_mem_barOf hkb
  have hcC : k * a ∈ Cen z := mul_mem hkC haC
  have hcc : (k * a) * (k * a) ∈ K := by
    have e : (k * a) * (k * a) = k * (a * k * a⁻¹) := by
      calc (k * a) * (k * a) = k * (a * k * a⁻¹) * (a * a) := by group
        _ = k * (a * k * a⁻¹) := by rw [ha2, mul_one]
    rw [e]
    exact mul_mem hkK ((Subgroup.mem_normalizer_iff.1 haK k).1 hkK)
  have hccC : (k * a) * (k * a) ∈ Cen z := mul_mem hcC hcC
  have hbc : toBar z ⟨k * a, hcC⟩ = toBar z ⟨k, hkC⟩ * toBar z ⟨a, haC⟩ := toBar_mul hkC haC
  have hb₀ : toBar z ⟨k * a, hcC⟩ * toBar z ⟨k * a, hcC⟩ = 1 := by rw [hbc]; exact hb2
  have hcc1 : toBar z ⟨(k * a) * (k * a), hccC⟩ = 1 := by
    rw [toBar_mul hcC hcC]; exact hb₀
  obtain ⟨j, hj⟩ := odd_orderOf_of_toBar_eq_one hccC hcc1
  set c := k * a with hc
  have hpow : (c * c) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
  have huc : c ^ (2 * j + 1) = ((c * c) ^ j * k) * a := by
    rw [pow_succ, pow_mul, sq, hc]
    group
  have huC : c ^ (2 * j + 1) ∈ Cen z := Subgroup.pow_mem _ hcC _
  refine ⟨c ^ (2 * j + 1), ⟨⟨(c * c) ^ j * k, mul_mem (Subgroup.pow_mem _ hcc j) hkK, huc⟩, ?_⟩, huC, ?_⟩
  · have e : c ^ (2 * j + 1) * c ^ (2 * j + 1) = (c * c) ^ (2 * j + 1) := by
      rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, sq]
    rw [e, hpow]
  · rw [toBar_pow hcC (2 * j + 1) huC, pow_succ, pow_mul, sq, hb₀, one_pow, one_mul, hbc]

end Lift

section Stab

variable {G : Type} [Group G]

@[expose] def stab (K : Subgroup G) (a : G) : Subgroup G where
  carrier := {g | g ∈ normalizer (K : Set G) ∧ g * a * g⁻¹ * a⁻¹ ∈ K}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, ?_⟩
    have e : g * h * a * (g * h)⁻¹ * a⁻¹ =
        (g * (h * a * h⁻¹ * a⁻¹) * g⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hg _).1 hh') hg'
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨inv_mem hg, ?_⟩
    have e : g⁻¹ * a * g⁻¹⁻¹ * a⁻¹ = g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (inv_mem hg) _).1 (inv_mem hg')

theorem K_le_stab {K : Subgroup G} {a : G} (haK : a ∈ normalizer (K : Set G)) : K ≤ stab K a := by
  intro g hg
  refine ⟨Subgroup.le_normalizer hg, ?_⟩
  have h1 : a * g⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 haK _).1 (inv_mem hg)
  have e : g * a * g⁻¹ * a⁻¹ = g * (a * g⁻¹ * a⁻¹) := by group
  rw [e]
  exact mul_mem hg h1

end Stab

section Conj

variable {G : Type} [Group G] [Finite G] {z : G} {a : G}

theorem conjUnder_of_bar {K M : Subgroup G} (hKM : K ≤ M)
    (haK : a ∈ normalizer (K : Set G)) (hMs : M ≤ stab K a) {u₁ u₂ : G}
    (hu₁ : u₁ ∈ invCoset K a) (hu₂ : u₂ ∈ invCoset K a) (hu₁C : u₁ ∈ Cen z) (hu₂C : u₂ ∈ Cen z)
    {gb : CentralizerBar z} (hgb : gb ∈ barOf z M)
    (h : gb * toBar z ⟨u₁, hu₁C⟩ * gb⁻¹ = toBar z ⟨u₂, hu₂C⟩) : IVK.ConjUnder M u₁ u₂ := by
  obtain ⟨g, hgM, hgC, rfl⟩ := Pull.exists_of_mem_barOf hgb
  obtain ⟨⟨k₁, hk₁, hu₁e⟩, hu₁2⟩ := hu₁
  obtain ⟨⟨k₂, hk₂, hu₂e⟩, hu₂2⟩ := hu₂
  have hgs := hMs hgM
  have hvC : g * u₁ * g⁻¹ ∈ Cen z := mul_mem (mul_mem hgC hu₁C) (inv_mem hgC)
  have hv2 : (g * u₁ * g⁻¹) * (g * u₁ * g⁻¹) = 1 := by
    calc (g * u₁ * g⁻¹) * (g * u₁ * g⁻¹) = g * (u₁ * u₁) * g⁻¹ := by group
      _ = 1 := by rw [hu₁2]; group
  obtain ⟨kv, hkv, hvkv⟩ : ∃ kv ∈ K, g * u₁ * g⁻¹ = kv * a := by
    refine ⟨g * k₁ * g⁻¹ * (g * a * g⁻¹ * a⁻¹),
      mul_mem ((Subgroup.mem_normalizer_iff.1 hgs.1 _).1 hk₁) hgs.2, ?_⟩
    rw [hu₁e]
    group
  have hwK : (g * u₁ * g⁻¹)⁻¹ * u₂ ∈ K := by
    have e : (g * u₁ * g⁻¹)⁻¹ * u₂ = a⁻¹ * (kv⁻¹ * k₂) * a := by
      rw [hvkv, hu₂e]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem haK) (kv⁻¹ * k₂)).1
      (mul_mem (inv_mem hkv) hk₂)
    simpa using this
  have himg : toBar z ⟨g * u₁ * g⁻¹, hvC⟩ = toBar z ⟨u₂, hu₂C⟩ := by
    rw [toBar_mul (mul_mem hgC hu₁C) (inv_mem hgC), toBar_mul hgC hu₁C, toBar_inv hgC]
    exact h
  have hwC : (g * u₁ * g⁻¹)⁻¹ * u₂ ∈ Cen z := mul_mem (inv_mem hvC) hu₂C
  have hw1 : toBar z ⟨(g * u₁ * g⁻¹)⁻¹ * u₂, hwC⟩ = 1 := by
    rw [toBar_mul (inv_mem hvC) hu₂C, toBar_inv hvC, himg, inv_mul_cancel]
  obtain ⟨n, hn, hnv⟩ := exists_conj_of_odd hv2 hu₂2 (odd_orderOf_of_toBar_eq_one hwC hw1)
  have hnK : n ∈ K := (Subgroup.zpowers_le.2 hwK) hn
  refine ⟨n * g, M.mul_mem (hKM hnK) hgM, ?_⟩
  calc n * g * u₁ * (n * g)⁻¹ = n * (g * u₁ * g⁻¹) * n⁻¹ := by group
    _ = u₂ := hnv

end Conj

section Normalizer

variable {G : Type} [Group G]

theorem mul_self_of_orderOf_two {a : G} (h : orderOf a = 2) : a * a = 1 := by
  rw [← sq, ← h]
  exact pow_orderOf_eq_one a

theorem mem_normalizer_sup {K₁ K₂ : Subgroup G} {g : G} (h₁ : g ∈ normalizer (K₁ : Set G))
    (h₂ : g ∈ normalizer (K₂ : Set G)) : g ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_sup, h₁, h₂]

end Normalizer

end Cls

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {a x : G}

theorem l53_classes (hII : II4_4_4_center) (_h2A7 : IVK.Lifted.II4_2A7)
    (hctr : Ctr5 G z S K₁ K₂ a x) (_h52 : L52 S K₁ K₂) (haC : a ∈ Cen z)
    {Y A : Subgroup (CentralizerBar z)} {r : ℕ} (hD : AbsData z S K₁ K₂ a haC Y A r) :
    (∃ b ∈ invCoset (K₁ ⊔ K₂) a, ¬ IVK.ConjUnder (K₁ ⊔ K₂) a b ∧
      ∀ u ∈ invCoset (K₁ ⊔ K₂) a, IVK.ConjUnder (K₁ ⊔ K₂) a u ∨ IVK.ConjUnder (K₁ ⊔ K₂) b u) ∧
    (Pz S z ≠ pull z S Y → ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ∀ v ∈ invCoset (K₁ ⊔ K₂) a,
      IVK.ConjUnder (K₁ ⊔ K₂ ⊔ pull z S Y) u v) ∧
    IVK.ConjUnder (K₁ ⊔ K₂) a (a * z) := by
  have hstd : Std4 G z S K₁ K₂ := hctr.cfg.std
  have hM := m4_of_std hII hstd
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z) := hstd.sylow
  have hSC : S ≤ Cen z := hS.le
  have hK₁ : IsPCompIn 2 (Cen z) K₁ := hstd.comp_isPCompIn (Or.inl rfl)
  have hKC₁ : K₁ ≤ Cen z := hM.K₁_le
  have hKC₂ : K₂ ≤ Cen z := hM.K₂_le
  have hKC : K₁ ⊔ K₂ ≤ Cen z := sup_le hKC₁ hKC₂
  have haS : a ∈ S := hctr.elt.mem
  have ha2 : a * a = 1 := Cls.mul_self_of_orderOf_two hctr.elt.inv
  have haK₁ : a ∈ normalizer (K₁ : Set G) := hctr.elt.f₁.1
  have haK₂ : a ∈ normalizer (K₂ : Set G) := hctr.elt.f₂.1
  have haK : a ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := Cls.mem_normalizer_sup haK₁ haK₂
  have hz2 : z * z = 1 := Cls.mul_self_of_orderOf_two hstd.orderOf_z
  have hzK : z ∈ K₁ ⊔ K₂ := mem_sup_left (hM.z_mem_comp (Or.inl rfl))
  have hzC : z ∈ Cen z := mem_Cen_self z
  have hYT : Y ≤ barOf z S := hD.Y_le.trans inf_le_left
  have hbarK : barOf z (K₁ ⊔ K₂) = barOf z K₁ ⊔ barOf z K₂ := Pull.barOf_sup hKC₁ hKC₂
  have img : ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ∃ huC : u ∈ Cen z,
      toBar z ⟨u, huC⟩ ∈ IVK.Prod3.invCoset (barOf z (K₁ ⊔ K₂)) (toBar z ⟨a, haC⟩) := by
    rintro u ⟨⟨k, hk, rfl⟩, hu2⟩
    have hkC : k ∈ Cen z := hKC hk
    refine ⟨mul_mem hkC haC, ⟨toBar z ⟨k, hkC⟩, Pull.mem_barOf hk hkC, ?_⟩, ?_⟩
    · exact Cls.toBar_mul hkC haC
    · have h1 : toBar z ⟨k * a * (k * a), mul_mem (mul_mem hkC haC) (mul_mem hkC haC)⟩ = 1 := by
        have : (⟨k * a * (k * a), mul_mem (mul_mem hkC haC) (mul_mem hkC haC)⟩ : ↥(Cen z)) = 1 :=
          Subtype.ext hu2
        rw [this]
        exact map_one _
      rw [Cls.toBar_mul (mul_mem hkC haC) (mul_mem hkC haC)] at h1
      exact h1
  have haI : a ∈ invCoset (K₁ ⊔ K₂) a := ⟨⟨1, one_mem _, by simp⟩, ha2⟩
  have hKs : K₁ ⊔ K₂ ≤ Cls.stab (K₁ ⊔ K₂) a := Cls.K_le_stab haK
  have hYs : pull z S Y ≤ Cls.stab (K₁ ⊔ K₂) a := by
    intro y hy
    obtain ⟨hyS, hyC, hyY⟩ := Pull.mem_pull.1 hy
    have hyN₁ : y ∈ normalizer (K₁ : Set G) := by
      have : y ∈ S1 S K₁ := by
        rw [← Lat.pull_T1 hK₁ hS]
        exact Pull.pull_mono hD.Y_le hy
      exact this.2
    have hyN₂ : y ∈ normalizer (K₂ : Set G) := normalizer_other hM hstd.ne hyC hyN₁
    refine ⟨Cls.mem_normalizer_sup hyN₁ hyN₂, ?_⟩
    have hcomm : ⁅y, a⁆ ∈ K₁ ⊔ K₂ := by
      have hya : ⁅y, a⁆ ∈ S := by
        rw [commutatorElement_def]
        exact S.mul_mem (S.mul_mem (S.mul_mem hyS haS) (S.inv_mem hyS)) (S.inv_mem haS)
      refine (Lat.mem_pull_sup_iff hII hstd hya).1 ?_
      refine (Pull.comm_mem_pull hSC hyS haS).2 ?_
      exact (hD.Ce.1 _ hyY _ hD.Cd.1).2
    simpa [commutatorElement_def] using hcomm
  obtain ⟨⟨bh, hbh, hnb, hall⟩, hfus, hconj⟩ := hD.Cg
  rw [← hbarK] at hbh hnb hall hfus hconj
  obtain ⟨b, hb, hbC, hbimg⟩ := Cls.exists_lift_inv haC ha2 haK hbh
  refine ⟨⟨b, hb, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨k, hk, hkab⟩
    have hkC : k ∈ Cen z := hKC hk
    apply hnb
    refine ⟨toBar z ⟨k, hkC⟩, Pull.mem_barOf hk hkC, ?_⟩
    have e : (⟨k * a * k⁻¹, mul_mem (mul_mem hkC haC) (inv_mem hkC)⟩ : ↥(Cen z)) = ⟨b, hbC⟩ :=
      Subtype.ext hkab
    rw [← Cls.toBar_conj hkC haC, e]
    exact hbimg
  · intro u hu
    obtain ⟨huC, hu'⟩ := img u hu
    rcases hall _ hu' with ⟨gb, hgb, h⟩ | ⟨gb, hgb, h⟩
    · exact Or.inl (Cls.conjUnder_of_bar le_rfl haK hKs haI hu haC huC hgb h)
    · refine Or.inr (Cls.conjUnder_of_bar le_rfl haK hKs hb hu hbC huC hgb ?_)
      rw [hbimg]
      exact h
  · intro hne u hu v hv
    have hP : IVK.Prod3.P (barOf z S) (barOf z K₁) (barOf z K₂) ≠ Y := by
      intro heq
      exact hne (by rw [← Lat.pull_P hII hstd, heq])
    obtain ⟨huC, hu'⟩ := img u hu
    obtain ⟨hvC, hv'⟩ := img v hv
    obtain ⟨gb, hgb, h⟩ := hfus hP _ hu' _ hv'
    have hbarM : barOf z (K₁ ⊔ K₂ ⊔ pull z S Y) = barOf z (K₁ ⊔ K₂) ⊔ Y := by
      rw [Pull.barOf_sup hKC (Pull.pull_le.trans hSC), Pull.barOf_pull hYT]
    rw [← hbarM] at hgb
    exact Cls.conjUnder_of_bar le_sup_left haK (sup_le hKs hYs) hu hv huC hvC hgb h
  · obtain ⟨gb, hgb, h⟩ := hconj
    have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.1 haC
    have hazI : a * z ∈ invCoset (K₁ ⊔ K₂) a := by
      refine ⟨⟨z, hzK, haz⟩, ?_⟩
      calc a * z * (a * z) = a * (z * a) * z := by group
        _ = a * (a * z) * z := by rw [haz]
        _ = (a * a) * (z * z) := by group
        _ = 1 := by rw [ha2, hz2, one_mul]
    refine Cls.conjUnder_of_bar le_rfl haK hKs haI hazI haC (mul_mem haC hzC) hgb ?_
    rw [Cls.toBar_mul haC hzC]
    exact h

end Main

end CFSG.GH74.GLS.IVK.Lifted32
