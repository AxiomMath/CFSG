module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Tr

public section

namespace CFSG.OddStandard.ChengHeld.Excl2

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.OddStandard.ChengHeld.ChartShape (cj_mul cj_inv cj_cj cj_of_commute cm_eq_one_iff)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

@[expose] def mSub {d : Datum A} (V : Subgroup G) (f : ↥(normalizer (V : Set G)) →*
    Multiplicative (ZMod 2)) : Subgroup G :=
  d.X ⊓ f.ker.map (normalizer (V : Set G)).subtype

theorem mSub_le_X {d : Datum A} (V : Subgroup G)
    (f : ↥(normalizer (V : Set G)) →* Multiplicative (ZMod 2)) : mSub (d := d) V f ≤ d.X :=
  inf_le_left

namespace Cfg

variable {d : Datum A} (K : Cfg d 0)

include K

theorem mem_mSub_iff (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {x : G} :
    x ∈ mSub (d := d) K.c.V f ↔ x ∈ d.X ∧ ext1 f x = 1 := by
  have hXH : d.X ≤ normalizer (K.c.V : Set G) := K.X_le_normalizer_V
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨hx, by show ext1 f (y : G) = 1; rw [ext1_apply f y.2]; exact hy⟩
  · rintro ⟨hx, h1⟩
    refine ⟨hx, ⟨x, hXH hx⟩, ?_, rfl⟩
    rw [ext1_apply f (hXH hx)] at h1
    exact h1

theorem not_mem_mSub (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {z : G}
    (hfz : ext1 f z = Multiplicative.ofAdd 1) : z ∉ mSub (d := d) K.c.V f := fun h =>
  zmod_two_ofAdd_one_ne_one (hfz.symm.trans ((K.mem_mSub_iff f).1 h).2)

theorem relIndex_mSub (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {z : G}
    (hzX : z ∈ d.X) (hfz : ext1 f z = Multiplicative.ofAdd 1) :
    (mSub (d := d) K.c.V f).relIndex d.X = 2 := by
  have hXH : d.X ≤ normalizer (K.c.V : Set G) := K.X_le_normalizer_V
  let fX : ↥d.X →* Multiplicative (ZMod 2) := f.comp (Subgroup.inclusion hXH)
  have hker : (mSub (d := d) K.c.V f).subgroupOf d.X = fX.ker := by
    ext x
    rw [mem_subgroupOf, K.mem_mSub_iff f, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, h1⟩
      rw [ext1_apply f (hXH x.2)] at h1
      exact h1
    · intro h1
      refine ⟨x.2, ?_⟩
      rw [ext1_apply f (hXH x.2)]
      exact h1
  have hrange : fX.range = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    by_cases ha : a = 1
    · rw [ha]; exact one_mem _
    · refine ⟨⟨z, hzX⟩, ?_⟩
      rw [zmod_two_eq_ofAdd_one ha]
      show f ⟨z, hXH hzX⟩ = _
      rw [← ext1_apply f (hXH hzX)]
      exact hfz
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, hrange, Subgroup.card_top]
  simp [Nat.card_eq_fintype_card]

theorem isConj_q_of_mem_mSub (hqπ : IsConj d.q K.c.pi) (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t)
    (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {z : G}
    (hzP : z ∈ d.X ⊓ centralizer (K.c.V : Set G)) (hzW : z ∉ K.c.W)
    (hfz : ext1 f z = Multiplicative.ofAdd 1) {u : G} (hu : u ∈ mSub (d := d) K.c.V f)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) : IsConj d.q u := by
  obtain ⟨huX, hfu⟩ := (K.mem_mSub_iff f).1 hu
  have hSH : d.S ≤ normalizer (K.c.V : Set G) := K.c.S_le_normalizer_V K.hα K.h K.hP K.hQ
  have hXH : d.X ≤ normalizer (K.c.V : Set G) := K.X_le_normalizer_V
  by_cases huS : u ∈ d.S
  · by_cases huq : u = d.q
    · rw [huq]
    · obtain ⟨a, -, ha⟩ := K.c.involution_conj_pi K.h K.hc huS hu2 hu1 huq
      exact hqπ.trans (isConj_of_cj_eq ha).symm
  · have huP : u ∉ centralizer (K.c.V : Set G) := fun huP =>
      huS ((K.ext1_P_iff hQt f hzP hzW hfz ⟨huX, huP⟩).1 hfu).1
    have huH : u ∈ normalizer (K.c.V : Set G) := hXH huX
    set ρ := K.c.V.normalizerMonoidHom with hρ
    have hsurj : Function.Surjective ρ :=
      K.c.surjective_normalizerMonoidHom_of_isConj K.hα K.h K.hP K.hQ K.hS2 K.hc K.g_norm
        K.g_act hqπ
    have hV2 : ∀ v : ↥K.c.V, v * v = 1 := fun v => Subtype.ext (K.sf.V_sq v v.2)
    have hμS : K.c.mu ∈ d.S := K.c.mem.2.2.1
    have hμH : K.c.mu ∈ normalizer (K.c.V : Set G) := hSH hμS
    have hμ2 : K.c.mu * K.c.mu = 1 := by rw [← pow_two]; exact K.c.frame.mu2
    have hμP : K.c.mu ∉ centralizer (K.c.V : Set G) := fun hμP => by
      have hpiV : K.c.pi ∈ K.c.V := subset_closure (by simp)
      have h1 := mem_centralizer_iff.1 hμP K.c.pi hpiV
      have h2 : cj K.c.pi K.c.mu = K.c.pi := cj_of_commute h1
      rw [K.c.frame.pi_mu] at h2
      exact K.c.shape_t_sq_ne_one (by simpa using h2)
    have hord : ∀ {y : G} (hy : y ∈ normalizer (K.c.V : Set G)), y * y = 1 →
        y ∉ centralizer (K.c.V : Set G) → orderOf (ρ ⟨y, hy⟩) = 2 := by
      intro y hy hy2 hyP
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, ← map_mul]
        have : (⟨y, hy⟩ : ↥(normalizer (K.c.V : Set G))) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
        rw [this, map_one]
      · intro h1
        have hker : (⟨y, hy⟩ : ↥(normalizer (K.c.V : Set G))) ∈ ρ.ker := h1
        rw [hρ, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf] at hker
        exact hyP hker
    obtain ⟨c, hc⟩ := isConj_iff.1
      (isConj_of_orderOf_two_mulAut K.sf.card_V hV2 (hord huH hu2 huP) (hord hμH hμ2 hμP))
    obtain ⟨h, hh⟩ := hsurj c
    have hpP : (h : G) * u * (h : G)⁻¹ * K.c.mu⁻¹ ∈ centralizer (K.c.V : Set G) := by
      have hw : ρ (h * ⟨u, huH⟩ * h⁻¹ * (⟨K.c.mu, hμH⟩ : ↥(normalizer (K.c.V : Set G)))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hh, ← hc]
        group
      have hker : (h * ⟨u, huH⟩ * h⁻¹ * (⟨K.c.mu, hμH⟩ : ↥(normalizer (K.c.V : Set G)))⁻¹) ∈
          ρ.ker := hw
      rw [hρ, Subgroup.normalizerMonoidHom_ker, mem_subgroupOf] at hker
      simpa using hker
    have hcj : ext1 f ((h : G) * u * (h : G)⁻¹) = 1 := by
      have := ext1_cj f huH (inv_mem h.2)
      have e : cj u (h : G)⁻¹ = (h : G) * u * (h : G)⁻¹ := by simp [cj]
      rw [e] at this
      rw [this]
      exact hfu
    set u' := (h : G) * u * (h : G)⁻¹ with hu'
    have hμX : K.c.mu ∈ d.X := d.S_le_X hμS
    have hμC : ∀ x ∈ centralizer (K.c.V : Set G), K.c.mu * x * K.c.mu⁻¹ ∈
        centralizer (K.c.V : Set G) := fun x hx =>
      conj_mem_centralizer_of_normalizer (fun v => mem_normalizer_iff.1 hμH v) hx
    have hμP' : ∀ x ∈ d.X ⊓ centralizer (K.c.V : Set G), K.c.mu * x * K.c.mu⁻¹ ∈
        d.X ⊓ centralizer (K.c.V : Set G) := fun x hx =>
      ⟨d.X.mul_mem (d.X.mul_mem hμX hx.1) (d.X.inv_mem hμX), hμC x hx.2⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsyl := isSylowOf_sup_zpowers K.isSylowOf_P hμC hμP' hμ2 hμP
    have hu'D : u' ∈ centralizer (K.c.V : Set G) ⊔ zpowers K.c.mu := by
      have e : u' = (u' * K.c.mu⁻¹) * K.c.mu := by group
      rw [e]
      exact mul_mem (mem_sup_left hpP) (mem_sup_right (mem_zpowers _))
    have hu'2 : u' * u' = 1 := by
      calc u' * u' = (h : G) * (u * u) * (h : G)⁻¹ := by rw [hu']; group
        _ = 1 := by rw [hu2]; group
    have hp : IsPGroup 2 (zpowers u') :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, pow_one]
        refine orderOf_eq_prime (by rw [pow_two]; exact hu'2) fun h1 => hu1 ?_
        have : u = (h : G)⁻¹ * u' * h := by rw [hu']; group
        rw [this, h1]
        group)
    obtain ⟨P'', hP'', hu'P''⟩ := exists_isSylowOf_of_le hp (zpowers_le.2 hu'D)
    obtain ⟨e, heD, he⟩ := hsyl.exists_mem_conj hP''
    have hu''P : e⁻¹ * u' * e ∈ (d.X ⊓ centralizer (K.c.V : Set G)) ⊔ zpowers K.c.mu :=
      (he u').1 (hu'P'' (mem_zpowers u'))
    have heN : e ∈ normalizer (K.c.V : Set G) :=
      (sup_le (centralizer_le_normalizer _) (zpowers_le.2 hμH)) heD
    have hu'H : u' ∈ normalizer (K.c.V : Set G) := mul_mem (mul_mem h.2 huH) (inv_mem h.2)
    have hfu'' : ext1 f (e⁻¹ * u' * e) = 1 := by
      have := ext1_cj f hu'H heN
      rw [show cj u' e = e⁻¹ * u' * e from rfl] at this
      rw [this, hu', ← show cj u (h : G)⁻¹ = (h : G) * u * (h : G)⁻¹ by simp [cj],
        ext1_cj f huH (inv_mem h.2)]
      exact hfu
    have hμN' : K.c.mu ∈ normalizer
        ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) :=
      mem_normalizer_fintype fun x hx => hμP' x hx
    have hcoe : (((d.X ⊓ centralizer (K.c.V : Set G)) ⊔ zpowers K.c.mu : Subgroup G) : Set G) =
        ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) * (zpowers K.c.mu : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ (zpowers K.c.mu) (zpowers_le.2 hμN')
    have hu''S : e⁻¹ * u' * e ∈ d.S := by
      have hmem : e⁻¹ * u' * e ∈
          ((d.X ⊓ centralizer (K.c.V : Set G) : Subgroup G) : Set G) * (zpowers K.c.mu : Set G) :=
        by rw [← hcoe]; exact hu''P
      obtain ⟨p, hp, y, hy, hpy⟩ := hmem
      have hpy' : p * y = e⁻¹ * u' * e := hpy
      have hyS : y ∈ d.S := (zpowers_le.2 hμS) hy
      have hpH : p ∈ normalizer (K.c.V : Set G) := (centralizer_le_normalizer _) hp.2
      have hfp : ext1 f p = 1 := by
        have e1 : p = (e⁻¹ * u' * e) * y⁻¹ := by rw [← hpy']; group
        rw [e1, ext1_mul f (mul_mem (mul_mem (inv_mem heN) hu'H) heN) (inv_mem (hSH hyS)),
          hfu'', ext1_inv f (hSH hyS), K.ext1_S f _ hyS, inv_one, one_mul]
      rw [← hpy']
      exact mul_mem ((K.ext1_P_iff hQt f hzP hzW hfz hp).1 hfp).1 hyS
    have hu''2 : (e⁻¹ * u' * e) * (e⁻¹ * u' * e) = 1 := by
      calc (e⁻¹ * u' * e) * (e⁻¹ * u' * e) = e⁻¹ * (u' * u') * e := by group
        _ = 1 := by rw [hu'2]; group
    have hconj : IsConj u (e⁻¹ * u' * e) :=
      isConj_of_cj_eq (s := (h : G)⁻¹ * e) (by rw [hu']; simp only [cj]; group)
    by_cases hq : e⁻¹ * u' * e = d.q
    · rw [hq] at hconj
      exact hconj.symm
    have hu''1 : e⁻¹ * u' * e ≠ 1 := fun h1 => hu1 (by
      have : u = ((h : G)⁻¹ * e) * (e⁻¹ * u' * e) * ((h : G)⁻¹ * e)⁻¹ := by rw [hu']; group
      rw [this, h1]
      group)
    obtain ⟨a, -, ha⟩ := K.c.involution_conj_pi K.h K.hc hu''S hu''2 hu''1 hq
    exact (hqπ.trans (isConj_of_cj_eq ha).symm).trans hconj.symm

theorem isConj_q_z (hqπ : IsConj d.q K.c.pi) (hQt : ∀ u ∈ d.Q, u ∈ zpowers K.c.t)
    (f : ↥(normalizer (K.c.V : Set G)) →* Multiplicative (ZMod 2)) {z : G}
    (hzP : z ∈ d.X ⊓ centralizer (K.c.V : Set G)) (hzW : z ∉ K.c.W) (hz2 : z * z = 1)
    (hfz : ext1 f z = Multiplicative.ofAdd 1) : IsConj d.q z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzX : z ∈ d.X := hzP.1
  have hmax := K.relIndex_mSub f hzX hfz
  have hsylX := K.c.X_sylow_G_of_facts K.hα K.h K.hP K.hQ
  have hTidx : ¬ 2 ∣ d.X.index := by
    have := (CFSG.ABGLocalTools.isSylowOf_iff.1 hsylX).2.2
    rwa [Subgroup.relIndex_top_right] at this
  have := K.h.setting.simple
  obtain ⟨x, hx⟩ := CFSG.OddStandard.Seitz77.exists_conj_mem_of_index_two_of_mul_self
    K.h.setting.nonab d.X_sylow.isPGroup hTidx (mSub_le_X K.c.V f) hmax hzX
    (K.not_mem_mSub f hfz) hz2
  have hw2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [hz2]; group
  have hw1 : x⁻¹ * z * x ≠ 1 := fun h1 => hzW (by
    have : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [this, h1]
    simp)
  have hq := K.isConj_q_of_mem_mSub hqπ hQt f hzP hzW hfz hx hw2 hw1
  exact hq.trans (isConj_of_cj_eq (a := z) (s := x) rfl).symm

end Cfg

end CFSG.OddStandard.ChengHeld.Excl2
