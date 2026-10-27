module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma57
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step2a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement Pointwise

namespace Seven

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_inf_conjugate {B : Subgroup X} {y : X}
    (hy2 : y ^ 2 ∈ normalizer (B : Set X)) :
    y ∈ normalizer ((B ⊓ conjugate B y : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro w
  rw [mem_inf, mem_inf, mem_conjugate_iff, mem_conjugate_iff,
    show y * (y * w * y⁻¹) * y⁻¹ = y ^ 2 * w * (y ^ 2)⁻¹ by rw [pow_two]; group]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, (mem_normalizer_iff.mp hy2 w).mp h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(mem_normalizer_iff.mp hy2 w).mpr h2, h1⟩

theorem normalizer_le_normalizer_layerIn_centralizer (B : Subgroup X) :
    normalizer (B : Set X) ≤ normalizer (layerIn (centralizer (B : Set X)) : Set X) := by
  have : (pLayer ↥(centralizer (B : Set X)) 2).Characteristic :=
    CatalogueBPrimeJoin.pLayer_characteristic
  intro g hg
  refine UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ ?_
  rw [mem_normalizer_iff]
  intro c
  have key : ∀ g' ∈ normalizer (B : Set X), ∀ c' ∈ centralizer (B : Set X),
      g' * c' * g'⁻¹ ∈ centralizer (B : Set X) := by
    intro g' hg' c' hc'
    rw [mem_centralizer_iff]
    intro β hβ
    have h1 : g'⁻¹ * β * g' ∈ B := by
      have := (mem_normalizer_iff.mp (inv_mem hg') β).mp hβ
      rwa [inv_inv] at this
    have h2 := mem_centralizer_iff.mp hc' _ h1
    calc β * (g' * c' * g'⁻¹) = g' * ((g'⁻¹ * β * g') * c') * g'⁻¹ := by group
      _ = g' * (c' * (g'⁻¹ * β * g')) * g'⁻¹ := by rw [h2]
      _ = g' * c' * g'⁻¹ * β := by group
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this

omit [Finite X] in
theorem eq_one_or_of_mem_zpowers {a w : X} (ha : orderOf a = 2) (hw : w ∈ zpowers a) :
    w = 1 ∨ w = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← ha, pow_orderOf_eq_one]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left; rw [show m + m = 2 * m by ring, zpow_mul, ha2, one_zpow]
  · right; rw [zpow_add_one, zpow_mul, ha2, one_zpow, one_mul]

namespace Data

variable (d : Data X)

theorem a_mul_a : d.h.a * d.h.a = 1 := by
  rw [← pow_two, ← d.h.orderOf_a, pow_orderOf_eq_one]

theorem a_ne_one : d.h.a ≠ 1 := by
  intro h1
  have := d.h.orderOf_a
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_ne_one : d.z ≠ 1 := by
  intro h1
  have := d.hz2
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_mul_z : d.z * d.z = 1 := by
  rw [← pow_two, ← d.hz2, pow_orderOf_eq_one]

theorem z_mem_S : d.z ∈ d.h.S := d.h.D_le_S d.hzD

theorem z_not_mem_P : d.z ∉ d.h.P := by
  intro hzP
  have : d.z ∈ d.h.D ⊓ d.h.P := mem_inf.mpr ⟨d.hzD, hzP⟩
  rw [d.hDP, mem_bot] at this
  exact d.z_ne_one this

theorem y_mem_S : d.y ∈ d.h.S := (mem_inf.mp d.hyP).1

theorem T_le_normalizer_B : d.h.T ≤ normalizer (d.h.B : Set X) :=
  fun _ hw => (mem_inf.mp (mem_inf.mp hw).1).2

theorem y_mem_normalizer_B0 : d.y ∈ normalizer (B0 d.h d.y : Set X) :=
  mem_normalizer_inf_conjugate (d.T_le_normalizer_B d.hy2)

theorem normalizer_B0_le : normalizer (B0 d.h d.y : Set X) ≤ normalizer (Lay d.h d.y : Set X) :=
  normalizer_le_normalizer_layerIn_centralizer _

theorem y_not_mem_normalizer_B : d.y ∉ normalizer (d.h.B : Set X) := fun hyN =>
  d.hyT (mem_inf.mpr ⟨mem_inf.mpr ⟨d.y_mem_S, hyN⟩, d.hyP⟩)

theorem B_inf_zpowers_a : d.h.B ⊓ zpowers d.h.a = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwB, hwa⟩ := mem_inf.mp hw
  rcases eq_one_or_of_mem_zpowers d.h.orderOf_a hwa with h1 | h1
  · exact mem_bot.mpr h1
  · exact absurd (h1 ▸ hwB) d.h.a_not_mem_B

theorem y_mem_normalizer_T : d.y ∈ normalizer (d.h.T : Set X) := by
  have hP : d.y ∈ normalizer (d.h.P : Set X) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · exact d.h.conj_mem_P d.y_mem_S
    · intro hw
      have := d.h.conj_mem_P (inv_mem d.y_mem_S) hw
      rwa [show d.y⁻¹ * (d.y * w * d.y⁻¹) * d.y⁻¹⁻¹ = w by group] at this
  exact Six.mem_normalizer_inf d.hyQ hP

theorem relIndex_B0 : (B0 d.h d.y).relIndex d.h.B = 2 :=
  d.h.relIndex_inf_conjugate ⟨d.hT, d.B_inf_zpowers_a, fun _ hb => d.h.comm_a_B hb⟩
    d.y_mem_normalizer_T d.y_not_mem_normalizer_B

theorem mem_B0_or {β γ : X} (hβ : β ∈ d.h.B) (hβ0 : β ∉ B0 d.h d.y) (hγ : γ ∈ d.h.B) :
    γ ∈ B0 d.h d.y ∨ β⁻¹ * γ ∈ B0 d.h d.y := by
  have hidx : ((B0 d.h d.y).subgroupOf d.h.B).index = 2 := d.relIndex_B0
  have h1 := (mul_mem_iff_of_index_two hidx (a := (⟨β, hβ⟩ : d.h.B)⁻¹) (b := ⟨γ, hγ⟩))
  simp only [mem_subgroupOf, coe_mul, coe_inv, inv_mem_iff] at h1
  by_cases hγ0 : γ ∈ B0 d.h d.y
  · exact Or.inl hγ0
  · right
    exact h1.mpr ⟨fun h => absurd h hβ0, fun h => absurd h hγ0⟩

theorem y_mem_normalizer_L : d.y ∈ normalizer (Lay d.h d.y : Set X) :=
  d.normalizer_B0_le d.y_mem_normalizer_B0

theorem L_le_centralizer : Lay d.h d.y ≤ centralizer (B0 d.h d.y : Set X) := map_subtype_le _

theorem commutator_mem_L {β : X} (hβ : β ∈ Lay d.h d.y) : ⁅β, d.y⁆ ∈ Lay d.h d.y := by
  rw [commutatorElement_def, show β * d.y * β⁻¹ * d.y⁻¹ = β * (d.y * β⁻¹ * d.y⁻¹) by group]
  exact mul_mem hβ ((mem_normalizer_iff.mp d.y_mem_normalizer_L _).mp (inv_mem hβ))

theorem commutator_ne_one {β : X} (hβ : β ∈ d.h.B) (hβ0 : β ∉ B0 d.h d.y) :
    ⁅β, d.y⁆ ≠ 1 := by
  intro h1
  have hc : β * d.y = d.y * β := commutatorElement_eq_one_iff_mul_comm.mp h1
  apply d.y_not_mem_normalizer_B
  have key : ∀ γ ∈ d.h.B, d.y * γ * d.y⁻¹ ∈ d.h.B := by
    intro γ hγ
    rcases d.mem_B0_or hβ hβ0 hγ with h0 | h0
    · exact (mem_inf.mp ((mem_normalizer_iff.mp d.y_mem_normalizer_B0 _).mp h0)).1
    · have h2 := (mem_inf.mp ((mem_normalizer_iff.mp d.y_mem_normalizer_B0 _).mp h0)).1
      have h3 : d.y * γ * d.y⁻¹ = β * (d.y * (β⁻¹ * γ) * d.y⁻¹) := by
        calc d.y * γ * d.y⁻¹ = (d.y * β * d.y⁻¹) * (d.y * (β⁻¹ * γ) * d.y⁻¹) := by group
          _ = β * (d.y * (β⁻¹ * γ) * d.y⁻¹) := by rw [← hc, mul_inv_cancel_right]
      rw [h3]
      exact mul_mem hβ h2
  have key' : ∀ γ ∈ d.h.B, d.y⁻¹ * γ * d.y ∈ d.h.B := by
    intro γ hγ
    have hinj : Function.Injective (fun w : d.h.B => (⟨d.y * w * d.y⁻¹, key w w.2⟩ : d.h.B)) := by
      intro u v huv
      have := congrArg Subtype.val huv
      simp only at this
      exact Subtype.ext (by simpa using this)
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨γ, hγ⟩
    have hw' : d.y * w * d.y⁻¹ = γ := congrArg Subtype.val hw
    rw [← hw', show d.y⁻¹ * (d.y * w * d.y⁻¹) * d.y = w by group]
    exact w.2
  exact mem_normalizer_of_conj_mem key key'

section Fusion

variable (hNS : normalizer (d.h.S : Set X) ≤ centralizer ({d.h.a} : Set X))
include hNS

theorem sylow_S : ∃ R : Sylow 2 X, (R : Subgroup X) = d.h.S :=
  exists_sylow_of_normalizer_le d.hSa hNS

theorem conj_a_eq {g : X} (hg : ∀ t ∈ d.h.S, t * (g⁻¹ * d.h.a * g) = (g⁻¹ * d.h.a * g) * t) :
    g⁻¹ * d.h.a * g = d.h.a := by
  obtain ⟨n, hn, hn'⟩ := exists_normalizer_conj_of_central (d.sylow_S hNS)
    (fun t ht => d.h.comm_a ht) hg
  rw [hn', mul_assoc, ← mem_centralizer_singleton_iff.mp (hNS hn), inv_mul_cancel_left]

theorem not_conj_a_z (g : X) : g⁻¹ * d.h.a * g ≠ d.z := by
  intro hg
  have h1 := d.conj_a_eq hNS (by rw [hg]; exact d.hzS)
  rw [hg] at h1
  exact d.z_not_mem_P (h1 ▸ d.h.a_mem_P)

theorem a_not_mem_L : d.h.a ∉ Lay d.h d.y := by
  intro haL
  obtain ⟨r, -, -, hr⟩ := d.hconj 1 (one_mem _) (mul_one 1) (by rw [mul_one]; exact haL)
  rw [mul_one] at hr
  exact d.not_conj_a_z hNS r hr

end Fusion

structure Case2 (b : X) : Prop where
  hb2 : orderOf b = 2
  hbx : d.h.x⁻¹ * b * d.h.x = d.h.a * b
  hU2 : d.h.upperP 2 = closure {d.h.a, b}
  hbB0 : b ∈ B0 d.h d.y
  hyb : d.y * b = b * d.y
  hcomm : ⁅d.h.B, zpowers d.y⁆ ≤ closure {d.h.a, b}
  hidx : ((centralizer ({b} : Set X)).subgroupOf d.h.S).index = 2

theorem step5 (hNS : normalizer (d.h.S : Set X) ≤ centralizer ({d.h.a} : Set X)) :
    ∃ b : X, d.Case2 b := by
  rcases d.h61 with h1 | ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx⟩
  · exfalso
    obtain ⟨β, hβB, hβL, hβ0⟩ := d.hBL
    have hc : ⁅β, d.y⁆ ∈ zpowers d.h.a := h1 ▸ commutator_mem_commutator hβB (mem_zpowers d.y)
    rcases eq_one_or_of_mem_zpowers d.h.orderOf_a hc with h3 | h3
    · exact d.commutator_ne_one hβB hβ0 h3
    · exact d.a_not_mem_L hNS (h3 ▸ d.commutator_mem_L hβL)
  · exact ⟨b, hb2, hbx, hU2, hbB0, hyb, hcomm, hidx⟩

variable {d} {b : X}

theorem Case2.b_mem_B (hb : d.Case2 b) : b ∈ d.h.B := (mem_inf.mp hb.hbB0).1

theorem Case2.b_mem_S (hb : d.Case2 b) : b ∈ d.h.S := d.h.B_le_S hb.b_mem_B

theorem Case2.b_mem_P (hb : d.Case2 b) : b ∈ d.h.P := d.h.B_le_P hb.b_mem_B

theorem Case2.b_mul_b (hb : d.Case2 b) : b * b = 1 := by
  rw [← pow_two, ← hb.hb2, pow_orderOf_eq_one]

theorem Case2.ba (hb : d.Case2 b) : b * d.h.a = d.h.a * b := d.h.comm_a hb.b_mem_S

theorem Case2.b_ne_one (hb : d.Case2 b) : b ≠ 1 := by
  intro h1
  have := hb.hb2
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Case2.b_not_mem_L (hb : d.Case2 b) : b ∉ Lay d.h d.y := by
  intro hbL
  have : b ∈ B0 d.h d.y ⊓ Lay d.h d.y := mem_inf.mpr ⟨hb.hbB0, hbL⟩
  rw [d.hB0L, mem_bot] at this
  exact hb.b_ne_one this

theorem Case2.commutator_eq (hNS : normalizer (d.h.S : Set X) ≤ centralizer ({d.h.a} : Set X))
    (hb : d.Case2 b) {β : X} (hβB : β ∈ d.h.B) (hβL : β ∈ Lay d.h d.y)
    (hβ0 : β ∉ B0 d.h d.y) : ⁅β, d.y⁆ = d.h.a * b := by
  have hc := hb.hcomm (commutator_mem_commutator hβB (mem_zpowers d.y))
  rcases Six.mem_closure_pair_cases d.a_mul_a hb.b_mul_b hb.ba hc with h1 | h1 | h1 | h1
  · exact absurd h1 (d.commutator_ne_one hβB hβ0)
  · exact absurd (h1 ▸ d.commutator_mem_L hβL) (d.a_not_mem_L hNS)
  · exact absurd (h1 ▸ d.commutator_mem_L hβL) hb.b_not_mem_L
  · exact h1

theorem Case2.ab_mem_L (hNS : normalizer (d.h.S : Set X) ≤ centralizer ({d.h.a} : Set X))
    (hb : d.Case2 b) : d.h.a * b ∈ Lay d.h d.y := by
  obtain ⟨β, hβB, hβL, hβ0⟩ := d.hBL
  rw [← hb.commutator_eq hNS hβB hβL hβ0]
  exact d.commutator_mem_L hβL

theorem Case2.ab_mul_ab (hb : d.Case2 b) : d.h.a * b * (d.h.a * b) = 1 := by
  rw [show d.h.a * b * (d.h.a * b) = d.h.a * (b * d.h.a) * b by group, hb.ba,
    show d.h.a * (d.h.a * b) * b = (d.h.a * d.h.a) * (b * b) by group, d.a_mul_a, hb.b_mul_b,
    one_mul]

theorem Case2.ab_ne_one (hb : d.Case2 b) : d.h.a * b ≠ 1 := by
  intro h1
  apply d.h.a_not_mem_B
  have : d.h.a = b⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact inv_mem hb.b_mem_B

theorem Case2.exists_r (hNS : normalizer (d.h.S : Set X) ≤ centralizer ({d.h.a} : Set X))
    (hb : d.Case2 b) : ∃ r ∈ Lay d.h d.y, r * r = 1 ∧ r⁻¹ * (d.h.a * b) * r = d.z ∧
      r⁻¹ * d.z * r = d.h.a * b ∧ r * b = b * r := by
  obtain ⟨r, hrL, hr2, hr⟩ := d.hconj b hb.hbB0 hb.b_mul_b (hb.ab_mem_L hNS)
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  refine ⟨r, hrL, hr2, hr, ?_, ?_⟩
  · rw [← hr, hrinv, show r * (r * (d.h.a * b) * r) * r = (r * r) * (d.h.a * b) * (r * r) by group,
      hr2, one_mul, mul_one]
  · exact (mem_centralizer_iff.mp (d.L_le_centralizer hrL) b hb.hbB0).symm

end Data

end Seven

end CFSG.ComponentClassification.GSThmB
