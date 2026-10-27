module

import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecCorr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB71Step2a

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

abbrev secP0 (h : Hyp52 X) (y : X) : Subgroup X := h.S ⊓ h.secG0 y ⊓ h.P

variable {h : Hyp52 X} {y : X}

theorem B_inf_zpowers_eq_bot : h.B ⊓ zpowers h.a = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwB, hwa⟩ := mem_inf.mp hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hwa
  have ha2 : h.a ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m by ring, zpow_mul, ha2, one_zpow]
    exact one_mem _
  · exfalso
    apply B5a.a_not_mem_B h
    rw [zpow_add_one, zpow_mul, ha2, one_zpow, one_mul] at hwB
    exact hwB

theorem nP_of_T_eq (hT : h.T = h.B ⊔ zpowers h.a) :
    h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧ ∀ b ∈ h.B, b * h.a = h.a * b :=
  ⟨hT, B_inf_zpowers_eq_bot, fun _ hb => h.comm_a_B hb⟩

theorem mem_normalizer_secJ0_of_sup {g : X}
    (hg : g ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X)) :
    g ∈ normalizer (h.secJ0 y : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC : h.secJ0 y ≤ centralizer (h.secB0 y : Set X) :=
    (GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans inf_le_right
  have hBN : h.secB0 y ≤ normalizer (h.secJ0 y : Set X) :=
    (Subgroup.le_centralizer_iff.mp hJC).trans (Subgroup.centralizer_le_normalizer _)
  have hBs : Group.IsSolvable (h.secB0 y) := by
    have := (h.isPGroup_secB0 y).isNilpotent
    infer_instance
  have hJ0 : ⁅h.secJ0 y, h.secJ0 y⁆ = h.secJ0 y := Subgroup.isPerfect_iff.mp isPerfect_secJ0
  have hP : ⁅conjugate (h.secJ0 y) g, conjugate (h.secJ0 y) g⁆ = conjugate (h.secJ0 y) g := by
    change ⁅(h.secJ0 y).map (MulAut.conj g⁻¹).toMonoidHom,
      (h.secJ0 y).map (MulAut.conj g⁻¹).toMonoidHom⁆ = (h.secJ0 y).map (MulAut.conj g⁻¹).toMonoidHom
    rw [← Subgroup.map_commutator, hJ0]
  have hle : conjugate (h.secJ0 y) g ≤ h.secJ0 y ⊔ h.secB0 y := by
    have h1 : conjugate (h.secJ0 y ⊔ h.secB0 y) g = h.secJ0 y ⊔ h.secB0 y :=
      conjugate_eq_of_mem_normalizer hg
    rw [← h1]
    exact Subgroup.map_mono le_sup_left
  have h1 := CFSG.SeitzReduction.perfect_le_of_le_sup hBN hBs hP hle
  have heq : conjugate (h.secJ0 y) g = h.secJ0 y :=
    eq_of_le_of_card_ge h1 (le_of_eq (card_conjugate_eq (h.secJ0 y) g).symm)
  exact mem_normalizer_of_conjugate_eq heq

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem y_normalizes_T : y ∈ normalizer (h.T : Set X) := by
  have hP : y ∈ normalizer (h.P : Set X) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · exact B5a.conj_mem_P h (mem_S hc)
    · intro hw
      have := B5a.conj_mem_P h (inv_mem (mem_S hc)) hw
      rwa [show y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w by group] at this
  exact Six.mem_normalizer_inf hc.mem_normalizer_Q hP

theorem relIndex_secB0 (hT : h.T = h.B ⊔ zpowers h.a) : (h.secB0 y).relIndex h.B = 2 :=
  h.relIndex_inf_conjugate (nP_of_T_eq hT) (y_normalizes_T hc) (y_not_mem_normalizer hc)

theorem B_le_secP0 : h.B ≤ h.secP0 y :=
  le_inf (le_inf (h.B_le.trans inf_le_left) (B_le_G0 hc)) h.B_le

theorem y_mem_secP0 : y ∈ h.secP0 y :=
  mem_inf.mpr ⟨mem_inf.mpr ⟨mem_S hc, y_mem_G0 hc⟩, hc.mem_P⟩

theorem a_mem_secP0 : h.a ∈ h.secP0 y :=
  mem_inf.mpr ⟨mem_inf.mpr ⟨B5a.a_mem_S h, a_mem_G0 hc⟩, h.a_mem_P⟩

end SecCond

end Hyp52

end CFSG.ComponentClassification.GSThmB
