module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSection

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

variable (h : Hyp52 X) (y : X)

@[expose] def secB0 : Subgroup X := h.B ⊓ conjugate h.B y

abbrev secG0 : Subgroup X := normalizer (h.secB0 y : Set X)

abbrev secB0' : Subgroup ↥(h.secG0 y) := (h.secB0 y).subgroupOf (h.secG0 y)

abbrev secBar : Type := ↥(h.secG0 y) ⧸ h.secB0' y

abbrev secMk : ↥(h.secG0 y) →* h.secBar y := QuotientGroup.mk' (h.secB0' y)

abbrev secImage (Y : Subgroup X) : Subgroup (h.secBar y) :=
  (Y.subgroupOf (h.secG0 y)).map (h.secMk y)

abbrev secQuot : Type := h.secBar y ⧸ pPrimeCore 2 (h.secBar y)

abbrev secQ : ↥(h.secG0 y) →* h.secQuot y :=
  (QuotientGroup.mk' (pPrimeCore 2 (h.secBar y))).comp (h.secMk y)

abbrev secJ0 : Subgroup X := GSLit.fixedLayer h.J (h.secB0 y)

structure SecCond : Prop where
  mem_P : y ∈ h.P
  not_mem_T : y ∉ h.T
  sq_mem_T : y ^ 2 ∈ h.T
  Q_le : h.Q ≤ h.secG0 y
  mem_normalizer_Q : y ∈ normalizer (h.Q : Set X)

theorem secB0_le_B : h.secB0 y ≤ h.B := inf_le_left

theorem isPGroup_secB0 : IsPGroup 2 (h.secB0 y) := (B5a.isPGroup_B h).to_le (h.secB0_le_B y)

instance secB0'_normal : (h.secB0' y).Normal := normal_in_normalizer

theorem ker_secMk : (h.secMk y).ker = h.secB0' y := QuotientGroup.ker_mk' _

theorem centralizer_le_G0 : centralizer (h.secB0 y : Set X) ≤ h.secG0 y :=
  centralizer_le_normalizer _

theorem V_le_centralizer_secB0 : h.V ≤ centralizer (h.secB0 y : Set X) :=
  (B5a.V_le_centralizer h).trans (centralizer_le (SetLike.coe_subset_coe.mpr (h.secB0_le_B y)))

theorem V_le_G0 : h.V ≤ h.secG0 y :=
  (h.V_le_centralizer_secB0 y).trans (h.centralizer_le_G0 y)

theorem secJ0_le : h.secJ0 y ≤ centralizer ({h.a} : Set X) ⊓ centralizer (h.secB0 y : Set X) :=
  (GSLit.fixedLayer_le_inf h.J (h.secB0 y)).trans (inf_le_inf_right _ h.J_le)

theorem secJ0_le_G0 : h.secJ0 y ≤ h.secG0 y :=
  (h.secJ0_le y).trans (inf_le_right.trans (h.centralizer_le_G0 y))

theorem B_le_Q : h.B ≤ h.Q := fun _ hb =>
  mem_inf.mpr ⟨(mem_inf.mp (h.B_le hb)).1, le_normalizer hb⟩

theorem a_mem_Q : h.a ∈ h.Q := mem_inf.mpr ⟨B5a.a_mem_S h, h.a_mem_normalizer⟩

theorem a_not_mem_secB0 : h.a ∉ h.secB0 y := fun ha => B5a.a_not_mem_B h (h.secB0_le_B y ha)

variable {h y}

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem mem_S : y ∈ h.S := (mem_inf.mp hc.mem_P).1

theorem B_le_G0 : h.B ≤ h.secG0 y := h.B_le_Q.trans hc.Q_le

theorem a_mem_G0 : h.a ∈ h.secG0 y := hc.Q_le h.a_mem_Q

theorem T_le_G0 : h.T ≤ h.secG0 y := inf_le_left.trans hc.Q_le

theorem y_mem_G0 : y ∈ h.secG0 y := by
  have hx2 : y ^ 2 ∈ normalizer (h.B : Set X) := (mem_inf.mp (mem_inf.mp hc.sq_mem_T).1).2
  rw [mem_normalizer_iff]
  intro z
  rw [secB0, mem_inf, mem_inf, mem_conjugate_iff, mem_conjugate_iff]
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨hy2, ?_⟩
    rw [show y * (y * z * y⁻¹) * y⁻¹ = y ^ 2 * z * (y ^ 2)⁻¹ by rw [pow_two]; group]
    exact (mem_normalizer_iff.mp hx2 z).mp hy1
  · rintro ⟨hy1, hy2⟩
    refine ⟨?_, hy1⟩
    rw [show y * (y * z * y⁻¹) * y⁻¹ = y ^ 2 * z * (y ^ 2)⁻¹ by rw [pow_two]; group] at hy2
    exact (mem_normalizer_iff.mp hx2 z).mpr hy2

theorem y_not_mem_normalizer : y ∉ normalizer (h.B : Set X) := fun hyN =>
  hc.not_mem_T (mem_inf.mpr ⟨mem_inf.mpr ⟨mem_S hc, hyN⟩, hc.mem_P⟩)

theorem secB0_ne_B : h.secB0 y ≠ h.B := by
  intro heq
  apply y_not_mem_normalizer hc
  have hle : h.B ≤ conjugate h.B y := by
    intro b hb
    have hb' : b ∈ h.secB0 y := by rw [heq]; exact hb
    exact (mem_inf.mp hb').2
  have hcard : Nat.card (conjugate h.B y) = Nat.card h.B :=
    (Nat.card_congr (h.B.equivMapOfInjective _ (MulAut.conj y⁻¹).injective).toEquiv).symm
  have heq' : conjugate h.B y = h.B :=
    (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
  have h1 := mem_normalizer_of_conjugate_eq heq'
  exact h1

end SecCond

end Hyp52

end CFSG.ComponentClassification.GSThmB
