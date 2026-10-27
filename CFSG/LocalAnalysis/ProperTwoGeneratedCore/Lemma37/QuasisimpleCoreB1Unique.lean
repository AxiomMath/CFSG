module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Bender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBasics

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.BenderSuzuki.PFchapter1section1 CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ShultStronglyClosedTI

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

omit [Finite J] in
@[expose] def IsXType (T : Sylow 2 (quasiNormalizer u)) (L : Subgroup (QuasiQuotient u))
    (y : J ⧸ Subgroup.center J) : Prop :=
  ∃ x ∈ b1X T L, x ≠ 1 ∧ IsConj y x

section IsXType

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)}

omit [Finite J] in
theorem isXType_of_mem_X {x : J ⧸ Subgroup.center J} (hx : x ∈ b1X T L) (hx1 : x ≠ 1) :
    IsXType T L x :=
  ⟨x, hx, hx1, IsConj.refl x⟩

omit [Finite J] in
theorem IsXType.of_isConj {y z : J ⧸ Subgroup.center J} (hy : IsXType T L y)
    (hyz : IsConj y z) : IsXType T L z := by
  obtain ⟨x, hx, hx1, hyx⟩ := hy
  exact ⟨x, hx, hx1, hyz.symm.trans hyx⟩

omit [Finite J] in
theorem IsXType.conj {y : J ⧸ Subgroup.center J} (hy : IsXType T L y)
    (g : J ⧸ Subgroup.center J) : IsXType T L (g * y * g⁻¹) :=
  hy.of_isConj (isConj_iff.mpr ⟨g, rfl⟩)

omit [Finite J] in
theorem IsXType.inv_mul_mul {y : J ⧸ Subgroup.center J} (hy : IsXType T L y)
    (g : J ⧸ Subgroup.center J) : IsXType T L (g⁻¹ * y * g) := by
  have h := hy.conj g⁻¹
  rwa [inv_inv] at h

omit [Finite J] in
theorem isXType_conj_iff (g y : J ⧸ Subgroup.center J) :
    IsXType T L (g * y * g⁻¹) ↔ IsXType T L y := by
  refine ⟨fun h => ?_, fun h => h.conj g⟩
  have h' := h.inv_mul_mul g
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h'

end IsXType

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem orderOf_of_isXType (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) : orderOf y = 2 := by
  obtain ⟨x, hx, hx1, hyx⟩ := hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hyx.symm
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact hb.orderOf_of_mem_X hx hx1

theorem not_isMixedInv_of_isXType (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) : ¬ IsMixedInv y := by
  obtain ⟨x, hx, -, hyx⟩ := hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hyx.symm
  rw [isMixedInv_conj_iff]
  exact hb.not_isMixedInv_of_mem_X hx

theorem isMixedInv_or_isXType_or_exists_isConj (hb : CaseB1 Q B T L M)
    {v : J ⧸ Subgroup.center J} (hv : orderOf v = 2) (hvB : v ∈ b1Bar B) :
    IsMixedInv v ∨ IsXType T L v ∨ ∃ d ∈ b1D T L, orderOf d = 2 ∧ IsConj v d := by
  by_cases hm : IsMixedInv v
  · exact Or.inl hm
  obtain ⟨b, -, hbS⟩ := involution_conjugate_into_sylow hb.sylow (b1Bar B) hb.S_le v hvB hv
  have h2 : orderOf (b⁻¹ * v * b) = 2 := (orderOf_inv_mul_mul b v).trans hv
  have hm' : ¬ IsMixedInv (b⁻¹ * v * b) := by rwa [isMixedInv_inv_mul_mul_iff]
  have hconj : IsConj v (b⁻¹ * v * b) := isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩
  rcases hb.mem_X_or_mem_D_of_not_isMixedInv hbS h2 hm' with hX | hD
  · refine Or.inr (Or.inl ⟨_, hX, fun h1 => ?_, hconj⟩)
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  · exact Or.inr (Or.inr ⟨_, hD, h2, hconj⟩)

theorem centralizer_le_of_mem_X
    (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B :=
  hb.centralizer_le_of_centralizer_X_le hx hx1 hb.centralizer_X_le

theorem mem_of_conj_mem_of_mem_X
    (hb : CaseB1 Q B T L M) {x g : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) (hg : g * x * g⁻¹ ∈ b1Bar B) : g ∈ b1Bar B := by
  have h2 : orderOf (g * x * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hb.orderOf_of_mem_X hx hx1
  obtain ⟨b, hbB, hbS⟩ := involution_conjugate_into_sylow hb.sylow (b1Bar B) hb.S_le _ hg h2
  have hkS : b⁻¹ * g * x * (b⁻¹ * g)⁻¹ ∈ b1S T := by
    rwa [show b⁻¹ * g * x * (b⁻¹ * g)⁻¹ = b⁻¹ * (g * x * g⁻¹) * b by group]
  obtain ⟨n, hn, hnx⟩ := exists_mem_normalizer_conj_eq_of_mem_centralizer hb.sylow
    (hb.mem_centralizer_of_mem_X hx) (hb.mem_centralizer_of_mem_X (hb.mul_mul_inv_mem_X hx hkS))
    (g := (b⁻¹ * g)⁻¹) (by rw [inv_inv])
  have hC : n * (b⁻¹ * g) ∈ Subgroup.centralizer {x} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * (b⁻¹ * g) * x = n * (b⁻¹ * g * x * (b⁻¹ * g)⁻¹) * (b⁻¹ * g) := by group
      _ = n * (n⁻¹ * x * n) * (b⁻¹ * g) := by rw [hnx]
      _ = x * (n * (b⁻¹ * g)) := by group
  rw [show g = b * n⁻¹ * (n * (b⁻¹ * g)) by group]
  exact (b1Bar B).mul_mem ((b1Bar B).mul_mem hbB ((b1Bar B).inv_mem (hb.normalizer_le hn)))
    (hb.centralizer_le_of_mem_X hx hx1 hC)

theorem unique_containment
    (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) (g : J ⧸ Subgroup.center J) :
    x ∈ rightConjugate (b1Bar B) g ↔ g ∈ b1Bar B := by
  rw [mem_rightConjugate_iff_conj_mem]
  exact ⟨hb.mem_of_conj_mem_of_mem_X hx hx1, fun hg => (b1Bar B).mul_mem
    ((b1Bar B).mul_mem hg (hb.S_le (hb.X_le_S hx))) ((b1Bar B).inv_mem hg)⟩

theorem mem_of_conj_mem_of_isXType
    (hb : CaseB1 Q B T L M) {y g : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) (hyB : y ∈ b1Bar B) (hg : g * y * g⁻¹ ∈ b1Bar B) : g ∈ b1Bar B := by
  obtain ⟨x, hx, hx1, hyx⟩ := hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hyx.symm
  have hc := hb.mem_of_conj_mem_of_mem_X hx hx1 hyB
  have hgc := hb.mem_of_conj_mem_of_mem_X hx hx1 (g := g * c)
    (by rwa [show g * c * x * (g * c)⁻¹ = g * (c * x * c⁻¹) * g⁻¹ by group])
  rw [show g = g * c * c⁻¹ by group]
  exact (b1Bar B).mul_mem hgc ((b1Bar B).inv_mem hc)

theorem centralizer_le_of_isXType
    (hb : CaseB1 Q B T L M) {y : J ⧸ Subgroup.center J}
    (hy : IsXType T L y) (hyB : y ∈ b1Bar B) :
    Subgroup.centralizer ({y} : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B := fun g hg =>
  hb.mem_of_conj_mem_of_isXType hy hyB (by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    exact hyB)

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
