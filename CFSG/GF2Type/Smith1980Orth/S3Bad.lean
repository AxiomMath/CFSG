module

public import CFSG.GF2Type.Smith1980Orth.S2Pair
public import CFSG.GF2Type.Smith1980Orth.LocalGlue
public import CFSG.GF2Type.Smith1980Orth.Transport
public import CFSG.LargeExtraspecial.S14SMKDeltaBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def Bad (S : Setting G) (k : G) : Prop :=
  k * S.z * k⁻¹ ∈ S.M ∧ k * S.z * k⁻¹ ∉ S.QG ∧ ∀ a : G, IsConj S.z a → a ∉ S.QG ⊓ S.Qa k

namespace Bad

variable {S : Setting G} {k : G}

theorem mem_M (h : Bad S k) : k * S.z * k⁻¹ ∈ S.M := h.1

theorem not_mem_QG (h : Bad S k) : k * S.z * k⁻¹ ∉ S.QG := h.2.1

theorem not_mem (h : Bad S k) {a : G} (ha : IsConj S.z a) : a ∉ S.QG ⊓ S.Qa k := h.2.2 a ha

theorem conjBy_Qa_inv (S : Setting G) (k : G) : (S.conjBy k).Qa k⁻¹ = S.QG :=
  Setting.QG_eq_of_z_eq _ _ (by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group)

theorem symm (h : Bad S k) : Bad (S.conjBy k) k⁻¹ := by
  have e : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ = S.z := by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group
  refine ⟨?_, ?_, fun a ha haD => ?_⟩
  · rw [e]
    exact mem_centralizer_singleton_iff.mpr (S.z_comm h.mem_M).symm
  · rw [e]
    exact S14.SMK.z_not_mem_Qa S h.not_mem_QG
  · rw [conjBy_Qa_inv] at haD
    exact h.not_mem ((S.isConj_conjBy_z_iff k).mp ha) ⟨haD.2, haD.1⟩

theorem mul_left {m : G} (hm : m ∈ S.M) (h : Bad S k) : Bad S (m * k) := by
  have e : m * k * S.z * (m * k)⁻¹ = m * (k * S.z * k⁻¹) * m⁻¹ := by group
  refine ⟨?_, ?_, fun a ha haD => ?_⟩
  · rw [e]
    exact S.M.mul_mem (S.M.mul_mem hm h.mem_M) (S.M.inv_mem hm)
  · rw [e]
    intro hQ
    apply h.not_mem_QG
    have := S.conj_mem_QG (S.M.inv_mem hm) hQ
    rwa [show m⁻¹ * (m * (k * S.z * k⁻¹) * m⁻¹) * m⁻¹⁻¹ = k * S.z * k⁻¹ by group] at this
  · refine h.not_mem (a := m⁻¹ * a * m) ?_ ⟨?_, ?_⟩
    · exact ha.trans (isConj_iff.mpr ⟨m⁻¹, by rw [inv_inv]⟩)
    · have := S.conj_mem_QG (S.M.inv_mem hm) haD.1
      rwa [inv_inv] at this
    · exact S.mem_Qa_mul_iff.mp haD.2

theorem of_z_eq {T : Setting G} (hz : T.z = S.z) (h : Bad T k) : Bad S k := by
  have hM : T.M = S.M := by
    show centralizer ({T.z} : Set G) = centralizer ({S.z} : Set G)
    rw [hz]
  have hQ : T.QG = S.QG := Setting.QG_eq_of_z_eq T S hz
  have hQa : T.Qa k = S.Qa k :=
    Setting.QG_eq_of_z_eq (T.conjBy k) (S.conjBy k) (by simp [hz])
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · rw [← hM, ← hz]
    exact h.mem_M
  · rw [← hQ, ← hz]
    exact h.not_mem_QG
  · rw [← hQ, ← hQa]
    exact h.not_mem (hz ▸ ha)

theorem of_symm (h : Bad (S.conjBy k) k⁻¹) : Bad S k := by
  have h' := h.symm
  rw [inv_inv] at h'
  exact h'.of_z_eq (by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group)

end Bad

theorem exists_of_not_bad {S : Setting G} {k : G} (h : ¬ Bad S k) (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hxQ : k * S.z * k⁻¹ ∉ S.QG) : ∃ a : G, IsConj S.z a ∧ a ∈ S.QG ⊓ S.Qa k := by
  by_contra hno
  push Not at hno
  exact h ⟨hxM, hxQ, hno⟩

theorem S2Data.oe34a_of_forall_not_bad {S : Setting G} {M1 : Subgroup S.O} (D : S2Data S M1)
    (h : ∀ k : G, ¬ Bad S k) : OE34a S := by
  intro x hx hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  obtain ⟨a, ha, haD⟩ := exists_of_not_bad (h k) hxM hxQ
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  exact D.not_isConj_mul_z_of_mem rfl hxM hxQ haD

end CFSG.GF2Type.Smith1980Orth
