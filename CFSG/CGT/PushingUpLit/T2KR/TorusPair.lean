module

public import CFSG.CGT.Timmesfeld75.L2Aut

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped MatrixGroups

section Conj

variable {X : Type*} [Group X]

theorem mem_normalizer_conjSubgroup_of {T : Subgroup X} {g z : X}
    (h : g⁻¹ * z * g ∈ Subgroup.normalizer (T : Set X)) :
    z ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_conjSubgroup_eq] at h ⊢
  rw [conjSubgroup_conjSubgroup]
  have e : z * g = g * (g⁻¹ * z * g) := by group
  rw [e, ← conjSubgroup_conjSubgroup, h]

end Conj

section Pair

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem l2Pair_exists_twoPoint_torus (h : IsL2Pair X S q) {x : X} (hne : conjSubgroup x S ≠ S) :
    ∃ H : Subgroup X, H ≤ Subgroup.normalizer (S : Set X) ∧
      H ≤ Subgroup.normalizer ((conjSubgroup x S : Subgroup X) : Set X) ∧ Nat.card H = q - 1 := by
  obtain ⟨F, _, _, _, e, hq, hSe⟩ := h
  have hconj : (conjSubgroup x S).map e.toMonoidHom = conjSubgroup (e x) (utri F) := by
    rw [map_conjSubgroup_mulEquiv, hSe]
  have hab : conjSubgroup 1 (utri F) ≠ conjSubgroup (e x) (utri F) := by
    rw [conjSubgroup_one, ← hconj, ← hSe]
    intro heq
    exact hne (Subgroup.map_injective e.injective heq).symm
  obtain ⟨g, hP, hQ⟩ := exists_conj_utri_ltri_of_ne hab
  rw [conjSubgroup_one] at hP
  refine ⟨(conjSubgroup g (torus F)).map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h1 : z ∈ Subgroup.normalizer ((conjSubgroup g (utri F) : Subgroup _) : Set _) :=
      mem_normalizer_conjSubgroup_of (by
        rw [normalizer_utri]
        exact torus_le_borel (mem_conjSubgroup.1 hz))
    rw [← hP] at h1
    rw [mem_normalizer_iff_mulEquiv e, hSe]
    simpa using h1
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h1 : z ∈ Subgroup.normalizer ((conjSubgroup g (ltri F) : Subgroup _) : Set _) :=
      mem_normalizer_conjSubgroup_of (by
        obtain ⟨a, ha⟩ := mem_torus_iff.1 (mem_conjSubgroup.1 hz)
        rw [ha]
        exact mem_normalizer_of_conjSubgroup_eq (conjSubgroup_torusElt_ltri a))
    rw [← hQ] at h1
    rw [mem_normalizer_iff_mulEquiv e, hconj]
    simpa using h1
  · rw [Subgroup.card_map_of_injective e.symm.injective, card_conjSubgroup, card_torus, hq]

end Pair

end CFSG.CGT.PushingUpLit.T2KR
