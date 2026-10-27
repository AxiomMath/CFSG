module

public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

theorem oPrimeResidualOf_le_of_two_elements {X : Type*} [Group X] {V S : Subgroup X}
    (h : ∀ v ∈ V, (∃ k : ℕ, v ^ (2 ^ k) = 1) → v ∈ S) : oPrimeResidualOf 2 V ≤ S := by
  unfold oPrimeResidualOf oPrimeResidual
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro ⟨v, hv⟩ ⟨k, hk⟩
  exact h v hv ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem oPrimeResidualOf_le_self {X : Type*} [Group X] (V : Subgroup X) :
    oPrimeResidualOf 2 V ≤ V := Subgroup.map_subtype_le _

theorem mem_oPrimeResidualOf_of_two_element {X : Type*} [Group X] {V : Subgroup X} {g : X}
    (hg : g ∈ V) (h2 : ∃ k : ℕ, g ^ (2 ^ k) = 1) : g ∈ oPrimeResidualOf 2 V :=
  ⟨⟨g, hg⟩, Subgroup.subset_closure (by
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩), rfl⟩

theorem map_oPrimeResidualOf_le {X X' : Type*} [Group X] [Group X'] (f : X →* X')
    (V : Subgroup X) : (oPrimeResidualOf 2 V).map f ≤ oPrimeResidualOf 2 (V.map f) := by
  rintro _ ⟨r, hr, rfl⟩
  have hle : oPrimeResidualOf 2 V ≤ (oPrimeResidualOf 2 (V.map f)).comap f := by
    unfold oPrimeResidualOf oPrimeResidual
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro ⟨v, hv⟩ ⟨k, hk⟩
    have hv2 : (v ^ (2 ^ k) = 1) := by simpa using congrArg Subtype.val hk
    show f v ∈ oPrimeResidualOf 2 (V.map f)
    exact mem_oPrimeResidualOf_of_two_element ⟨v, hv, rfl⟩ ⟨k, by rw [← map_pow, hv2, map_one]⟩
  exact hle hr

theorem mem_normalizer_of_map_conj_eq {X : Type*} [Group X] {K : Subgroup X} {x : X}
    (h : K.map (MulAut.conj x).toMonoidHom = K) : x ∈ normalizer (K : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨k, hk, hke⟩ := hy
    have : k = y := by
      have : x * k * x⁻¹ = x * y * x⁻¹ := hke
      simpa using this
    rw [← this]; exact hk


end CFSG.GH74.GLS.Balance
