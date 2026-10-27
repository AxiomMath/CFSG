module

public import CFSG.GroupTheory.SylowIntersectionControl.Defs
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] {p : ℕ}

theorem isSylowOf_map_conj [Finite G] [Fact p.Prime] {P K : Subgroup G} (h : IsSylowOf p P K)
    (g : G) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hPK, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hPK, hP.map _, ?_⟩
  rwa [Subgroup.relIndex_map_map_of_injective P K (MulAut.conj g).injective]

theorem le_of_isSylowOf_inf [Finite G] [Fact p.Prime] {S X K : Subgroup G}
    (hS : IsSylowOf p S K) (hXK : X ≤ K) (hX : ¬ p ∣ X.relIndex K)
    (h : IsSylowOf p (S ⊓ X) X) : S ≤ X := by
  have hmul := Subgroup.relIndex_mul_card X K
  rw [inf_eq_left.mpr hXK] at hmul
  have hrel0 : X.relIndex K ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact Nat.card_pos.ne' hmul.symm
  have hfac : (Nat.card ↥K).factorization p = (Nat.card ↥X).factorization p := by
    rw [← hmul, Nat.factorization_mul hrel0 Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hX, zero_add]
  have hcard : Nat.card ↥(S ⊓ X) = Nat.card ↥S := by
    rw [h.card_eq, hS.card_eq, hfac]
  have heq : S ⊓ X = S :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
  exact inf_eq_left.mp heq

theorem sylowConjLink_of_le [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K D S S' X : Subgroup G} (hS : IsSylowOf p S K) (hS' : IsSylowOf p S' K) (hX : X ∈ 𝓕)
    (hXK : X ≤ K) (hSX : S ≤ X) (hS'X : S' ≤ X) (hD : D ≤ S ⊓ S') :
    SylowConjLink p 𝓕 K D S S' := by
  have hSX' : S ⊓ X = S := inf_eq_left.mpr hSX
  have hS'X' : S' ⊓ X = S' := inf_eq_left.mpr hS'X
  have hSXs : IsSylowOf p S X := hS.of_le hSX hXK
  have hS'Xs : IsSylowOf p S' X := hS'.of_le hS'X hXK
  obtain ⟨x, hxX, hx⟩ := hSXs.exists_mem_conj hS'Xs
  have hmap : S.map (MulAut.conj x).toMonoidHom = S' := by
    ext y
    rw [Subgroup.mem_map, hx y]
    constructor
    · rintro ⟨s, hs, rfl⟩
      change x⁻¹ * (x * s * x⁻¹) * x ∈ S
      have hc : x⁻¹ * (x * s * x⁻¹) * x = s := by group
      rwa [hc]
    · intro hy
      refine ⟨x⁻¹ * y * x, hy, ?_⟩
      change x * (x⁻¹ * y * x) * x⁻¹ = y
      group
  have hXS : X ∈ sylowMembers p 𝓕 S := ⟨hX, by rw [hSX']; exact hSXs⟩
  have hXS' : X ∈ sylowMembers p 𝓕 S' := ⟨hX, by rw [hS'X']; exact hS'Xs⟩
  have hD' : D ≤ S ⊓ S' ⊓ X :=
    hD.trans (le_inf le_rfl ((inf_le_left : S ⊓ S' ≤ S).trans hSX))
  exact ⟨hS, hS', X, hXS, hXS', hD', x, hxX, hmap.symm⟩

end CFSG.GroupTheory
