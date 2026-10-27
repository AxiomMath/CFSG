module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21

open Subgroup

theorem exists_normal_index_two_of_odd_perm {G Ω : Type*} [Group G] [Fintype Ω] [DecidableEq Ω]
    (φ : G →* Equiv.Perm Ω) {t : G} (ht : φ t ^ 2 = 1)
    (hodd : Odd ((Fintype.card Ω - Fintype.card (Function.fixedPoints (φ t))) / 2)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N := by
  set ψ : G →* ℤˣ := Equiv.Perm.sign.comp φ with hψ
  have hψt : ψ t = -1 := by
    rw [hψ, MonoidHom.comp_apply, Equiv.Perm.sign_of_pow_two_eq_one ht, hodd.neg_one_pow]
  refine ⟨ψ.ker, inferInstance, ?_, ?_⟩
  · rw [Subgroup.index_ker]
    have hrange : ψ.range = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rcases Int.units_eq_one_or v with rfl | rfl
      · exact one_mem _
      · exact ⟨t, hψt⟩
    rw [hrange, Subgroup.card_top]
    rw [Nat.card_eq_two_iff' (1 : ℤˣ)]
    refine ⟨-1, ⟨by decide, fun y hy => ?_⟩⟩
    rcases Int.units_eq_one_or y with rfl | rfl
    · exact absurd rfl hy
    · rfl
  · intro hmem
    rw [MonoidHom.mem_ker, hψt] at hmem
    exact absurd hmem (by decide)

section ConjClass

variable {G : Type*} [Group G]

@[expose] def conjClassPerm (t : G) (k : G) : Equiv.Perm {s : G // ∃ g : G, g * t * g⁻¹ = s} where
  toFun s := ⟨k * s * k⁻¹, by
    obtain ⟨s, g, rfl⟩ := s
    exact ⟨k * g, by group⟩⟩
  invFun s := ⟨k⁻¹ * s * k, by
    obtain ⟨s, g, rfl⟩ := s
    exact ⟨k⁻¹ * g, by group⟩⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])

@[expose] def conjClassHom (t : G) : G →* Equiv.Perm {s : G // ∃ g : G, g * t * g⁻¹ = s} where
  toFun := conjClassPerm t
  map_one' := Equiv.ext fun s => Subtype.ext (by simp [conjClassPerm])
  map_mul' a b := Equiv.ext fun s => Subtype.ext (by simp [conjClassPerm, mul_assoc])

theorem card_conjClass (t : G) :
    Nat.card {s : G // ∃ g : G, g * t * g⁻¹ = s} = (centralizer ({t} : Set G)).index := by
  rw [Subgroup.index_centralizer_eq_ncard t, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro s
  exact isConj_iff.symm

variable [Finite G]

theorem exists_normal_index_two_of_conj_class {t : G} (ht : t * t = 1)
    (hc : 4 ∣ (centralizer ({t} : Set G)).index)
    (hf : Nat.card {s : G // (∃ g : G, g * t * g⁻¹ = s) ∧ t * s * t⁻¹ = s} % 4 = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N := by
  classical
  have := Fintype.ofFinite {s : G // ∃ g : G, g * t * g⁻¹ = s}
  have hsq : (conjClassHom t t) ^ 2 = 1 := by
    rw [← map_pow, sq, ht, map_one]
  have hfix : Fintype.card (Function.fixedPoints (conjClassHom t t)) =
      Nat.card {s : G // (∃ g : G, g * t * g⁻¹ = s) ∧ t * s * t⁻¹ = s} := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact
      { toFun := fun p => ⟨p.1.1, p.1.2, by
          have := congrArg Subtype.val p.2
          exact this⟩
        invFun := fun q => ⟨⟨q.1, q.2.1⟩, Subtype.ext q.2.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hcard : Fintype.card {s : G // ∃ g : G, g * t * g⁻¹ = s} =
      (centralizer ({t} : Set G)).index := by
    rw [← Nat.card_eq_fintype_card, card_conjClass]
  have hle : Fintype.card (Function.fixedPoints (conjClassHom t t)) ≤
      Fintype.card {s : G // ∃ g : G, g * t * g⁻¹ = s} := Fintype.card_subtype_le _
  rw [hcard, hfix] at hle
  refine exists_normal_index_two_of_odd_perm (conjClassHom t) hsq ?_
  rw [hcard, hfix]
  obtain ⟨k, hk⟩ := hc
  rw [Nat.odd_iff]
  omega

end ConjClass

section Coset

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_index_two_of_free_coset {t : G} (ht : t * t = 1) {U : Subgroup G}
    (hU : ∀ g : G, g⁻¹ * t * g ∉ U) (hidx : U.index % 4 = 2) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 ∧ t ∉ N := by
  classical
  have := Fintype.ofFinite (G ⧸ U)
  have hsq : (MulAction.toPermHom G (G ⧸ U) t) ^ 2 = 1 := by
    rw [← map_pow, sq, ht, map_one]
  have hfix : Function.fixedPoints (MulAction.toPermHom G (G ⧸ U) t) = ∅ := by
    ext q
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_empty_iff_false,
      iff_false]
    induction q using QuotientGroup.induction_on with
    | H g =>
      intro hq
      apply hU g
      have h1 : (QuotientGroup.mk (t * g) : G ⧸ U) = QuotientGroup.mk g := hq
      rw [QuotientGroup.eq] at h1
      have h2 : (t * g)⁻¹ * g = g⁻¹ * t * g := by
        have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
        rw [mul_inv_rev, this]
      rwa [h2] at h1
  refine exists_normal_index_two_of_odd_perm (MulAction.toPermHom G (G ⧸ U)) hsq ?_
  have hempty : Fintype.card (Function.fixedPoints (MulAction.toPermHom G (G ⧸ U) t)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨q, hq⟩ => by rw [hfix] at hq; exact hq⟩
  have hcard : Fintype.card (G ⧸ U) = U.index := by
    rw [← Nat.card_eq_fintype_card]; rfl
  rw [hempty, hcard, Nat.sub_zero, Nat.odd_iff]
  omega

end Coset

end CFSG.LocalAnalysis.EvenBN.Tits.I21
