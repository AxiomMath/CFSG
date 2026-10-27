module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

theorem even_half_card_moved {X Ω : Type*} [Group X] [Finite Ω]
    (hX : ∀ K : Subgroup X, K.index ≠ 2) (ρ : X →* Equiv.Perm Ω) {x : X} (hx : x ^ 2 = 1) :
    Even ((Nat.card Ω - Nat.card (Function.fixedPoints (ρ x))) / 2) := by
  classical
  let := Fintype.ofFinite Ω
  have hsq : ρ x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hsign : Equiv.Perm.sign (ρ x) = 1 := by
    by_contra hne
    have hneg : Equiv.Perm.sign (ρ x) = -1 := (Int.units_eq_one_or _).resolve_left hne
    apply hX (Equiv.Perm.sign.comp ρ).ker
    refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨x, ?_, fun g => ?_⟩
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hneg]
      decide
    · rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ g)) with h1 | h1
      · exact Or.inr (by rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1])
      · left
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, h1, hneg]
        decide
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq] at hsign
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rcases Nat.even_or_odd ((Fintype.card Ω - Fintype.card (Function.fixedPoints (ρ x))) / 2)
    with he | ho
  · exact he
  · rw [ho.neg_one_pow] at hsign
    exact absurd hsign (by decide)

variable {G : Type*} [Group G]

theorem even_half_card_conjugacyWithin_moved [Finite G] {H : Subgroup G}
    (hH : ∀ K : Subgroup H, K.index ≠ 2) (z : G) {x : G} (hxH : x ∈ H) (hx : x ^ 2 = 1) :
    Even ((Nat.card (conjugacyWithin H z) - Nat.card (conjugacyWithin H z ∩
      (Subgroup.centralizer ({x} : Set G) : Set G) : Set G)) / 2) := by
  have hmem : ∀ h : H, ∀ w ∈ conjugacyWithin H z,
      (h : G) * w * (h : G)⁻¹ ∈ conjugacyWithin H z := by
    rintro h w ⟨k, rfl⟩
    exact ⟨k * h⁻¹, by simp [mul_assoc]⟩
  let ρ : H →* Equiv.Perm (conjugacyWithin H z) :=
    { toFun := fun h =>
        { toFun := fun w => ⟨h * w * (h : G)⁻¹, hmem h w w.2⟩
          invFun := fun w => ⟨(h : G)⁻¹ * w * h, by simpa using hmem h⁻¹ w w.2⟩
          left_inv := fun w => by ext; simp [mul_assoc]
          right_inv := fun w => by ext; simp [mul_assoc] }
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hxx : (⟨x, hxH⟩ : H) ^ 2 = 1 := Subtype.ext (by simpa using hx)
  have key := even_half_card_moved hH ρ hxx
  have hfix : Nat.card (Function.fixedPoints (ρ ⟨x, hxH⟩)) = Nat.card (conjugacyWithin H z ∩
      (Subgroup.centralizer ({x} : Set G) : Set G) : Set G) := by
    have hiff : ∀ w : conjugacyWithin H z, w ∈ Function.fixedPoints (ρ ⟨x, hxH⟩) ↔
        (w : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      intro w
      rw [Function.mem_fixedPoints, Function.IsFixedPt, Subgroup.mem_centralizer_singleton_iff]
      change (⟨x * w * x⁻¹, _⟩ : conjugacyWithin H z) = w ↔ _
      rw [Subtype.ext_iff]
      constructor
      · intro h
        change x * (w : G) * x⁻¹ = w at h
        calc (w : G) * x = x * w * x⁻¹ * x := by rw [h]
          _ = x * w := by group
      · intro h
        change x * w * x⁻¹ = w
        rw [← h]
        group
    exact Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.1.2, (hiff w.1).mp w.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, (hiff ⟨w.1, w.2.1⟩).mpr w.2.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  rwa [hfix] at key

end CFSG.ProperTwoGeneratedCore.HighRankPair
