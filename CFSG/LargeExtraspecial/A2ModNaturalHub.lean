module

public import CFSG.LargeExtraspecial.A2ModNaturalOmega
public import CFSG.LargeExtraspecial.AS35YTHubO

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.Open CFSG.Blueprint Matrix CFSG.ClassicalGroups.Symplectic

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem RootClass.exists_ne_mul_comm (hD : RootClass X D) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨d, hd, e, he, h4⟩ := hD.2.1
  refine ⟨d, e, fun hc => ?_⟩
  have h2 : (d * e) ^ 2 = 1 := by
    rw [_root_.sq, show d * e * (d * e) = d * d * (e * e) by
      rw [mul_assoc, ← mul_assoc e d e, ← hc]; group, hD.mul_self hd, hD.mul_self he, mul_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h4] at this
  exact absurd this (by norm_num)

theorem RootClass.commutator_eq_top [IsSimpleGroup X] (hD : RootClass X D) :
    commutator X = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hD.exists_ne_mul_comm
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a (Subgroup.mem_top a))
  · exact h


theorem exists_naturalSeries_psp [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) {m : ℕ}
    (hm : 4 ≤ m) (hL : LieModel X .PSp m 2 1) :
    ∃ (Q₁ Q₂ : Submodule (ZMod 2) V) (φ : X ≃* ↥(StatedSp m (ZMod 2)))
      (π : V →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      Q₁ ≤ Q₂ ∧ commSpaceOf ρ ⊤ ≤ Q₂ ∧ (∀ x, ∀ v ∈ Q₁, ρ x v = v) ∧
      Q₂.map π = ⊤ ∧ Q₂ ⊓ LinearMap.ker π = Q₁ ∧
      (∀ x, ∀ v ∈ Q₂, π (ρ x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ u ∈ Q₂, ∀ v ∈ Q₂, polar Q u v = spForm m (ZMod 2) (π u) (π v)) := by
  have hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m + 1 := by
    have := (AS35YT.dim_of_psp hD hA hL).1
    omega
  have hX : Nat.card X = 2 ^ (m ^ 2) * ∏ i ∈ Finset.Icc 1 m, (2 ^ (2 * i) - 1) := by
    rw [(Ord.card_of_lieModel_PSp hL).2, AS35YT.ordBC_two_eq', _root_.sq]
  obtain ⟨φ, π, hsurj, hker, heq, hpol⟩ := Natural.exists_natural_symplectic hA.nondegenerate
    hA.map_apply hA.injective hD.2.2.2 hX hdim
  refine ⟨commSpaceOf ρ ⊤ ⊓ LinearMap.ker π, commSpaceOf ρ ⊤, φ, π, inf_le_left, le_rfl,
    fun x v hv => ?_, hsurj, rfl, heq, hpol⟩
  obtain ⟨hv, hv0⟩ := Submodule.mem_inf.mp hv
  exact (hker v hv).mp hv0 x

theorem exists_natural_pOmegaPlus [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ) {m : ℕ}
    (hm : 5 ≤ m) (hL : LieModel X .POmegaPlus m 2 1) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadPlus m (ZMod 2))))
      (π : V →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadPlus m (ZMod 2) (π v) = Q v) := by
  have hdim := ((AS35YT.dim_of_pomega hD hA (Or.inl hL)).1 hm).le
  have := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus X m 2 1
    (Ord.statedClassicalModel_of_lieModel (by decide) hL)).2
  exact Natural.exists_natural_plus hA.nondegenerate hA.map_apply hA.injective hD.2.2.2
    hD.commutator_eq_top (by omega) (Ord.card_of_lieModel_POmegaPlus hL).2
    (AS35YT.spOrd_pred_lt_card_of_lieModel_POmega (Or.inl hL)) hdim

theorem exists_natural_pOmegaMinus_of_finrank_le [Finite X] (hD : RootClass X D)
    (hA : A2Action D Q ρ) {m : ℕ} (hm : 4 ≤ m) (hL : LieModel X .POmegaMinus m 2 1)
    (hdim : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * m) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)))
      (π : V →ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadMinus m (ZMod 2) 1 1 (π v) = Q v) := by
  have := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus X m 2
    1 (Ord.statedClassicalModel_of_lieModel (by decide) hL)).2
  exact Natural.exists_natural_minus hA.nondegenerate hA.map_apply hA.injective hD.2.2.2
    hD.commutator_eq_top hm (Ord.card_of_lieModel_POmegaMinus hL).2
    (AS35YT.spOrd_pred_lt_card_of_lieModel_POmega (Or.inr hL)) hdim

theorem exists_natural_pOmegaMinus_of_five_le [Finite X] (hD : RootClass X D)
    (hA : A2Action D Q ρ) {m : ℕ} (hm : 5 ≤ m) (hL : LieModel X .POmegaMinus m 2 1) :
    ∃ (φ : X ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)))
      (π : V →ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)),
      (commSpaceOf ρ ⊤).map π = ⊤ ∧ commSpaceOf ρ ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ commSpaceOf ρ ⊤, π (ρ x v) =
        ((φ x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ commSpaceOf ρ ⊤, StatedQuadMinus m (ZMod 2) 1 1 (π v) = Q v) :=
  exists_natural_pOmegaMinus_of_finrank_le hD hA (by omega) hL
    ((AS35YT.dim_of_pomega hD hA (Or.inr hL)).1 hm).le

end CFSG.LargeExtraspecial.A2Mod
