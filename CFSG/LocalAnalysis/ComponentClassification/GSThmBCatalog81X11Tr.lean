module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GSThmB

namespace X11

open Subgroup CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

theorem inv_mul_eq_one_of_ne_one {x y : Multiplicative (ZMod 2)} (hx : x ≠ 1) (hy : y ≠ 1) :
    x⁻¹ * y = 1 := by
  revert x y
  decide

variable {H : Type*} [Group H] [Finite H]

theorem exists_normal_of_character {T : Subgroup H} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (χ : T →* Multiplicative (ZMod 2)) {u : H} (huT : u ∈ T)
    (hu : χ ⟨u, huT⟩ ≠ 1) (huu : u * u = 1)
    (hext : ∀ (g : H) (hg : g⁻¹ * u * g ∈ T), IsExtremalIn 2 T (g⁻¹ * u * g) →
      χ ⟨g⁻¹ * u * g, hg⟩ ≠ 1) :
    ∃ (N : Subgroup H) (_ : N.Normal), IsCyclic (H ⧸ N) ∧ IsPGroup 2 (H ⧸ N) ∧ u ∉ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup H := χ.ker.map T.subtype with hQ
  have hmemQ : ∀ (t : H) (ht : t ∈ T), t ∈ Q ↔ χ ⟨t, ht⟩ = 1 := by
    intro t ht
    constructor
    · rintro ⟨s, hs, hst⟩
      have hs' : s = ⟨t, ht⟩ := Subtype.ext hst
      rw [← hs']
      exact hs
    · intro h1
      exact ⟨⟨t, ht⟩, h1, rfl⟩
  have hQT : Q ≤ T := map_subtype_le _
  have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
    intro t ht q hq
    have hqT := hQT hq
    rw [hmemQ _ hqT] at hq
    rw [hmemQ _ (T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht))]
    have e : (⟨t * q * t⁻¹, T.mul_mem (T.mul_mem ht hqT) (T.inv_mem ht)⟩ : T) =
        ⟨t, ht⟩ * ⟨q, hqT⟩ * (⟨t, ht⟩ : T)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hq, mul_one, mul_inv_cancel]
  have hcyc : ∃ c ∈ T, ∀ t ∈ T, ∃ k : ℤ, (c ^ k)⁻¹ * t ∈ Q := by
    refine ⟨u, huT, fun t ht => ?_⟩
    by_cases htQ : χ ⟨t, ht⟩ = 1
    · exact ⟨0, by rw [zpow_zero, inv_one, one_mul, hmemQ _ ht]; exact htQ⟩
    · refine ⟨1, ?_⟩
      have hmem : (u ^ (1 : ℤ))⁻¹ * t ∈ T := by
        rw [zpow_one]
        exact T.mul_mem (T.inv_mem huT) ht
      rw [hmemQ _ hmem]
      have e : (⟨(u ^ (1 : ℤ))⁻¹ * t, hmem⟩ : T) = (⟨u, huT⟩ : T)⁻¹ * ⟨t, ht⟩ :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_inv]
      exact inv_mul_eq_one_of_ne_one hu htQ
  have huQ : u ∉ Q := fun h1 => hu ((hmemQ _ huT).mp h1)
  have htr := thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc huT huQ
    (fun g k _ => by
      rw [pow_mul, sq, huu, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hg hge => by
      right
      have hmem : u⁻¹ * (g⁻¹ * u * g) ∈ T := T.mul_mem (T.inv_mem huT) hg
      rw [hmemQ _ hmem]
      have e : (⟨u⁻¹ * (g⁻¹ * u * g), hmem⟩ : T) = (⟨u, huT⟩ : T)⁻¹ * ⟨g⁻¹ * u * g, hg⟩ := rfl
      rw [e, map_mul, map_inv]
      exact inv_mul_eq_one_of_ne_one hu (hext g hg hge))
  rcases htr with ⟨N, hN, hcycN, hpN, huN⟩ | ⟨g, hgQ, hgext, -⟩
  · exact ⟨N, hN, hcycN, hpN, huN⟩
  · exact absurd ((hmemQ _ (hQT hgQ)).mp hgQ) (hext g (hQT hgQ) hgext)

omit [Finite H] in
theorem not_mem_commutator_of_normal {N : Subgroup H} [N.Normal] (hN : IsCyclic (H ⧸ N))
    {u : H} (huN : u ∉ N) : u ∉ commutator H := by
  intro hu
  apply huN
  have hle : commutator H ≤ N := by
    rw [commutator_def, commutator_le]
    intro g₁ _ g₂ _
    have hcomm : (QuotientGroup.mk' N g₁) * QuotientGroup.mk' N g₂ =
        QuotientGroup.mk' N g₂ * QuotientGroup.mk' N g₁ :=
      (IsCyclic.commGroup (α := H ⧸ N)).mul_comm _ _
    have h1 : QuotientGroup.mk' N ⁅g₁, g₂⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact hle hu

end X11

end CFSG.ComponentClassification.GSThmB
