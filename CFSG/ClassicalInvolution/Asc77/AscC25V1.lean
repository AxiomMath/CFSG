module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Trans

public section

namespace CFSG.ClassicalInvolution.Asc77.C25V

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hom_eq_one_of_simple_of_commGroup [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    {A : Type*} [CommGroup A] (ψ : G →* A) : ψ = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    apply ψ.ker_eq_bot_iff.mp h
    rw [map_mul, map_mul, mul_comm]
  · ext g
    have : g ∈ ψ.ker := h ▸ Subgroup.mem_top g
    simpa using this

theorem transfer_trivial_of_fusion [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    {A : Type*} [CommGroup A] (ϕ : H →* A) (a : G) (haH : a ∈ H) (ha2 : a * a = 1)
    (hfus : ∀ (x : G) (hx : x⁻¹ * a * x ∈ H), ϕ ⟨x⁻¹ * a * x, hx⟩ = ϕ ⟨a, haH⟩) :
    ϕ ⟨a, haH⟩ = 1 := by
  classical
  by_contra hne
  set c : A := ϕ ⟨a, haH⟩ with hc
  have hc2 : c ^ 2 = 1 := by
    have h1 : (⟨a, haH⟩ : H) * ⟨a, haH⟩ = 1 := Subtype.ext ha2
    rw [hc, pow_two, ← map_mul, h1, map_one]
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hne
    have : (⟨1, haH⟩ : H) = 1 := rfl
    rw [hc, this, map_one]
  have hord : orderOf a = 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
  have hT := T7F2.transfer_eq_pow_index ϕ a 1 hord c hc2 hfus (fun i x hx => by
    have h1 : a ^ (2 ^ (i + 1)) = 1 := by
      rw [pow_succ', pow_mul, pow_two, ha2, one_pow]
    have h2 : (⟨x⁻¹ * a ^ (2 ^ (i + 1)) * x, hx⟩ : H) = 1 := by
      apply Subtype.ext
      simp [h1]
    rw [h2, map_one])
  have hodd : Odd H.index := by
    have h2 : ¬ 2 ∣ H.index := fun hd =>
      S.not_dvd_index (hd.trans (Subgroup.index_dvd_of_le hSH))
    rw [Nat.odd_iff]
    omega
  have hone : ϕ.transfer a = 1 := by
    have := hom_eq_one_of_simple_of_commGroup hnc ϕ.transfer
    exact congrArg (fun f => f a) this
  rw [hone] at hT
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_succ, pow_mul, hc2, one_pow, one_mul] at hT
  exact hne hT.symm

theorem false_of_transfer_fusion [IsSimpleGroup G] (hnc : ∃ x y : G, x * y ≠ y * x)
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    {A : Type*} [CommGroup A] (ϕ : H →* A) (a : G) (haH : a ∈ H) (ha2 : a * a = 1)
    (hfus : ∀ (x : G) (hx : x⁻¹ * a * x ∈ H), ϕ ⟨x⁻¹ * a * x, hx⟩ = ϕ ⟨a, haH⟩)
    (hne : ϕ ⟨a, haH⟩ ≠ 1) : False :=
  hne (transfer_trivial_of_fusion hnc S H hSH ϕ a haH ha2 hfus)

end CFSG.ClassicalInvolution.Asc77.C25V
