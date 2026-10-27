module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModACore

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup Equiv

theorem modA_dihedral : ∃ a b : alternatingGroup (Fin 6), a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧
    b ≠ 1 ∧ (a * b) ^ 5 = 1 ∧ a * b ≠ 1 := by
  refine ⟨⟨swap 1 4 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨swap 1 4 * swap 2 3 * (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4),
      Perm.mem_alternatingGroup.2 (by decide)⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V ≃ₗ[ZMod 2] V}

theorem modA_rk_involution_two (B : A6Base J a) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ J, Stable g M) (g : J) (hg2 : g * g = 1)
    (hg1 : g ≠ 1) : rk (modA_resJ J M sM g) = 2 := by
  haveI := modA_finite B
  obtain ⟨e⟩ := B.iso
  have hinj := modA_resJ_injective B hM sM
  set r := modA_resJ J M sM
  have hr2 : ∀ u : J, u * u = 1 → r u * r u = 1 := fun u hu => by rw [← map_mul, hu, map_one]
  have hr1 : ∀ u : J, u ≠ 1 → r u ≠ 1 := fun u hu h => hu (hinj (by rw [h, map_one]))
  have hle : ∀ u : J, u * u = 1 → 2 * rk (r u) ≤ 4 := fun u hu => by
    have := two_mul_rk_le (r u) (hr2 u hu)
    rwa [hM] at this
  have hpos : ∀ u : J, u ≠ 1 → rk (r u) ≠ 0 := fun u hu h0 => hr1 u hu (modA_eq_one_of_rk_zero h0)
  have h2 := hle g hg2
  have h0 := hpos g hg1
  by_contra hne
  have hone : rk (r g) = 1 := by omega
  have hall : ∀ u : J, u * u = 1 → u ≠ 1 → rk (r u) = 1 := by
    intro u hu2 hu1
    obtain ⟨h, hh⟩ := A6_involutions_conj e hg2 hu2 hg1 hu1
    rw [← hh, map_mul, map_mul, map_inv, rk_conj, hone]
  obtain ⟨a₁, b₁, ha2, hb2, ha1, hb1, h5, h51⟩ := modA_dihedral
  obtain ⟨u₁, hu₁⟩ := e.surjective a₁
  obtain ⟨u₂, hu₂⟩ := e.surjective b₁
  have hu₁2 : u₁ * u₁ = 1 := e.injective (by rw [map_mul, hu₁, ha2, map_one])
  have hu₂2 : u₂ * u₂ = 1 := e.injective (by rw [map_mul, hu₂, hb2, map_one])
  have hu₁1 : u₁ ≠ 1 := fun h => ha1 (by rw [← hu₁, h, map_one])
  have hu₂1 : u₂ ≠ 1 := fun h => hb1 (by rw [← hu₂, h, map_one])
  have hu5 : (u₁ * u₂) ^ 5 = 1 :=
    e.injective (by rw [map_pow, map_mul, hu₁, hu₂, h5, map_one])
  have hu51 : u₁ * u₂ ≠ 1 := fun h => h51 (by rw [← hu₁, ← hu₂, ← map_mul, h, map_one])
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf (r u₁ * r u₂) = 5 := by
    rw [← map_mul]
    apply orderOf_eq_prime
    · rw [← map_pow, hu5, map_one]
    · exact hr1 _ hu51
  exact orderOf_mul_ne_five (hr2 u₁ hu₁2) (hr2 u₂ hu₂2) (hall u₁ hu₁2 hu₁1)
    (hall u₂ hu₂2 hu₂1) hord

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
