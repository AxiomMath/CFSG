module

public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.GroupTheory.SmallFixedTwoGroup.TheoremPBound
public import CFSG.GroupTheory.SmallFixedTwoGroup.TheoremPSimple
public import CFSG.GroupTheory.SmallFixedTwoGroup.TheoremPFive

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem nonempty_mulEquiv_alt5_of_inverted_card {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {θ : MulAut G} (hθ : θ * θ = 1)
    (hS : Nat.card G ≤ 4 * Nat.card {g : G // θ g = g⁻¹}) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have h7 : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p ≤ 5 := by
    intro p hp hpG
    by_contra hle
    have hlt : 5 < p := not_le.mp hle
    have hp7 : 7 ≤ p := by
      have hpne6 : p ≠ 6 := fun h6 => by rw [h6] at hp; norm_num at hp
      omega
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
    obtain ⟨hab, hbound⟩ := sylow_abelian_and_index_bound hθ hS (le_of_lt hlt) P
    exact false_of_sylow_index_bound hnab hp7 hpG P hab hbound
  have h5dvd : 5 ∣ Nat.card G := by
    by_contra h5
    have hsub : (Nat.card G).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
      intro q hq
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hqG : q ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hq
      have hq2 : 2 ≤ q := hqprime.two_le
      have hq5 : q ≤ 5 := h7 q hqprime hqG
      have hqne5 : q ≠ 5 := fun h => h5 (h ▸ hqG)
      have hq23 : q = 2 ∨ q = 3 := by
        interval_cases q
        · exact Or.inl rfl
        · exact Or.inr rfl
        · norm_num at hqprime
        · norm_num at hqne5
      rcases hq23 with rfl | rfl <;> simp
    have hcard : (Nat.card G).primeFactors.card ≤ 2 := by
      calc (Nat.card G).primeFactors.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 2 := by decide
    haveI : Group.IsSolvable G :=
      CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two hcard
    have hcomm : ∀ a b : G, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (hcomm a b)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  obtain ⟨hab, hbound⟩ := sylow_abelian_and_index_bound hθ hS (le_refl 5) P
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_eq_sixty_of_sylow_five hnab h5dvd P hab hbound)

theorem nonempty_mulEquiv_alt5_of_fixed_card_le_four {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (τ : MulAut G) (hτ : τ * τ = 1)
    (h4 : Nat.card (fixedSubgroup τ) ≤ 4) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  refine nonempty_mulEquiv_alt5_of_inverted_card hnab hτ ?_
  calc Nat.card G ≤ Nat.card (fixedSubgroup τ) * Nat.card {g : G // τ g = g⁻¹} :=
        card_le_card_fixedSubgroup_mul_card_inverted hτ
    _ ≤ 4 * Nat.card {g : G // τ g = g⁻¹} := Nat.mul_le_mul_right _ h4

end CFSG.GroupTheory.SmallFixedTwoGroup
