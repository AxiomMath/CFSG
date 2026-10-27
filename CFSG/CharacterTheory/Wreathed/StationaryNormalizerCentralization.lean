module

public import CFSG.CharacterTheory.Semidihedral.StationaryOddLocalization

public section

namespace CFSG.Wreathed.StationaryNormalizerCentralization

open scoped Pointwise
open CFSG.Wreathed.OriginalSylowNormalizerWitness CFSG.Semidihedral.StationaryOddLocalization

universe u

variable {G : Type u} [Group G]

theorem sup_eq_of_mul_eq {H O C : Subgroup G} (hOH : O ≤ H) (hCH : C ≤ H)
    (h : (O : Set G) * (C : Set G) = H) : O ⊔ C = H := by
  apply le_antisymm (sup_le hOH hCH)
  intro g hg
  have hg' : g ∈ (O : Set G) * (C : Set G) := by
    rw [h]
    exact hg
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hg'
  exact Subgroup.mul_mem_sup ha hb

theorem ambientOddCore_eq_pPrimeCore (H : Subgroup G) :
    ambientOddCore H = (CFSG.pPrimeCore 2 H).map H.subtype := by
  rw [ambientOddCore, original_oddCore_eq_twoPrimeCore]

theorem stationary_normalizer_factorizations_force_local_prime_centralization [Finite G]
    (T : Subgroup G) [IsKleinFour T] (x y : G) (hxT : x ∈ T) (hyT : y ∈ T)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y)
    {ell : ℕ} (hell : ell.Prime) (hellodd : Odd ell)
    (P : Subgroup G) (hPp : IsPGroup ell P) (hTP : T ≤ Subgroup.normalizer (P : Set G))
    (hPC : P ≤ Subgroup.centralizer ({x} : Set G))
    (hstationary : ∃ P0 : Sylow ell (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))),
      ((P0 : Subgroup _).map (CFSG.pPrimeCore 2 (Subgroup.normalizer (P : Set G))).subtype).map
        (Subgroup.normalizer (P : Set G)).subtype = P)
    (hfactor : ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P → T ≤ Subgroup.normalizer (U : Set G) →
      (((CFSG.pPrimeCore 2 (Subgroup.normalizer (U : Set G))).map
          (Subgroup.normalizer (U : Set G)).subtype : Subgroup G) : Set G) *
        ((Subgroup.normalizer (U : Set G) ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) :
          Set G) = (Subgroup.normalizer (U : Set G) : Set G)) :
    T = Subgroup.closure ({x, y} : Set G) ∧
      ∀ U : Subgroup G, U ≠ ⊥ → U ≤ P → T ≤ Subgroup.normalizer (U : Set G) →
        ∀ B : Subgroup G, B ≤ Subgroup.normalizer (U : Set G) → IsPGroup ell B →
          x ∈ Subgroup.normalizer (B : Set G) → B ≤ Subgroup.centralizer ({x} : Set G) := by
  have hx : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    omega
  have hy : y ≠ 1 := fun h => by
    rw [h, orderOf_one] at hy2
    omega
  refine ⟨original_four_group_generated_pair T x y hxT hyT hx hy hxy,
    stationary_localization_from_actual_factorizations hell hellodd x hx2 T P hxT hPp hTP hPC
      (stationary_sylow_from_intrinsic_core hell P hstationary) fun U hU hUP hTU => ?_⟩
  rw [ambientOddCore_eq_pPrimeCore]
  exact sup_eq_of_mul_eq (Subgroup.map_subtype_le _) inf_le_left (hfactor U hU hUP hTU)

end CFSG.Wreathed.StationaryNormalizerCentralization
