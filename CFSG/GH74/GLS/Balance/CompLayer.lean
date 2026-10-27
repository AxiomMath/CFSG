module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]


variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_pack (H : Subgroup X) :
    ∃ Q : Subgroup X, Q ≤ H ∧ IsPGroup 2 Q ∧
      ∀ T : Subgroup X, T ≤ H → IsPGroup 2 T → Nat.card T ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥H))
  refine ⟨(S : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map H.subtype, fun T hTH hT2 => ?_⟩
  have hT' : IsPGroup 2 (T.subgroupOf H) := hT2.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  have e1 : Nat.card T = Nat.card (T.subgroupOf H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv.symm
  have e2 : Nat.card ((S : Subgroup ↥H).map H.subtype) = Nat.card S :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [e1, e2, Sylow.card_eq_multiplicity S]
  calc Nat.card (T.subgroupOf H) ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    _ = _ := Sylow.card_eq_multiplicity S'

theorem iSup_comps_le_centralizer {S : Set (Subgroup X)} (hS : ∀ K ∈ S, IsComponent K)
    {K₀ : Subgroup X} (hK₀ : IsComponent K₀) (hK₀S : K₀ ∉ S) :
    (⨆ K ∈ S, K) ≤ centralizer (K₀ : Set X) := by
  refine iSup₂_le fun K hK => ?_
  have hne : K ≠ K₀ := fun h => hK₀S (h ▸ hK)
  rcases CFSG.LocalCores.distinct_components_commute (hS K hK) hK₀ with h | h
  · exact absurd h hne
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem exists_layer_element_aux (r : X) :
    ∀ S : Set (Subgroup X), S.Finite → (∀ K ∈ S, IsComponent K) →
      (∀ K ∈ S, ∃ k ∈ K, ∀ y ∈ K, r * y * r⁻¹ = k * y * k⁻¹) →
      ∃ ℓ ∈ ⨆ K ∈ S, K, ∀ K ∈ S, ∀ y ∈ K, r * y * r⁻¹ = ℓ * y * ℓ⁻¹ := by
  intro S hSfin
  refine Set.Finite.induction_on (motive := fun S _ => (∀ K ∈ S, IsComponent K) →
      (∀ K ∈ S, ∃ k ∈ K, ∀ y ∈ K, r * y * r⁻¹ = k * y * k⁻¹) →
      ∃ ℓ ∈ ⨆ K ∈ S, K, ∀ K ∈ S, ∀ y ∈ K, r * y * r⁻¹ = ℓ * y * ℓ⁻¹) S hSfin ?_ ?_
  · intro _ _
    exact ⟨1, one_mem _, fun K hK => absurd hK (Set.notMem_empty K)⟩
  · intro K₀ S hK₀S hSfin' ih hcomp hin
    obtain ⟨ℓ, hℓ, hℓK⟩ := ih (fun K hK => hcomp K (Set.mem_insert_of_mem _ hK))
      (fun K hK => hin K (Set.mem_insert_of_mem _ hK))
    obtain ⟨k₀, hk₀, hk₀K⟩ := hin K₀ (Set.mem_insert _ _)
    have hK₀c : IsComponent K₀ := hcomp K₀ (Set.mem_insert _ _)
    have hSc : ∀ K ∈ S, IsComponent K := fun K hK => hcomp K (Set.mem_insert_of_mem _ hK)
    have hℓC : ℓ ∈ centralizer (K₀ : Set X) := iSup_comps_le_centralizer hSc hK₀c hK₀S hℓ
    have hℓK₀ : ∀ y ∈ K₀, ℓ * y = y * ℓ := fun y hy =>
      (mem_centralizer_iff.mp hℓC y hy).symm
    refine ⟨ℓ * k₀, ?_, ?_⟩
    · have hle : (⨆ K ∈ S, K) ≤ ⨆ K ∈ insert K₀ S, K :=
        iSup₂_le fun K hK => le_iSup₂ (f := fun K (_ : K ∈ insert K₀ S) => K) K
          (Set.mem_insert_of_mem _ hK)
      have h1 : ℓ ∈ ⨆ K ∈ insert K₀ S, K := hle hℓ
      have h2 : k₀ ∈ ⨆ K ∈ insert K₀ S, K :=
        (le_iSup₂ (f := fun K (_ : K ∈ insert K₀ S) => K) K₀ (Set.mem_insert _ _)) hk₀
      exact mul_mem h1 h2
    · intro K hK y hy
      rcases Set.mem_insert_iff.mp hK with rfl | hKS
      ·
        have hy' : k₀ * y * k₀⁻¹ ∈ K := K.mul_mem (K.mul_mem hk₀ hy) (K.inv_mem hk₀)
        calc r * y * r⁻¹ = k₀ * y * k₀⁻¹ := hk₀K y hy
          _ = ℓ * (k₀ * y * k₀⁻¹) * ℓ⁻¹ := by
              rw [hℓK₀ _ hy']; group
          _ = ℓ * k₀ * y * (ℓ * k₀)⁻¹ := by group
      ·
        have hne : K ≠ K₀ := fun h => hK₀S (h ▸ hKS)
        have hk₀C : k₀ ∈ centralizer (K : Set X) := by
          rcases CFSG.LocalCores.distinct_components_commute hK₀c (hSc K hKS) with h | h
          · exact absurd h.symm hne
          · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hk₀
        have hk₀y : k₀ * y = y * k₀ := (mem_centralizer_iff.mp hk₀C y hy).symm
        calc r * y * r⁻¹ = ℓ * y * ℓ⁻¹ := hℓK K hKS y hy
          _ = ℓ * (k₀ * y * k₀⁻¹) * ℓ⁻¹ := by rw [hk₀y]; group
          _ = ℓ * k₀ * y * (ℓ * k₀)⁻¹ := by group

theorem exists_layer_element (r : X) (S : Set (Subgroup X)) (hS : ∀ K ∈ S, IsComponent K)
    (hin : ∀ K ∈ S, ∃ k ∈ K, ∀ y ∈ K, r * y * r⁻¹ = k * y * k⁻¹)
    (hcent : ∀ K : Subgroup X, IsComponent K → K ∉ S → ∀ y ∈ K, r * y = y * r) :
    ∃ ℓ ∈ ⨆ K ∈ S, K, ∀ K : Subgroup X, IsComponent K → ∀ y ∈ K, r * y * r⁻¹ = ℓ * y * ℓ⁻¹ := by
  obtain ⟨ℓ, hℓ, hℓK⟩ := exists_layer_element_aux r S (Set.toFinite S) hS hin
  refine ⟨ℓ, hℓ, fun K hK y hy => ?_⟩
  by_cases hKS : K ∈ S
  · exact hℓK K hKS y hy
  · have hℓC : ℓ ∈ centralizer (K : Set X) := iSup_comps_le_centralizer hS hK hKS hℓ
    have h1 : ℓ * y = y * ℓ := (mem_centralizer_iff.mp hℓC y hy).symm
    have h2 := hcent K hK hKS y hy
    calc r * y * r⁻¹ = (y * r) * r⁻¹ := by rw [h2]
      _ = y := by group
      _ = ℓ * y * ℓ⁻¹ := by rw [h1]; group


end CFSG.GH74.GLS.Balance
