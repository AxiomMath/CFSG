module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

theorem ker_le_of_simple {G : Type} [Group G] {K M : Subgroup G}
    {ψ : ↥K →* alternatingGroup (Fin 5)} (hsurj : Function.Surjective ψ)
    (hker : ∀ l : ↥K, ψ l = 1 ↔ (l : G) ∈ M) {X : Type} (ρ : ↥K →* Perm X)
    (hMρ : ∀ l : ↥K, (l : G) ∈ M → ρ l = 1) (hnt : ∃ l : ↥K, ρ l ≠ 1) :
    ∀ l : ↥K, ρ l = 1 → (l : G) ∈ M := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI hN : (ρ.ker.map ψ).Normal := Subgroup.Normal.map inferInstance ψ hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρ.ker.map ψ) with h | h
  · intro l hl
    have hmem : ψ l ∈ ρ.ker.map ψ := Subgroup.mem_map_of_mem ψ hl
    rw [h, Subgroup.mem_bot] at hmem
    exact (hker l).mp hmem
  · exfalso
    obtain ⟨l, hl⟩ := hnt
    have hmem : ψ l ∈ ρ.ker.map ψ := by rw [h]; trivial
    obtain ⟨n, hn, hnl⟩ := hmem
    have h1 : ψ (n⁻¹ * l) = 1 := by rw [map_mul, map_inv, hnl, inv_mul_cancel]
    have h2 : ρ (n⁻¹ * l) = 1 := hMρ _ ((hker _).mp h1)
    have hn' : ρ n = 1 := hn
    apply hl
    have h3 : ρ l = ρ n * ρ (n⁻¹ * l) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h3, h2, hn', mul_one]

theorem even_surj_of_ker {K : Type*} [Group K] [Finite K] (ρ : K →* Perm (Fin 5))
    (ψ : K →* alternatingGroup (Fin 5)) (hψ : Function.Surjective ψ)
    (hker : ∀ l, ρ l = 1 ↔ ψ l = 1) :
    (∀ l, sign (ρ l) = 1) ∧ ∀ g : Perm (Fin 5), sign g = 1 → ∃ l, ρ l = g := by
  have hkerEq : ρ.ker = ψ.ker := by
    ext l
    exact hker l
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have h2 := Subgroup.card_ker_mul_card_of_surjective hψ
  rw [hkerEq] at h1
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h3 : Nat.card ρ.range = 60 := by
    have h4 : Nat.card ψ.ker * Nat.card ρ.range = Nat.card ψ.ker * 60 := by
      rw [h1, ← h2, hA]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  have hidx : ρ.range.index = 2 := by
    have h := Subgroup.card_mul_index ρ.range
    rw [h3, Nat.card_perm, Nat.card_fin] at h
    norm_num [Nat.factorial] at h
    omega
  have hrange : ρ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx
  refine ⟨fun l => ?_, fun g hg => ?_⟩
  · have hl : ρ l ∈ ρ.range := ⟨l, rfl⟩
    rw [hrange] at hl
    exact Equiv.Perm.mem_alternatingGroup.mp hl
  · have hg' : g ∈ ρ.range := by
      rw [hrange]
      exact Equiv.Perm.mem_alternatingGroup.mpr hg
    exact hg'

end CFSG.EvenSporadicStandard.HNRecog.Section4
