module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRSix
public import CFSG.ClassicalInvolution.Asc77.AscT7DRCoord

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2
open scoped commutatorElement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ s t' : G, s ∈ (S : Subgroup G) ∧ t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧
          conjSub t' R = R' ∧ s * s = 1 ∧ s * t' = t' * s ∧ conjSub s R = R ∧
          (∃ r ∈ R, ⁅s, r⁆ ∉ T7DR.squaresSub R) ∧
          Subgroup.closure (((R ⊔ R' : Subgroup G) : Set G) ∪ {s, t'}) = (S : Subgroup G)

theorem c25_20_coord_of (h : C25_20 p f) : C25_20_coord p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨s, t', hsS, ht'S, hg, hconj, hs2, hst, hsR, hnt, hgen⟩ :=
    h G Ω K K' W S R R' z t u₁ u₂ hyp h4
  have hsetting : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hp : p ≠ 2 := hsetting.stand.odd
  have hquat : IsQuatSub R := hsetting.stand.hyp.isQuatSub_of_mem_RSet hp hyp.hR.1
  have hsR' : ∀ r ∈ R, s * r * s⁻¹ ∈ R := fun r hr => by
    have := conj_mem_conjSub (n := s) hr
    rwa [hsR] at this
  obtain ⟨a, b, haR, hbR, hclos, hbab, hk, hsa, hsb⟩ := T7DR.exists_coord hquat hs2 hsR' hnt
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hSclos : Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hRS haR
      · exact hRS hbR
      · exact hsS
      · exact ht'S
    · rw [← hgen, Subgroup.closure_le]
      have hRc : R ≤ Subgroup.closure ({a, b, s, t'} : Set G) := by
        rw [← hclos]
        exact Subgroup.closure_mono (fun x hx => by
          rcases hx with rfl | hx
          · simp
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            simp)
      have ht'c : t' ∈ Subgroup.closure ({a, b, s, t'} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hsc : s ∈ Subgroup.closure ({a, b, s, t'} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hR'c : R' ≤ Subgroup.closure ({a, b, s, t'} : Set G) := by
        intro x hx
        have hx' : x ∈ conjSub t' R := by rw [hconj]; exact hx
        rw [mem_conjSub_iff] at hx'
        have h1 := hRc hx'
        have : x = t' * (t'⁻¹ * x * t') * t'⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'c h1) (Subgroup.inv_mem _ ht'c)
      rintro x (hx | hx)
      · exact (sup_le hRc hR'c) hx
      · rcases hx with rfl | hx
        · exact hsc
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ht'c
  exact ⟨a, b, s, t', haR, hbR, hclos, hbab, hk, hsS, ht'S, hg, hconj, hSclos, hs2, hst, hsa, hsb⟩

theorem c25_21_of_sylow (h20 : C25_20 p f) : C25_21 p f :=
  c25_21_of_sylow_coord p f (c25_20_coord_of p f h20)

end CFSG.ClassicalInvolution.Asc77
