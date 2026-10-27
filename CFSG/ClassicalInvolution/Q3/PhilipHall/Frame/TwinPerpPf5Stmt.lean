module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M7

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

@[expose] def C25_9P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) ≤ 4 ∧
        (Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 →
          ∃ a : G, Subgroup.closure {a, z} =
              (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) ∧
            z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)))

@[expose] def C25_11FourP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a : G,
      Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 →
      Subgroup.closure {a, z} =
        (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) →
      z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)) →
      z ∉ zStarOf (Subgroup.centralizer ({a * z} : Set G)) → False

theorem c25_11_of_9_fourP (h9 : C25_9P) (h4 : C25_11FourP) : C25_11 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨hle, hfour⟩ := h9 G Ω K K' W S R R' z t u₁ u₂ hyp
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hzS : z ∈ (S : Subgroup G) := h.hRS h.hzR.mem
  have hzC : z ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by
    have : R ⊔ R' ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.hzR.commute_of_mem hx).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.hzR'.commute_of_mem hx).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)
  have hzA : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    ⟨hzS, hzC⟩
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact h.hzR.sq) h.hzR.ne_one
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, hzord]
  have hle2 : Subgroup.zpowers z ≤
      (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le).mpr hzA
  have hcard2 : 2 ≤ Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) := by
    have := Subgroup.card_le_of_le hle2
    omega
  have hcases : Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 2 ∨
      Nat.card ↥((S : Subgroup G) ⊓
      Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 4 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp
      (S.isPGroup'.to_le (inf_le_left : (S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ≤ (S : Subgroup G)))
    have hk' : Nat.card ↥((S : Subgroup G) ⊓
        Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)) = 2 ^ k := hk
    clear hk
    have hk3 : k < 3 := by
      by_contra hk3
      have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> omega
  rcases hcases with h2 | h4'
  · exact (Subgroup.eq_of_le_of_card_ge hle2 (by rw [hz2, h2])).symm
  · exfalso
    obtain ⟨a, hcl, hz1, hz2'⟩ := hfour h4'
    exact h4 G Ω K K' W S R R' z t u₁ u₂ hyp a h4' hcl hz1 hz2'

end Asc77

end CFSG.ClassicalInvolution.Q8P
