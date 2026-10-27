module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinG
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Asc77.S28 (SameOrOrth fund_central_involution
  mem_center_of_map_commutes)
open scoped MatrixGroups commutatorElement


theorem commutator_top_of_isPerfect {X : Type} [Group X] (h : Group.IsPerfect X) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
  have := h.commutator_eq_top
  rwa [_root_.commutator_def] at this

section Images

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem twin_images3 {X : Type} [Group X] (π : X →* (V ≃ₗ[F] V)) (hodd : Odd (Nat.card F))
    {𝓕 : Set (Subgroup X)} {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 π 𝓕 (fundSet Q) Z') {R R' : Subgroup X} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hne : R ≠ R') (hc : Commutes R R')
    (hnb : ∀ S ∈ 𝓕, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) {r r' : X}
    (hrR : r ∈ R) (hr'R' : r' ∈ R') (hr2 : r * r = 1) (hr'2 : r' * r' = 1) (hr1 : π r ≠ 1)
    (hr'1 : π r' ≠ 1) :
    ∃ i i' : V ≃ₗ[F] V, IsFundamental Q (R.map π) i ∧ IsFundamental Q (R'.map π) i' ∧
      π r = i ∧ π r' = i' ∧ IsTwinPair (fundSet Q) (R.map π) (R'.map π) := by
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  obtain ⟨i', hi'⟩ := cq.map_mem R' hR'
  have hπr : orderOf (π r) = 2 :=
    orderOf_eq_prime (by rw [_root_.sq, ← map_mul, hr2, map_one]) hr1
  have hπr' : orderOf (π r') = 2 :=
    orderOf_eq_prime (by rw [_root_.sq, ← map_mul, hr'2, map_one]) hr'1
  refine ⟨i, i', hi, hi', hi.eq_of_orderOf_eq_two hodd (Subgroup.mem_map_of_mem π hrR) hπr,
    hi'.eq_of_orderOf_eq_two hodd (Subgroup.mem_map_of_mem π hr'R') hπr', ?_⟩
  refine ⟨cq.map_mem R hR, cq.map_mem R' hR', fun h => hne (cq.map_inj hR hR' h), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · intro S' hS' h0 h1
    obtain ⟨S, hS, rfl⟩ := cq.surj S' hS'
    have key : ∀ T ∈ 𝓕, (S.map π = T.map π ∨ Commutes (S.map π) (T.map π)) ↔
        (S = T ∨ Commutes S T) := by
      intro T hT
      constructor
      · rintro (h | h)
        · exact Or.inl (cq.map_inj hS hT h)
        · exact Or.inr ((cq.commutes_iff hS).mp h)
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr ((cq.commutes_iff hS).mpr h)
    have h := (key R hR).trans ((hnb S hS).trans (key R' hR').symm)
    rwa [or_iff_right h0, or_iff_right h1] at h

end Images

section Orth

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem twinProductCentral_orth3 {X : Type} [Group X] (hodd : Odd (Nat.card F))
    (π : X →* (V ≃ₗ[F] V)) {𝓕 : Set (Subgroup X)} {Z' : Subgroup (V ≃ₗ[F] V)}
    (cq : Q3W.CentralQuot3 π 𝓕 (fundSet Q) Z')
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hsl : ∀ R ∈ 𝓕, Nonempty (R ≃* SL(2, F))) (hsame : SameOrOrth Q) :
    ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, R ≠ R' → Commutes R R' →
      (∀ S ∈ 𝓕, (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) →
      ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
      ∀ r' ∈ R', (∀ s ∈ R', r' * s = s * r') → r' ≠ 1 → r * r' ∈ Subgroup.center X := by
  intro R hR R' hR' hne hc hnb r hrR hrc hr1 r' hr'R hr'c hr'1
  obtain ⟨eR⟩ := hsl R hR
  obtain ⟨eR'⟩ := hsl R' hR'
  obtain ⟨ord, -⟩ := fund_central_involution hodd eR hrR hrc hr1
  obtain ⟨ord', -⟩ := fund_central_involution hodd eR' hr'R hr'c hr'1
  have hr2 : r * r = 1 := by
    have := pow_orderOf_eq_one r
    rwa [ord, _root_.sq] at this
  have hr'2 : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [ord', _root_.sq] at this
  have hπ1 : π r ≠ 1 := fun h => hr1 (cq.inj R hR r hrR h)
  have hπ1' : π r' ≠ 1 := fun h => hr'1 (cq.inj R' hR' r' hr'R h)
  obtain ⟨i, i', hi, hi', hπr, hπr', hTP⟩ :=
    twin_images3 π hodd cq hR hR' hne hc hnb hrR hr'R hr2 hr'2 hπ1 hπ1'
  rcases hsame _ _ i i' hi hi' hTP with h | h
  · have : π (r * r') = 1 := by rw [map_mul, hπr, hπr', h, hi.mul_self]
    exact cq.ker_le (MonoidHom.mem_ker.mpr this)
  · refine mem_center_of_map_commutes π cq.ker_le hX fun g => ?_
    rw [map_mul, hπr, hπr']
    exact ((Subgroup.mem_center_iff.mp h) (π g)).symm

end Orth

end CFSG.ClassicalInvolution.Q3.Q3TIV
