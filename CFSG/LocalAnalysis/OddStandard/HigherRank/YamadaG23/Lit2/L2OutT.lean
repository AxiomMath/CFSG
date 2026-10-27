module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)

theorem l2out_onCenterQuotient_sq {H : Type} [Group H] (τ : H ≃* H) (hτ : ∀ x, τ (τ x) = x) :
    onCenterQuotient τ ^ 2 = 1 := by
  ext s
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center H) s
  rw [sq, MulAut.mul_apply, onCenterQuotient_apply_mk, onCenterQuotient_apply_mk, hτ]
  rfl

theorem l2out_not_solvable_T {H : Type} [Group H] [Finite H] (τ : H ≃* H)
    (Q : Subgroup (H ⧸ center H)) (hQ : Group.IsPerfect Q) (hev : Even (Nat.card Q))
    (hfix : ∀ s ∈ Q, onCenterQuotient τ s = s) :
    ¬ Group.IsSolvable ↥(litTSub τ (center H)) := by
  intro hT
  have hRT : Q.comap (QuotientGroup.mk' (center H)) ≤ litTSub τ (center H) := by
    intro x hx
    have h1 : QuotientGroup.mk' (center H) (τ x) = QuotientGroup.mk' (center H) x := by
      rw [← onCenterQuotient_apply_mk]
      exact hfix _ hx
    have h2 : τ x * x⁻¹ ∈ (QuotientGroup.mk' (center H)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rwa [QuotientGroup.ker_mk'] at h2
  haveI : Group.IsSolvable ↥(Q.comap (QuotientGroup.mk' (center H))) :=
    solvable_of_solvable_injective (Subgroup.inclusion_injective hRT)
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(Q.comap (QuotientGroup.mk' (center H))) →* Q,
      Function.Surjective φ := by
    refine ⟨((QuotientGroup.mk' (center H)).comp (Subgroup.subtype _)).codRestrict Q
      (fun x => x.2), fun y => ?_⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center H) (y : H ⧸ center H)
    exact ⟨⟨x, by rw [Subgroup.mem_comap, hx]; exact y.2⟩, Subtype.ext hx⟩
  haveI : Group.IsSolvable Q := solvable_of_surjective hφ
  haveI := hQ
  by_cases hnt : Nontrivial Q
  · exact Group.IsPerfect.not_isSolvable Q ‹_›
  · haveI : Subsingleton Q := not_nontrivial_iff_subsingleton.mp hnt
    have h1 : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [h1] at hev
    exact absurd hev (by decide)

end CFSG.OddStandard.HigherRank.YamadaG23
