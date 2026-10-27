module

public import CFSG.GH74.Uniqueness.Section167Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma167_stepA
    (S : ZDSetup X Z M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup X} (hY : IsPGroup p Y) (h3 : 3 ≤ (omegaFix M (Y : Set X)).ncard) {s : X}
    (hs : s ∈ Z) (hsN : s ∈ normalizer (Y : Set X)) (hsC : ¬ ∀ y ∈ Y, s * y = y * s) :
    (∀ β ∈ omegaFix M (Y : Set X), conjugate β s ≠ β) ∧
      Open.pRank 2 (zHull Z (normalizer (Y : Set X))) ≤ 1 ∧
      (∀ z' ∈ Z, ¬ ∀ y ∈ Y, z' * y = y * z') ∧
      IsZStarIn (normalizer (Y : Set X)) s := by
  have hodd : Odd (Nat.card Y) := odd_card_of_isPGroup hp hp2 hY
  have hfix : ∀ β ∈ omegaFix M (Y : Set X), conjugate β s ≠ β := by
    intro β hβ hsβ
    have hYβ : Y ≤ β := (S.prodDisc.mem_omegaFix_iff.mp hβ).2
    rcases S.theorem4b_omega hs hodd hsN hβ.1 hsβ hYβ with hc | hu
    · exact hsC hc
    · have hsub : omegaFix M (Y : Set X) ⊆ {β} := fun δ hδ => hu δ hδ
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      simp only [Set.ncard_singleton] at this
      omega
  have hrank : Open.pRank 2 (zHull Z (normalizer (Y : Set X))) ≤ 1 := by
    by_contra hge
    push Not at hge
    obtain ⟨β, ⟨hβΩ, hβs⟩, -⟩ := S.prodDisc.existsUnique_fixed_point S.invariant hs
    have hYβ := S.lemma313 hodd hge hs hsN hβΩ hβs
    exact hfix β (S.prodDisc.mem_omegaFix_iff.mpr ⟨hβΩ, hYβ⟩) hβs
  refine ⟨hfix, hrank, ?_, isZStarIn_of_pRank_zHull_le_one S.invariant hrank hs hsN⟩
  intro z' hz' hall
  have hz'N : z' ∈ normalizer (Y : Set X) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr (fun h hh => (hall h hh).symm))
  have hiso : ∀ y ∈ Z, y ∈ normalizer (Y : Set X) → y * s = s * y → y = s := fun y hy hyN hys =>
    eq_of_commute_of_pRank_zHull_le_one S.invariant hrank hy hyN hs hsN hys
  obtain ⟨a, haN, ha⟩ := exists_mem_conj_of_isolated S.invariant hs hsN hiso hz' hz'N
  apply hsC
  intro y hy
  have hay : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp haN y).mp hy
  have hay' : a⁻¹ * y * a ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (Y : Set X)).inv_mem haN) y).mp hy
    simpa using this
  have hz1 := hall _ hay'
  have hsa : s = a * z' * a⁻¹ := by rw [← ha]; group
  calc s * y = a * z' * a⁻¹ * y := by rw [hsa]
    _ = a * (z' * (a⁻¹ * y * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * y * a) * z') * a⁻¹ := by rw [hz1]
    _ = y * (a * z' * a⁻¹) := by group
    _ = y * s := by rw [hsa]

end CFSG.GH74.Uniqueness
