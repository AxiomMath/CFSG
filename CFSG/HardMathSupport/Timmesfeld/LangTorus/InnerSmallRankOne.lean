module

public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


theorem not_dvd_card_sl2_of_card_le_three {K : Type} [Field K] [Finite K] (hK : Nat.card K ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ Nat.card (SL2 K) := by
  classical
  have := Fintype.ofFinite K
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : Nat.card (SL2 K) =
      ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) / (Fintype.card K - 1) := by
    have := Matrix.card_SL_field (𝔽 := K) 2
    simpa [Fin.prod_univ_two] using this
  rw [Nat.card_eq_fintype_card] at hK h2
  have hv : Nat.card (SL2 K) = 6 ∨ Nat.card (SL2 K) = 24 := by
    rw [hcard]
    interval_cases h : Fintype.card K
    · left; norm_num
    · right; norm_num
  intro hd
  rcases hv with hv | hv <;> rw [hv] at hd
  · have := Nat.le_of_dvd (by norm_num) hd
    have h6 := (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from hd)
    rcases h6 with h | h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
  · have := Nat.le_of_dvd (by norm_num) hd
    have h24 : p ∣ 2 ^ 3 * 3 := hd
    rcases (Nat.Prime.dvd_mul hp).1 h24 with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega

theorem componentRootSpan_le_range_of_rank_one {τ : Tag} {K : Type} [Field K] {M : Type}
    [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i)
    (hrank : ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    componentRootSpan K χ i ≤ (rootSL2 τ K α).range := by
  have hαr : IsRoot τ α := (isRootComponent_componentRoots i).isRoot α hα
  have h := (exceptional_Lang_root_rank_one_torus_transport τ K hαr).1
  change rootSpan τ K (componentRoots χ i) ≤ _
  refine iSup₂_le fun δ hδ => ?_
  change _ ≤ rootRankOneGroup τ K α
  rw [h]
  rcases hrank δ hδ with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem not_dvd_card_componentRootSpan_of_rank_one {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K ≤ 3) {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (componentRootSpan K χ i) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hle := componentRootSpan_le_range_of_rank_one (K := K) i hα (hrank a.1 hα)
  intro hd
  exact not_dvd_card_sl2_of_card_le_three hK hp hp5
    (hd.trans ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd _)))

end CFSG.HardMathSupport.Timmesfeld.LangTorus
