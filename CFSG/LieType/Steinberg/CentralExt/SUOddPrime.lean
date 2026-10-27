module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.RankThree.CentralLiftU.PerfectSplit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUOdd

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg

universe v

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

theorem not_dvd_card_of_isPGroup {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) {A : Type*} [Group A]
    [Finite A] (hA : IsPGroup r A) : ¬ p ∣ Nat.card A := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hA
  rw [hk]
  intro h
  exact hrp ((Nat.prime_dvd_prime_iff_eq hp.out hr).1 (hp.out.dvd_of_dvd_pow h)).symm

theorem exists_rankOne_section_SU_odd
    (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p)
    (h3 : ∀ (R : Type v) [Group R] [Finite R] (ρ : R →* SU σ₀ 3), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center R → IsPGroup r ρ.ker → ∃ s : SU σ₀ 3 →* R, ∀ x, ρ (s x) = x)
    {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n) {E : Type v} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hrk : IsPGroup r π.ker)
    (k : Fin (n / 2)) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne
      (rootGroup σ₀ (unitaryInvolution_involutive hF) n) k) →* E, ∀ g, π (φ g) = g := by
  have hC : ¬ p ∣ Nat.card π.ker := not_dvd_card_of_isPGroup hr hrp hrk
  by_cases hk : k.val + 1 < n / 2
  · set e := rankOneShortEquiv (hσ := unitaryInvolution_involutive hF) hk
    obtain ⟨ρ, hρ, -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC
      ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h1 := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h1
    exact h1
  · obtain ⟨e⟩ := nonempty_rankOne_last_odd_mulEquiv hF ho hn hk
    obtain ⟨ρ, hρ⟩ := CFSG.RankThree.CentralLiftU.exists_lift_of_forall_section_prime h3 hπ hcen
      hrk ((Subgroup.subtype _).comp e.symm.toMonoidHom)
    refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
    have h1 := DFunLike.congr_fun hρ (e g)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype] at h1
    exact h1

theorem su_odd_exists_section_of_prime
    (hF : Nat.card F = (p ^ f) ^ 2) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p)
    (h3 : ∀ (R : Type v) [Group R] [Finite R] (ρ : R →* SU σ₀ 3), Function.Surjective ρ →
      ρ.ker ≤ Subgroup.center R → IsPGroup r ρ.ker → ∃ s : SU σ₀ 3 →* R, ∀ x, ρ (s x) = x)
    {n : ℕ} (hn : 3 ≤ n) (ho : ¬ Even n) {E : Type v} [Group E] [Finite E] {π : E →* SU σ₀ n}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hrk : IsPGroup r π.ker) :
    ∃ s : SU σ₀ n →* E, ∀ x, π (s x) = x := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hC : ¬ p ∣ Nat.card π.ker := not_dvd_card_of_isPGroup hr hrp hrk
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s, hs, -⟩ := existsUnique_section_of_rankOne_lift (D := rootDatum hF n)
    (isCTGroupDatum hF n (by omega) ζ hζ) (steinbergExtras hF n (by omega) ζ hζ)
    (fun γ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (SUExtras.toStd_ne_zero_of_mem_roots hγ)) hπ hcen hC
    (exists_rankOne_section_SU_odd hF hr hrp h3 hn ho hπ hcen hrk)
  exact ⟨s, hs⟩

end CFSG.LieType.Steinberg.CentralExt.SUOdd
