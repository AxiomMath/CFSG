module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Cover
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits

universe u

theorem spinMinus6_noCover_pPrime {F : Type} [Field F] {p f : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) (h5 : 5 ≤ Nat.card F) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoCover.{u} (fun n => Odd n ∧ ¬ p ∣ n) (spinGroup (quadMinus 3 F b c)) := by
  intro E _ _ _ π hπ hcen hQ
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ hp.out.ne_zero)
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hk : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hk
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h5)
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) p :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective p
  have hdiv : ∀ m n : ℕ, m ∣ n → (Odd n ∧ ¬ p ∣ n) → (Odd m ∧ ¬ p ∣ m) :=
    fun m n hmn ⟨ho, hn⟩ => ⟨ho.of_dvd_nat hmn, fun h => hn (h.trans hmn)⟩
  have hct := minusDatum_isCTGroupDatum_three hirr h2
  obtain ⟨σ, hσ⟩ : ∃ σ : spinGroup (quadMinus 3 F b c) →* E, ∀ x, π (σ x) = x := by
    refine (existsUnique_section_of_rankOne_lift (p := p) hct (minusDatum_steinbergExtras 3 hirr)
      (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hcen hQ.2 fun i => ?_).exists
    by_cases hi : i.val + 1 < 3 - 1
    · obtain ⟨ρ', hρ'⟩ := exists_lift_of_noCover (Q := fun n => Odd n ∧ ¬ p ∣ n) hdiv
        (sl2_noCover hp2 hF) π hπ hcen hQ
        ((minusFrame 3 b c).longSL2 (succ_ne_of_lt 3 hi) true false)
      exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
        (rankOne_minusRootGroup_of_lt 3 hirr hi).le fun g => DFunLike.congr_fun hρ' g
    · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras 3 hirr) i
        (shortRels 3 hirr i) (mem_minusRootGroup_single_iff hirr hi)
        (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
        (fun t ht h1 => shortRels_h_eq_one hirr h2 i ht h1) hπ hcen hQ.2
  have htop : σ.range = ⊤ := by
    refine eq_top_of_perfect_of_central hcen (S := σ.range) (Z := π.ker) fun e => ?_
    refine ⟨σ (π e), ⟨_, rfl⟩, (σ (π e))⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  rw [eq_bot_iff]
  intro c' hc'
  obtain ⟨x, rfl⟩ : c' ∈ σ.range := by rw [htop]; trivial
  rw [MonoidHom.mem_ker, hσ] at hc'
  rw [hc', map_one]
  exact Subgroup.one_mem _

end CFSG.ClassicalInvolution.WeakCT
