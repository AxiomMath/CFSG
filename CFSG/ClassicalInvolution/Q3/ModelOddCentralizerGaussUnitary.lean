module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerPSLComplex

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open CFSG.ComponentClassification
  CFSG.Assembly.LowTwoRank

section Field

variable {F : Type} [Field F] [Finite F] [hF3 : Fact (Nat.card F = 3)]

instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

instance fact_not_isSquare_neg_one : Fact (¬ IsSquare (-1 : F)) :=
  ⟨not_isSquare_neg_one_of_card_eq_three hF3.out⟩

theorem charP_of_card_eq_three : CharP F 3 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF3.out)

instance charP_gaussField : CharP (GaussField F) 3 := by
  have := charP_of_card_eq_three (F := F)
  exact charP_of_injective_ringHom (f := algebraMap F (GaussField F))
    (fun x y h => by simpa using congrArg QuadraticAlgebra.re h) 3

theorem card_gaussField_sq : Nat.card (GaussField F) = (3 ^ 1) ^ 2 := by
  rw [card_gaussField_eq_nine hF3.out]
  norm_num

theorem gauss_pow_three (z : GaussField F) : z ^ 3 = ⟨z.re, -z.im⟩ := by
  have := charP_of_card_eq_three (F := F)
  have : Fintype F := Fintype.ofFinite F
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hpow : ∀ a : F, a ^ 3 = a := fun a => by
    have := FiniteField.pow_card a
    rwa [← Nat.card_eq_fintype_card, hF3.out] at this
  have hz : z ^ 3 = z * z * z := by ring
  rw [hz]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (hpow z.re) - (z.re * z.im ^ 2) * h3
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    linear_combination (z.re ^ 2 * z.im) * h3 - (hpow z.im)

noncomputable abbrev gaussSigma : GaussField F ≃+* GaussField F :=
  unitaryInvolution (GaussField F) 3 1

theorem gaussSigma_apply (z : GaussField F) : gaussSigma (F := F) z = ⟨z.re, -z.im⟩ := by
  rw [unitaryInvolution_apply, pow_one, gauss_pow_three]

theorem subsingleton_suid_of_le_one {m : ℕ} (hm : m ≤ 1) :
    Subsingleton (SUid (gaussSigma (F := F)) m) := by
  have := subsingleton_specialLinear_of_le_one (F := GaussField F) hm
  exact (CFSG.ClassicalInvolution.Models.suToSL_injective
    (σ := gaussSigma (F := F)) (n := m)).subsingleton

theorem componentOddCore_su_eq_bot (m : ℕ) :
    componentClassificationOddCore (SUid (gaussSigma (F := F)) m) = ⊥ := by
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m
    · have := subsingleton_suid_of_le_one (F := F) (m := 0) (by omega)
      exact Subsingleton.elim _ _
    · have := subsingleton_suid_of_le_one (F := F) (m := 1) (by omega)
      exact Subsingleton.elim _ _
    · obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two
        (K := GaussField F) (p := 3) (f := 1) card_gaussField_sq
      have hfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield (GaussField F) 3 1) = 3 := by
        rw [CFSG.LieType.Steinberg.card_fixedSubfield card_gaussField_sq, pow_one]
      have h1 := OddCore.equiv_invariant e
      rw [componentOddCore_sl2_eq_bot hfix] at h1
      simpa using h1.symm
  · have hnq : (m, 3 ^ 1) ≠ (3, 2) := fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega
    have hq' := isQuasisimple_statedSU_of_card (F := GaussField F) (p := 3) (f := 1)
      card_gaussField_sq h hnq
    let e : SUid (gaussSigma (F := F)) m ≃* StatedSU m (3 ^ 1) (GaussField F) :=
      MulEquiv.subgroupCongr (SUid_eq_statedSU card_gaussField_sq m)
    refine componentOddCore_eq_bot_of_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
        (isQuasisimple_of_mulEquiv e.symm hq'.1)) ?_
    refine (CenterExp.of_mulEquiv e (k := 3) ?_).isPGroup
    intro z hz
    rw [hq'.2] at hz
    exact Subtype.ext (by
      simpa using pow_eq_one_of_mem_statedScalars (k := 3)
        (by rw [card_gaussField_eq_nine hF3.out]; norm_num) (Subgroup.mem_subgroupOf.mp hz))

end Field

end CFSG.ClassicalInvolution.Q3
