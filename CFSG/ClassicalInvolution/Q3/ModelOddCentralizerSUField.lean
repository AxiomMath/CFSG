module

public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Open CFSG.ComponentClassification
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem card_sq_of_card_nine {E : Type} (hE : Nat.card E = 9) : Nat.card E = (3 ^ 1) ^ 2 := by
  rw [hE]
  norm_num

section Field

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem sigma_apply (z : E) : unitaryInvolution E 3 1 z = z ^ 3 := by
  rw [unitaryInvolution_apply, pow_one]

theorem sigma_mul_self (z : E) : unitaryInvolution E 3 1 z * z = z ^ 4 := by
  rw [sigma_apply]
  ring

omit [Fact (Nat.Prime 3)] [CharP E 3] in
theorem pow_eight_eq_one (hE : Nat.card E = 9) {z : E} (hz : z ≠ 0) : z ^ 8 = 1 := by
  have : Fintype E := Fintype.ofFinite E
  have h1 := FiniteField.pow_card_sub_one_eq_one z hz
  rwa [← Nat.card_eq_fintype_card, hE] at h1

omit [Finite E] [Fact (Nat.Prime 3)] in
theorem two_ne_zero_of_charP_three : (2 : E) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : E) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff E 3 2).mp h'
  omega

omit [Fact (Nat.Prime 3)] [CharP E 3] in
theorem exists_sq_eq_neg_one (hE : Nat.card E = 9) : ∃ ω : E, ω * ω = -1 := by
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card, hE]
  have := (FiniteField.isSquare_neg_one_iff (F := E)).mpr (by rw [hcard]; norm_num)
  obtain ⟨ω, hω⟩ := this
  exact ⟨ω, hω.symm⟩

theorem pow_four_eq_one_of_norm_eq_one {c : E} (hc : unitaryInvolution E 3 1 c * c = 1) :
    c ^ 4 = 1 := by
  rw [sigma_mul_self] at hc
  exact hc

omit [Fact (Nat.Prime 3)] in
theorem exists_sq_eq_of_pow_four_eq_one (hE : Nat.card E = 9) {c : E} (hc : c ^ 4 = 1) :
    ∃ μ : E, μ * μ = c := by
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card, hE]
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  have hchar : ringChar E ≠ 2 := by
    rw [ringChar.eq E 3]
    omega
  have := (FiniteField.isSquare_iff hchar hc0).mpr (by rw [hcard]; simpa using hc)
  obtain ⟨μ, hμ⟩ := this
  exact ⟨μ, hμ.symm⟩

end Field

section OddCore

variable {E : Type} [Field E] [Finite E] [Fact (Nat.Prime 3)] [CharP E 3]

theorem subsingleton_suid_of_le_one' {m : ℕ} (hm : m ≤ 1) :
    Subsingleton (SUid (unitaryInvolution E 3 1) m) := by
  have := subsingleton_specialLinear_of_le_one (F := E) hm
  exact (CFSG.ClassicalInvolution.Models.suToSL_injective
    (σ := unitaryInvolution E 3 1) (n := m)).subsingleton

theorem componentOddCore_suid_eq_bot (hE : Nat.card E = 9) (m : ℕ) :
    componentClassificationOddCore (SUid (unitaryInvolution E 3 1) m) = ⊥ := by
  have hE' := card_sq_of_card_nine hE
  rcases Nat.lt_or_ge m 3 with h | h
  · interval_cases m
    · have := subsingleton_suid_of_le_one' (E := E) (m := 0) (by omega)
      exact Subsingleton.elim _ _
    · have := subsingleton_suid_of_le_one' (E := E) (m := 1) (by omega)
      exact Subsingleton.elim _ _
    · obtain ⟨e⟩ := CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two
        (K := E) (p := 3) (f := 1) hE'
      have hfix : Nat.card (CFSG.LieType.Steinberg.fixedSubfield E 3 1) = 3 := by
        rw [CFSG.LieType.Steinberg.card_fixedSubfield hE', pow_one]
      have h1 := OddCore.equiv_invariant e
      rw [componentOddCore_sl2_eq_bot hfix] at h1
      simpa using h1.symm
  · have hnq : (m, 3 ^ 1) ≠ (3, 2) := fun h' => by
      have := congrArg Prod.snd h'
      simp only at this
      omega
    have hq' := isQuasisimple_statedSU_of_card (F := E) (p := 3) (f := 1) hE' h hnq
    let e : SUid (unitaryInvolution E 3 1) m ≃* StatedSU m (3 ^ 1) E :=
      MulEquiv.subgroupCongr (SUid_eq_statedSU hE' m)
    refine componentOddCore_eq_bot_of_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
        (isQuasisimple_of_mulEquiv e.symm hq'.1)) ?_
    refine (CenterExp.of_mulEquiv e (k := 3) ?_).isPGroup
    intro z hz
    rw [hq'.2] at hz
    exact Subtype.ext (by
      simpa using pow_eq_one_of_mem_statedScalars (k := 3)
        (by rw [hE]; norm_num) (Subgroup.mem_subgroupOf.mp hz))

omit [Fact (Nat.Prime 3)] [CharP E 3] in
theorem componentOddCore_specialLinear_of_card_nine (hE : Nat.card E = 9) (m : ℕ) :
    componentClassificationOddCore SL(m, E) = ⊥ := by
  rcases Nat.lt_or_ge m 3 with hk | hk
  · interval_cases m
    · have := subsingleton_specialLinear_of_le_one (F := E) (a := 0) (by omega)
      exact Subsingleton.elim _ _
    · have := subsingleton_specialLinear_of_le_one (F := E) (a := 1) (by omega)
      exact Subsingleton.elim _ _
    · exact componentOddCore_eq_bot_of_isQuasisimple
        (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two (by rw [hE]; norm_num))
        (isPGroup_center_specialLinear_of_card (k := 3) (by rw [hE]; norm_num) (by norm_num))
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact componentOddCore_eq_bot_of_isQuasisimple
      (CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
        (CFSG.LieType.Universal.SpecialLinear.isQuasisimple k E (by omega)))
      (isPGroup_center_specialLinear_of_card (k := 3) (by rw [hE]; norm_num) (by omega))

end OddCore

end CFSG.ClassicalInvolution.Q3
