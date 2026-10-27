module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Leaves

variable {ℓ f : ℕ} {E : Type} [Field E] {hE : UnitaryFieldData ℓ f E}
  {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E}

theorem finite_sesqUnitaryGroup' : Finite ↥(sesqUnitaryGroup Hf) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  have : Finite (LinearMap.GeneralLinearGroup E W) := Finite.of_injective _ Units.val_injective
  infer_instance

private theorem eq_one_of_apply_smul_char_two [CharP E 2] (g : LinearMap.GeneralLinearGroup E W)
    (hg : g ^ 2 = 1) (c : E) (hcw : ∀ w, (g : Module.End E W) w = c • w) : g = 1 := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact Units.ext (LinearMap.ext fun w => Subsingleton.elim _ _)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  have h1 : ((g ^ 2 : LinearMap.GeneralLinearGroup E W) : Module.End E W) w = w := by
    rw [hg]
    rfl
  rw [pow_two, Units.val_mul, Module.End.mul_apply, hcw, hcw, smul_smul] at h1
  have h2 : c * c = 1 := smul_left_injective E hw (by simpa using h1)
  have h3 : c = 1 := by
    have h2' : (2 : E) = 0 := by exact_mod_cast CharP.cast_eq_zero E 2
    have h4 : (c - 1) ^ 2 = 0 := by linear_combination h2 + (1 - c) * h2'
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [hcw, h3, one_smul]
  rfl

theorem eq_one_of_commute_special_unitary_of_sq_eq_one (hℓ : ℓ = 2) (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft) (hm : 2 ≤ Module.finrank E W)
    (g : LinearMap.GeneralLinearGroup E W) (hg : g ^ 2 = 1)
    (hc : ∀ δ : LinearMap.GeneralLinearGroup E W, δ ∈ sesqSpecialUnitaryGroup Hf →
      δ * g = g * δ) : g = 1 := by
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : f ≠ 0) hE.prime.one_lt
    omega
  haveI : CharP E 2 := hℓ ▸ hE.charP
  obtain ⟨c, hcw⟩ :=
    CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hE hHf hHfl hm hq
      (g : Module.End E W) fun δ hδ => by
        have h := congrArg Units.val (hc δ hδ)
        rw [Units.val_mul, Units.val_mul] at h
        exact h.symm
  exact eq_one_of_apply_smul_char_two g hg c hcw

theorem dvd_card_special_of_dvd_card (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 2 ≤ Module.finrank E W) {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (sesqUnitaryGroup Hf)) : p ∣ Nat.card (sesqSpecialUnitaryGroup Hf) := by
  obtain ⟨hU, hSU, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := Module.finrank E W) rfl (by omega)
  have hmul : (Nat.card (sesqUnitaryGroup Hf) : ℤ) =
      (((ℓ ^ f : ℕ) : ℤ) + 1) * Nat.card (sesqSpecialUnitaryGroup Hf) := by
    rw [hU, hSU, CFSG.LinearGroups.prod_Icc_one_eq_mul _ (by omega : 1 ≤ Module.finrank E W)]
    ring
  have hdvd : (((ℓ ^ f : ℕ) : ℤ) + 1) ∣ Nat.card (sesqSpecialUnitaryGroup Hf) := by
    rw [hSU]
    refine Dvd.dvd.mul_left ?_ _
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 (Module.finrank E W) := Finset.mem_Icc.mpr ⟨le_rfl, hm⟩
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem
      (fun i : ℕ => ((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) h2)
    exact ⟨((ℓ ^ f : ℕ) : ℤ) - 1, by ring⟩
  have hdvdN : ℓ ^ f + 1 ∣ Nat.card (sesqSpecialUnitaryGroup Hf) := by
    exact_mod_cast hdvd
  have hmulN : Nat.card (sesqUnitaryGroup Hf) =
      (ℓ ^ f + 1) * Nat.card (sesqSpecialUnitaryGroup Hf) := by
    exact_mod_cast hmul
  rw [hmulN] at h
  rcases hp.dvd_mul.mp h with h1 | h1
  · exact h1.trans hdvdN
  · exact h1

theorem natCard_sesqUnitaryGroup_two_two (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hq : ℓ ^ f = 2) (hm : Module.finrank E W = 2) : Nat.card (sesqUnitaryGroup Hf) = 18 := by
  obtain ⟨hcard, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := Module.finrank E W) rfl (by omega)
  rw [hm, hq] at hcard
  have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by decide +kernel
  exact_mod_cast hcard.trans e

theorem natCard_sesqUnitaryGroup_three_two (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hq : ℓ ^ f = 2) (hm : Module.finrank E W = 3) : Nat.card (sesqUnitaryGroup Hf) = 648 := by
  obtain ⟨hcard, -, -, -, -, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := Module.finrank E W) rfl (by omega)
  rw [hm, hq] at hcard
  have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by decide +kernel
  exact_mod_cast hcard.trans e

theorem normal_special_subgroupOf (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 1 ≤ Module.finrank E W) :
    ((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)).Normal := by
  obtain ⟨-, -, -, -, hker, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
    (n := Module.finrank E W) rfl hm
  rw [← hker]
  exact MonoidHom.normal_ker _

theorem isQuasisimple_special_subgroupOf (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (hm : 2 ≤ Module.finrank E W)
    (hq : (Module.finrank E W = 2 → 4 ≤ ℓ ^ f) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ f)) :
    CFSG.IsQuasisimple ↥((sesqSpecialUnitaryGroup Hf).subgroupOf (sesqUnitaryGroup Hf)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le Hf)).symm
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hE hHf
      hHfl hm hq)

end Leaves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
