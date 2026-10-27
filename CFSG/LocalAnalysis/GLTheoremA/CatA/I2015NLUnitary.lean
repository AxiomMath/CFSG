module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.SignalizerFunctorTheorem.NonLocal.UHeisenberg
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.StandardType.InndiagSU
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.LocalAnalysis.GLTheoremA.MI

section Witness

variable {K : Type} [Field K] [Finite K] {d n : ℕ}

theorem unitary_nlWitness (hd : 3 ≤ d) (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hq2 : ¬(d = 3 ∧ 2 ^ n = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : ¬(d = 3 ∧ n = p))
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hord : orderOf f = p) : NLWitness f := by
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  have hd1 : 1 ≤ d := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin d) K) := isPrimeFormGram_one
  obtain ⟨σ, hfσ⟩ := RecipeFieldSU.congr_field_eq h hd1 hf
  have hσord : orderOf σ = p := by
    have h1 := orderOf_injective (primeFormFieldHom h hC)
      (primeFormFieldHom_injective h d hd hq2) σ
    rw [← h1, ← hfσ]
    exact (MulEquiv.orderOf_eq (MulAut.congr (projEquiv h hd1)) f).trans hord
  obtain ⟨hpn, -⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσord
  have h₀ := fixSubfield_unitaryFieldData h hp hp2 hσord
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσord
  have hq₀ : ¬(d = 3 ∧ 2 ^ (n / p) = 2) := by
    rintro ⟨hd3, h2⟩
    obtain ⟨-, h1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
    exact hq ⟨hd3, by rw [← Nat.div_mul_cancel hpn, h1, one_mul]⟩
  have hinj := subfieldPSU_injective h h₀ hbar d hd1
  let eJ := MonoidHom.ofInjective hinj
  haveI := isSimpleGroup_primeFormP_one h₀ hd hq₀
  have hs : IsSimpleGroup ↥(subfieldPSU h h₀ hbar d).range := eJ.isSimpleGroup_congr.1 inferInstance
  have hna : ∃ x y : ↥(subfieldPSU h h₀ hbar d).range, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    exact not_commute_primeFormP_one h₀ hd hq₀ fun x y =>
      eJ.injective (by rw [map_mul, map_mul]; exact hcon _ _)
  haveI : Finite (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :=
    Finite.of_equiv _ (projEquiv h hd1).toEquiv
  refine nlWitness_of_nonLocalized (projEquiv h hd1) hs hna
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_unitarySubfield h h₀ hbar hd hq₀) ?_
  rintro _ ⟨x, hx, rfl⟩
  have h1 : primeFormFieldHom h hC σ x = x := range_subfieldPSU_le h d h₀ hbar hx
  rw [← hfσ] at h1
  have h2 : projEquiv h hd1 (f ((projEquiv h hd1).symm x)) = x := h1
  change f ((projEquiv h hd1).symm x) = (projEquiv h hd1).symm x
  apply (projEquiv h hd1).injective
  rw [h2, MulEquiv.apply_symm_apply]

end Witness

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnUnitary_holds : I2015NLOnUnitary := by
  intro lab hlab ht
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hr : 2 ≤ r := hlab.2.1
  have hrn : r = 2 → 2 ≤ n := hlab.2.2
  refine atLabelWhen_of_witness hlab ?_ (fun p _ => by simp)
  intro p hp hp2 _ _ _ Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ hbody f hf hord hfinR hJ => ?_⟩
  by_cases hq : r = 2 ∧ n = p
  · exfalso
    obtain ⟨hr2, hnp⟩ := hq
    subst hr2
    obtain ⟨-, D, hD, hdat | hexc'⟩ := hbody f hf hord
    · have hdiv : n / p = 1 := by rw [hnp]; exact Nat.div_self hp.pos
      dsimp only at hdat
      rw [hdiv] at hdat
      haveI := hfinR
      obtain ⟨J, hJ⟩ := hJ
      exact false_of_component_of_solvable hD (FR.Res.solvable_twA21 D hdat) hJ
    · rcases hexc' with ⟨h1, -⟩ | ⟨h1, -⟩ <;> cases h1
  · refine unitary_nlWitness (d := r + 1) (by omega) hn hK ?_ hp hp2
      (fun ⟨h1, h2⟩ => hq ⟨by omega, h2⟩) hf hord
    rintro ⟨h1, h2⟩
    obtain ⟨-, h4⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
    have := hrn (by omega)
    omega

theorem i2015NLOnTwD3_holds : I2015NLOnTwD3 := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_
    (fun p _ h => by rw [ht] at h; exact absurd h.1 (by decide))
  intro p hp hp2 _ _ hC
  obtain ⟨t, r, n⟩ := lab
  dsimp only [regRank] at hC ht
  subst hC
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  simp only [CFSG.Assembly.LargeEvenRawDatum, show ¬((3 : ℕ) = 2) from by decide, if_false,
    if_true] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  refine ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf hord _ _ => ?_⟩
  exact unitary_nlWitness (d := 4) (by norm_num) hn hK (by omega) hp hp2 (by omega) hf hord

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
