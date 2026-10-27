module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.SignalizerFunctorTheorem.NonLocal.SpMain
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

section Witness

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem sympSimpleNonabelianRange (hr : 2 ≤ r) (σ : K ≃+* K)
    (hk : ¬ (r = 2 ∧ Nat.card (descentField σ) = 2)) :
    IsSimpleGroup (KCSpComm.subfieldProj (r := r) σ).range ∧
      ∃ x y : (KCSpComm.subfieldProj (r := r) σ).range, x * y ≠ y * x := by
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨hs, hperf⟩ := KCSpComm.simple_perfect_statedProj (k := descentField σ) hr hk
  rw [← KCSpComm.range_subfieldInj]
  let e := MonoidHom.ofInjective (KCSpComm.subfieldInj_injective (r := r) σ)
  refine ⟨e.symm.isSimpleGroup, ?_⟩
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ a b : StatedProj (StatedSp r (descentField σ)), a * b = b * a :=
    fun a b => e.injective (by rw [map_mul, map_mul]; exact hcon _ _)
  haveI : Nontrivial (StatedProj (StatedSp r (descentField σ))) := hs.toNontrivial
  haveI : IsMulCommutative (StatedProj (StatedSp r (descentField σ))) :=
    isMulCommutative_iff.mpr hcomm
  exact Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp r (descentField σ))) ‹_›

theorem sympNLWitness_fieldAut (hr : 2 ≤ r) (σ : K ≃+* K)
    (hk : ¬ (r = 2 ∧ Nat.card (descentField σ) = 2)) :
    NLWitness (fieldAut r K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K r))) := by
  obtain ⟨hs, hna⟩ := sympSimpleNonabelianRange hr σ hk
  refine nlWitness_of_nonLocalized (MulEquiv.refl (StatedProj (StatedSp r K))) hs hna
    (CFSG.SignalizerFunctorTheorem.NonLocal.nonLocalized_spSubfield hr σ) ?_
  rintro _ ⟨y, ⟨g, rfl⟩, rfl⟩
  exact KCSpComm.fieldAut_subfieldProj σ g

theorem sympFieldAut_data {p n : ℕ} (hr : 1 ≤ r) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {f : MulAut (LargeEvenProj (LargeEvenSpGroup K r))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K r)))
    (hord : orderOf f = p) :
    ∃ σ : K ≃+* K, f = fieldAut r K σ ∧ p ∣ n ∧ Nat.card (descentField σ) = 2 ^ (n / p) := by
  haveI : NeZero r := ⟨by omega⟩
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hσ : orderOf σ = p := by
    rw [← orderOf_injective (fieldAut r K) FieldFixSp.fieldAut_injective σ]
    exact hord
  obtain ⟨hpn, hcard⟩ := KCSpComm.card_descentField Nat.prime_two hn hK hσ
  exact ⟨σ, rfl, hpn, hcard⟩

theorem sympNLWitness {p n : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hn : 1 ≤ n) (hrn : ¬ (r = 2 ∧ n = p))
    (hK : Nat.card K = 2 ^ n) {f : MulAut (LargeEvenProj (LargeEvenSpGroup K r))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K r)))
    (hord : orderOf f = p) : NLWitness f := by
  obtain ⟨σ, rfl, hpn, hcard⟩ := sympFieldAut_data (by omega) hn hK hf hord
  refine sympNLWitness_fieldAut hr σ ?_
  rintro ⟨rfl, h2⟩
  rw [hcard] at h2
  have h1 : n / p = 1 := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
  obtain ⟨c, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left c hp.pos] at h1
  subst h1
  exact hrn ⟨rfl, mul_one p⟩

end Witness

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnSymplectic_holds : I2015NLOnSymplectic := by
  intro lab hlab ht
  refine atLabelWhen_of_witness hlab ?_ (fun p _ h => by
    rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h.1 (by decide))
  intro p hp _ _ _ hC Q hQ
  obtain ⟨t, r, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  have hrn : ¬ (r = 2 ∧ n = p) := hC
  rcases ht with rfl | rfl <;>
  · have hr : 2 ≤ r := hlab.2.1
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    intro _ _ _ f hf hord _ _
    exact sympNLWitness hp hr hn hrn hK hf hord

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
