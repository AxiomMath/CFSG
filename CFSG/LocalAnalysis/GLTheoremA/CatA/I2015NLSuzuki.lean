module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSz
import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInn2
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSuzukiMain
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremA.MI
  CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.LocalAnalysis.GLTheoremA.FR
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

section Witness

set_option linter.unusedSectionVars false


theorem suzukiNLWitness {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpa : p ≠ 2 * a + 1) {f : MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K))}
    (hord : orderOf f = p)
    (hnot : f ∉ (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup a K) →* _).range) :
    NLWitness f := by
  obtain ⟨e⟩ := nonempty_szQuot_equiv ha hK
  have hαord : orderOf (MulAut.congr e f) = p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) f, hord]
  have hαinn : MulAut.congr e f ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hnot ((congr_mem_range_conj e f).1 h)
  obtain ⟨σ, h, b, k, _, _, hσp, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e f)
      hαord hαinn
  have hb1 : 1 ≤ b := by
    by_contra hb0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  let e' : CFSG.Open.signalizerFixedSubgroup (szFieldAut a K σ) ≃* suzukiGroup b k :=
    (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans eH
  obtain ⟨hsC, hnaC, -⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_and_not_isSolvable_of_equiv_suzukiGroup
      hb1 hkcard e'
  have hNL := CFSG.SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedSuzuki a ha K hK p hp
    hp2 hpa σ hσp
  let eT : LargeEvenCenterQuot (LargeEvenSzGroup a K) ≃* suzukiGroup a K :=
    e.trans (MulAut.conj h)
  refine nlWitness_of_nonLocalized eT hsC hnaC hNL ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : szFieldAut a K σ x = x := hx
  show f (eT.symm x) = eT.symm x
  apply eT.injective
  have key : ∀ y, eT (f y) = szFieldAut a K σ (eT y) := by
    intro y
    have h1 := congrArg (fun φ : MulAut (suzukiGroup a K) => φ (MulAut.conj h (e y))) hconj
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      MulAut.congr_apply, MulEquiv.trans_apply] at h1
    exact h1
  rw [key, MulEquiv.apply_symm_apply]
  exact hx'

end Witness

section Family

set_option linter.unusedSectionVars false


theorem suzukiWitnessAt {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twB2) : I2015NLWitnessAt (fun _ _ => True) lab := by
  intro p hp hp2 _ _ _
  have hInn := canonRawInnAny hp.ne_one hlab
  have h₁ : CAll lab fun R _ I F => GGRawInnField p R I F →
      LargeEvenSimpleGuard (fun R _ I F => SubfieldBody p lab R I F → ∀ f ∈ F, orderOf f = p →
        Finite R → (∃ J, GLAPComponent p (fixSub f) J) → NLWitness f) R I F := by
    obtain ⟨t, r, n⟩ := lab
    obtain ⟨-, hl⟩ := hlab
    dsimp only at ht hl
    subst ht
    obtain ⟨rfl, ⟨k, hk⟩, hn3⟩ := hl
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    intro Q hQ
    unfold CFSG.Assembly.LargeEvenRawDatum at hQ ⊢
    dsimp only at hQ ⊢
    rw [e] at hQ ⊢
    obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hF, hfin, hK, hQ', ?_⟩
    intro hinn hs hna hbody f hf hord hfinR hJ'
    obtain ⟨-, -, hconj, hFI⟩ := hinn hs hna
    obtain ⟨J, hJ⟩ := hJ'
    haveI := hfinR
    have hk1 : 1 ≤ k := by omega
    by_cases hpa : p = 2 * k + 1
    · exfalso
      obtain ⟨-, D, hD, hdat⟩ := hbody f hf hord
      have hsol : Group.IsSolvable ↥D := by
        rcases hdat with hdat | ⟨-, -, hsol⟩ | ⟨htag, -⟩
        · have h1 : (2 * k + 1) / p = 1 := by rw [← hpa, Nat.div_self hp.pos]
          dsimp only at hdat
          rw [h1] at hdat
          exact FR.Res.solvable_twB2 ↥D hdat
        · exact hsol
        · simp at htag
      exact false_of_component_of_solvable hD hsol hJ
    · exact suzukiNLWitness hk1 hK hp hp2 hpa hord fun ⟨r, hr⟩ => hFI f hf hord (hr ▸ hconj r)
  exact (h₁.and hInn).mono fun R _ I F ⟨h1, h2⟩ => h1 h2

theorem i2015NLOnSuzuki_holds : I2015NLOnSuzuki := by
  intro lab hlab ht
  have ht' : lab.tag = .twB2 := ht
  refine atLabelWhen_of_witness hlab (suzukiWitnessAt hlab ht') fun p _ h => ?_
  rw [ht'] at h
  exact absurd h.1 (by decide)

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
