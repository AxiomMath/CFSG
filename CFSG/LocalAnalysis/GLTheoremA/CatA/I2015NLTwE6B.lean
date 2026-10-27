module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLTwE6
import CFSG.RankThree.Chevalley.SteinbergBTOddF4Subfield
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalTwistedE6Main
import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedE6Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2015

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.RankThree.Chevalley (subfieldRootGroupImage subfieldImage
  units_map_entrywiseHom_of_mem_subfieldImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)

local notation "twH[" n ", " K "]" =>
  LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n

section Witness

set_option linter.unusedSectionVars false


theorem nlWitness_twE6_of_nl {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 ≤ p)
    (hnl : ∀ d : ℕ, 1 ≤ d → ∀ (L : Type) [Field L] [Finite L], Nat.card L = 2 ^ (2 * d * p) →
      ∀ (κ σ : L ≃+* L) (σ₀ : fixSubfield κ ≃+* fixSubfield κ), (∀ c, κ c = c ^ 2 ^ (2 * d)) →
        (∀ c, σ c = c ^ 2 ^ (d * p)) → (∀ c, (σ₀ c : L) = (c : L) ^ 2 ^ d) →
          NonLocalized ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
            (graphFixedRootGroup TwistTag.E6 L σ.toRingHom)))
    {f : MulAut (LargeEvenCenterQuot (twH[n, K]))}
    (hf : f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K (twH[n, K]))
    (hord : orderOf f = p) : NLWitness f := by
  classical
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨σe, hσ2, hσ1, hσe⟩ := exists_frobInvolution hn hK'
  obtain ⟨σ₀, hσ₀ord, ⟨d, hd⟩, hfixed⟩ := twE6SigmaZero hn hK hp hp2 hf hord
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      omega
    · exact h0
  have hnd : n = d * p := by rw [hd, mul_comm]
  have h2n : 2 * n = 2 * d * p := by rw [hnd]; ring
  obtain ⟨φ, hφ, hφord, hφtop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * n) hK'
  have hκ : ∀ c, (φ ^ (2 * d)) c = c ^ 2 ^ (2 * d) := fun c =>
    ringAut_pow_apply_of_frobenius hφ (2 * d) c
  have hT : ∀ c, (φ ^ d) c = c ^ 2 ^ d := fun c => ringAut_pow_apply_of_frobenius hφ d c
  have hε : ∀ c, (φ ^ (d * (p + 1))) c = c ^ 2 ^ (d * (p + 1)) := fun c =>
    ringAut_pow_apply_of_frobenius hφ (d * (p + 1)) c
  have hκord : orderOf (φ ^ (2 * d)) = p := by
    rw [orderOf_pow' _ (by omega : 2 * d ≠ 0), hφord, h2n, Nat.gcd_eq_right (Dvd.intro p rfl),
      Nat.mul_div_cancel_left p (by omega : 0 < 2 * d)]
  have hzp : Subgroup.zpowers σ₀ = Subgroup.zpowers (φ ^ (2 * d)) :=
    twE6ZpowersEq hφtop (hσ₀ord.trans hκord.symm)
  have hmem : σ₀ ∈ Subgroup.zpowers (φ ^ (2 * d)) := hzp ▸ Subgroup.mem_zpowers σ₀
  have hσ₀fix : ∀ c ∈ fixSubfield (φ ^ (2 * d)), σ₀ c = c := fun c hc =>
    twE6ApplyEqOfMemZpowers hmem hc
  have hK2 : Nat.card K = 2 ^ (2 * d * p) := by rw [hK', h2n]
  have hσ : ∀ c, σe c = c ^ 2 ^ (d * p) := fun c => by rw [hσe, hnd]
  have hσ₀' : ∀ c : fixSubfield (φ ^ (2 * d)),
      (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)) c : K) = (c : K) ^ 2 ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hNL := hnl d hd1 K hK2 (φ ^ (2 * d)) σe (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)))
    hκ hσ hσ₀'
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨-, -, hJC, -, -, hsJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer Nat.prime_two hd1 hp3
      (hp.odd_of_ne_two hp2) K hK2 (φ ^ (2 * d)) hκ σe hσ (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)))
      hσ₀' (φ ^ (d * (p + 1))) hε
  have eJC := Subgroup.subgroupOfEquivOfLe hJC
  have hs : IsSimpleGroup ↥((subfieldRootGroupImage TwistTag.E6 (fixSubfield (φ ^ (2 * d)))
      (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)))).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σe.toRingHom)) := eJC.isSimpleGroup
  have hna : ∃ x y : ↥((subfieldRootGroupImage TwistTag.E6 (fixSubfield (φ ^ (2 * d)))
      (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)))).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σe.toRingHom)), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  obtain ⟨e, he⟩ := twE6Model hn hK σe hσ2 hσ1 hσe (LargeEvenIsRoot TwistTag.E6.tag.cartan)
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag) (twH[n, K]) (largeEvenTwistedH_eq _ _ _ _)
  have hJsub : subfieldRootGroupImage TwistTag.E6 (fixSubfield (φ ^ (2 * d)))
      (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d))) ≤
        subfieldImage TwistTag.E6.tag (fixSubfield (φ ^ (2 * d))) :=
    Subgroup.map_mono ((graphFixedRootGroup_le _ _ _).trans
      (twistedFixedGroup_le_adjointGroup _ _ _))
  have hfix : ((subfieldRootGroupImage TwistTag.E6 (fixSubfield (φ ^ (2 * d)))
      (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d)))).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σe.toRingHom)).map e.symm.toMonoidHom ≤ fixSub f := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm y)
    have hey : e (QuotientGroup.mk x) = y := by rw [hx]; exact e.apply_symm_apply y
    have hyJ : (y : ModGL TwistTag.E6.tag K) ∈ subfieldRootGroupImage TwistTag.E6
        (fixSubfield (φ ^ (2 * d))) (fixSubfieldRestrict (φ ^ d) (φ ^ (2 * d))) := hy
    have hyfix : Units.map (entrywiseHom σ₀.toRingHom) (y : ModGL TwistTag.E6.tag K) = y :=
      units_map_entrywiseHom_of_mem_subfieldImage hσ₀fix (hJsub hyJ)
    have h1 := (he σ₀ x).2 (by rw [hey]; exact hyfix)
    have h2 : twRho TwistTag.E6 K n σ₀ x = x := (twE6RhoFixed σ₀ x).2 h1
    show f (e.symm y) = e.symm y
    rw [← hx]
    exact hfixed x h2
  haveI : Finite ↥(graphFixedRootGroup TwistTag.E6 K σe.toRingHom) := Subtype.finite
  exact nlWitness_of_nonLocalized e hs hna hNL hfix

theorem nlWitness_twE6 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : 3 < p)
    {f : MulAut (LargeEvenCenterQuot (twH[n, K]))}
    (hf : f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K (twH[n, K]))
    (hord : orderOf f = p) : NLWitness f :=
  nlWitness_twE6_of_nl hn hK hp hp2 hp3.le
    (fun d hd L _ _ hL κ σ σ₀ hκ hσ hσ₀ =>
      CFSG.SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedTwistedE6_of
        CFSG.SignalizerFunctorTheorem.NonLocal.subfieldNonLocalizedTwistedE6Small 2 d p
        Nat.prime_two hd hp hp3 L hL κ σ σ₀ hκ hσ hσ₀) hf hord

end Witness

section Family

set_option linter.unusedSectionVars false


theorem i2015NLOnTwE6_holds : I2015NLOnTwE6 := by
  intro lab hlab ht
  obtain ⟨t, r, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn : 1 ≤ n := hlab.1
  refine atLabelWhen_of_witness hlab ?_ (fun p _ => by simp)
  intro p hp hp2 _ _ hC Q hQ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, hF, hfin, hK, hQ'⟩ := hQ
  have hp3 : 3 < p := by
    have h1 := hp.two_le
    have h2 : p ≠ 3 := hC
    omega
  exact ⟨K, hF, hfin, hK, hQ', fun _ _ _ f hf hord _ _ => nlWitness_twE6 hn hK hp hp2 hp3 hf hord⟩

end Family

end CFSG.LocalAnalysis.GLTheoremA.I2015

end
