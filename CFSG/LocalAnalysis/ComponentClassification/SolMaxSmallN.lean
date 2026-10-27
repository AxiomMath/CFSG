module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallM
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallK

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem pumpOracle_of_eleven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hHe : SignalizerHeldPumpExclusionInput) (hn : n = 11) :
    S.PumpOracle := by
  intro c e₀ hcB htc hcN hc he₀ he₀2 hce hs4 hτc hdich
  by_cases h0 : (coreImage θ he₀).support.card = 0
  · exact S.exists_balanced_pump hbal hPump hN1 hcB htc hcN hc he₀ he₀2 hce (by omega) hτc hdich
  · have hne1 : coreImage θ he₀ ≠ 1 := fun h => h0 (by rw [h, Perm.support_one, Finset.card_empty])
    have h2 : coreImage θ he₀ * coreImage θ he₀ = 1 := by
      have h1 : (⟨e₀, he₀⟩ : ↥J) * ⟨e₀, he₀⟩ = 1 := Subtype.ext he₀2
      have h3 : θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
          θ ((⟨e₀, he₀⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
        rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
      exact congrArg Subtype.val h3
    have h4 := four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ he₀) h2 hne1
    exact S.exists_balanced_pump_seven hbal hPump hN1 hHe hn hcB htc hcN hc he₀ hce (by omega)
      hτc hdich

end Sol33

variable {X : Type} [Group X]

theorem balanceLemma_of_eleven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hHe : SignalizerHeldPumpExclusionInput)
    [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hpair : Sol78.IsSolomonPair t J 11)
    (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 11)) {E : Subgroup X} (hEJ : E ≤ J)
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    {D : Finset (Fin 11)} (hD : D.card = 4)
    (hsupp : ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
      ((θ (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)) ω = ω)
    {y : X} (hy : orderOf y = 2) (hyE : y ∈ centralizer (E : Set X))
    (hyK : y ∈ UnbalancedLayer.coreActionKernel J) (hyJ : y ∉ J) {a b : X}
    (ha : a ∈ E ⊔ zpowers y) (ha1 : a ≠ 1) (hb : b ∈ E ⊔ zpowers y) (hb1 : b ≠ 1) :
    SolAltLit.thetaFunctor E a ⊓ centralizer ({b} : Set X) ≤ SolAltLit.thetaFunctor E b := by
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  obtain ⟨t', hpair', hty⟩ := exists_isSolomonPair_commute hpair hyK.1 hy2
  have S : Sol33 X t' J 11 θ E D y :=
    { nonab := hnab
      kProper := hKP
      unbal := hunb
      notU := hnU
      pair := hpair'
      le := hEJ
      klein := hE
      card := hD
      supp := fun x hx hxE => support_coreImage_subset θ hsupp hx hxE
      hy := hy
      hyE := hyE
      hyK := hyK
      hyJ := hyJ
      hty := hty }
  have hPO : S.PumpOracle := S.pumpOracle_of_eleven hbal hPump hN1 hHe rfl
  have hdag : ∀ a' ∈ E ⊔ zpowers y, a' ≠ 1 → ∀ b' ∈ E ⊔ zpowers y, b' ≠ 1 →
      DaggerAt E a' b' := fun a' ha' ha'1 b' hb' hb'1 L hLC hLpc hLX =>
    S.dagger hbal hPO ha' ha'1 hb' hb'1 hLC hLpc hLX
  have hEC : ∀ c ∈ E ⊔ zpowers y, E ≤ centralizer ({c} : Set X) := fun c hc x hx =>
    mem_centralizer_singleton_iff.mpr (S.comm_of_mem (mem_sup_left hx) hc)
  exact thetaFunctor_inf_le_of_dagger hbal hE (S.mul_self_of_mem ha) ha1
    (S.mul_self_of_mem hb) hb1 (S.comm_of_mem ha hb) (hEC a ha) (hEC b hb)
    (hdag a ha ha1 b hb hb1) fun e he he1 => hdag a ha ha1 e (mem_sup_left he) he1

theorem signalizerSmallDegreeElevenInput_of_inputs
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hHe : SignalizerHeldPumpExclusionInput) :
    SignalizerSmallDegreeElevenInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair e E hEJ hE D hD hsupp
  exact ⟨fun y hy hyE hyK hyJ a ha ha1 b hb hb1 =>
      balanceLemma_of_eleven hbal hPump hN1 hHe hnab hKP hunb hnU hpair e hEJ hE hD hsupp hy hyE
        hyK hyJ ha ha1 hb hb1,
    fun F hFJ hF hEF DF hDF hdisj hsF f hf hf1 b hb hb1 =>
      signalizerLemma35Eleven hbal hPump hN1 hnab hKP hunb hnU hpair e hEJ hFJ hE hF hEF hD hDF
        hdisj hsupp hsF hf hf1 hb hb1⟩

theorem signalizerSmallDegreeInput_of_nine
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hHe : SignalizerHeldPumpExclusionInput)
    (h9 : SignalizerSmallDegreeNineInput) : SignalizerSmallDegreeInput :=
  signalizerSmallDegreeInput_of_degrees h9
    (signalizerSmallDegreeElevenInput_of_inputs hbal hPump hN1 hHe)

end CFSG.ComponentClassification.SolMax
