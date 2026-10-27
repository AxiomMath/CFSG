module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamD4

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem outerPLayerAt_trialityD4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S) (hpdvd : p ∣ Nat.card S) :
    OuterPLayerAt p S := by
  have hp5 : 3 < p := by
    have := hp.two_le
    omega
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_trialityD4] at h
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
    Finite.of_equiv S e.toEquiv
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
  obtain ⟨Θ, hΘ, hker⟩ := exists_hom_trialityD4 q.prime_p q.exponent_pos K hK σ hσ
  have eS : S ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := e.trans eK
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv S eS.toEquiv
  have hpdvdM : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  have hpdvdCat : p ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
    Nat.card_congr eK.toEquiv ▸ hpdvdM
  obtain ⟨m, hm, hdvdphi⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion
    (ℓ := q.p) (f := q.exponent) hp hp5 hpq (chevalleyModel_cat_trialityD4 hv)).1
      hpdvdCat).2.2.2.2 rfl
  have hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
      p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1 := by
    by_cases h6 : p ∣ (q.p ^ q.exponent) ^ 6 - 1
    · exact Or.inl h6
    · exact Or.inr (dvd_phi12_of_exhaustion (Nat.one_le_pow _ _ q.prime_p.pos) h6 hm hdvdphi)
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS fun x hxp hxo => ?_
  have hxinner : x ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun h => hxo (inner_le_innAutDerived _ h)
  have hx1 : Θ x ≠ 1 := fun h1 => hxinner (by
    have h2 : x ∈ Θ.ker := h1
    rw [hker] at h2
    exact h2)
  have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hpf : p ∣ q.exponent := by
    have h3 := dvd_exponent_of_ringAut (n := 3 * q.exponent) q.prime_p
      (by have := q.exponent_pos; omega) hK3 hp hx1
      (by rw [← map_pow, hxp, map_one])
    rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact h3
  exact fieldCoreAt_D4 q.prime_p q.exponent_pos K hK σ hσ Θ hΘ hp hp5
    (fun δ hδ => not_coprime_card_trialityFieldImage' q.prime_p q.exponent_pos K hK σ hσ hp
      hp5 hpf hdq δ hδ)
    (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxinner) hxinner

theorem lieOuterPLayer_triality (p : ℕ) : p.Prime → p ≠ 2 →
    LieOuterPLayer p isTrialityIdx := by
  intro hp hp2 d hd hP hnExc S hS hfin he hnot hpdvd
  obtain ⟨e⟩ := he
  cases d with
  | trialityD4 q => exact outerPLayerAt_trialityD4 hp hp2 hnExc hd e hnot hpdvd
  | A n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedA n q => exact absurd hP (by simp [isTrialityIdx])
  | B n q => exact absurd hP (by simp [isTrialityIdx])
  | C n q => exact absurd hP (by simp [isTrialityIdx])
  | D n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedD n q => exact absurd hP (by simp [isTrialityIdx])
  | E6 q => exact absurd hP (by simp [isTrialityIdx])
  | E7 q => exact absurd hP (by simp [isTrialityIdx])
  | E8 q => exact absurd hP (by simp [isTrialityIdx])
  | F4 q => exact absurd hP (by simp [isTrialityIdx])
  | G2 q => exact absurd hP (by simp [isTrialityIdx])
  | twistedE6 q => exact absurd hP (by simp [isTrialityIdx])
  | suzuki k => exact absurd hP (by simp [isTrialityIdx])
  | reeG2 k => exact absurd hP (by simp [isTrialityIdx])
  | reeF4 k => exact absurd hP (by simp [isTrialityIdx])
  | tits => exact absurd hP (by simp [isTrialityIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
