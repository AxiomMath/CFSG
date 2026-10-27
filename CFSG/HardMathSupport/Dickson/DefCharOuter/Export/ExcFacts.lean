module

public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.I27_1Gen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
  CFSG.ComponentClassification.CatLeaf

section Arith

theorem excCard_isLTwoTwentySeven {X : Type} [Group X] (h : IsLTwoTwentySeven X) :
    Nat.card X = 9828 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd (by rw [hF]; decide), hF]
  norm_num

theorem excNotLTwoTwentySeven_of_pow_four_dvd {X : Type} [Group X] (h : 3 ^ 4 ∣ Nat.card X) :
    ¬ IsLTwoTwentySeven X := fun hL => by
  rw [excCard_isLTwoTwentySeven hL] at h
  norm_num at h

theorem excPowDvd_of_card_eq {t : StatedLieTag} {p f : ℕ}
    (hadm : StatedLieAdmissible t 0 p f) {G : Type} [Group G]
    (hcard : Nat.card G = lieOrderNumerator t 0 (p ^ f) / lieOrderDivisor t 0 (p ^ f)) :
    p ^ (lieSylowExponent t 0 * f) ∣ Nat.card G := by
  have hmul : Nat.card G * lieOrderDivisor t 0 (p ^ f) = lieOrderNumerator t 0 (p ^ f) := by
    rw [hcard]
    exact Nat.div_mul_cancel (CFSG.ComponentClassification.CatLeafProof.lieOrderDivisor_dvd_numerator
      hadm)
  have h1 : p ^ (lieSylowExponent t 0 * f) ∣ Nat.card G * lieOrderDivisor t 0 (p ^ f) := by
    rw [hmul, CFSG.ComponentClassification.CatLeafProof.lieOrderNumerator_eq hadm,
      mul_comm (lieSylowExponent t 0) f, pow_mul]
    exact dvd_mul_right _ _
  have hcop : Nat.Coprime (p ^ (lieSylowExponent t 0 * f)) (lieOrderDivisor t 0 (p ^ f)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hadm.1).2
      (CFSG.ComponentClassification.CatLeafProof.not_dvd_lieOrderDivisor hadm))
  exact hcop.dvd_of_dvd_mul_right h1

theorem excSylowExponent_ge {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags) :
    6 ≤ lieSylowExponent t 0 := by
  cases t <;> simp [chevalleyExceptionalTags, lieSylowExponent] at ht ⊢

end Arith

section Models


theorem excModel_isChevSimple {G : Type} [Group G] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel G t p f) : IsChevSimple p G := by
  obtain ⟨d, hd, he⟩ := CFSG.TauCetiBridge.exists_index_of_chevalleyExceptional
    CFSG.TauCetiBridge.chevalleyBridges h.1.1 hp2 ht h
  have hchar : d.1.characteristic = p := by
    obtain ⟨d, hv⟩ := d
    cases d <;> cases t <;>
      simp_all [CFSG.Models.NamesTag, chevalleyExceptionalTags]
  exact Or.inl ⟨.lie d, hchar, he⟩

theorem excModel_card_eq {G : Type} [Group G] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel G t p f) :
    Nat.card G = lieOrderNumerator t 0 (p ^ f) / lieOrderDivisor t 0 (p ^ f) := by
  rw [CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 h]
  cases t <;> simp [chevalleyExceptionalTags] at ht <;>
    simp [ordG2, ordF4, ordE6, ordE7, ordE8, ordTwistedE6, ordTrialityD4, lieOrderNumerator,
      lieOrderDivisor]

theorem excModel_pow_dvd_card {G : Type} [Group G] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel G t p f) : p ^ (lieSylowExponent t 0 * f) ∣ Nat.card G :=
  excPowDvd_of_card_eq h.1 (excModel_card_eq ht hp2 h)

theorem excModel_facts {G : Type} [Group G] {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {p f : ℕ} (hp2 : p ≠ 2)
    (h : ChevalleyExceptionalModel G t p f) :
    IsChevSimple p G ∧ p ∣ Nat.card G ∧ (p = 3 → ¬ IsLTwoTwentySeven G) := by
  have hf : 1 ≤ f := h.1.2.1
  have hN := excSylowExponent_ge ht
  have hpow := excModel_pow_dvd_card ht hp2 h
  refine ⟨excModel_isChevSimple ht hp2 h, ?_, ?_⟩
  · refine (dvd_pow_self p ?_).trans hpow
    exact (Nat.mul_pos (by omega) hf).ne'
  · rintro rfl
    refine excNotLTwoTwentySeven_of_pow_four_dvd ((pow_dvd_pow 3 ?_).trans hpow)
    calc 4 ≤ 6 * 1 := by norm_num
      _ ≤ lieSylowExponent t 0 * f := Nat.mul_le_mul hN hf

theorem excTwistedModel_graphFixedRootGroup (t : TwistTag) {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ d) ^ t.order) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ d)) :
    TwistedChevalleyModel (graphFixedRootGroup t K σ.toRingHom) t (ℓ ^ d) := by
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect t hℓ hd K hK σ.toRingHom hσ
  obtain ⟨e⟩ := nonempty_derivedCentralQuotient_equiv hΓ (exceptional_fixed_center_trivial t K σ)
  exact ⟨K, inferInstance, inferInstance, hK, σ.toRingHom, hσ, ⟨e.symm⟩⟩

end Models

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
