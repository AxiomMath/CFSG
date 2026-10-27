module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZKey

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeZ

variable {X : Type} [Group X] [Finite X]

theorem two_dvd_card_of_pRank_eq_one {H : Type*} [Group H] [Finite H] (h : pRank 2 H = 1) :
    2 ∣ Nat.card H := by
  by_contra hnd
  have h0 : pRank 2 H ≤ 0 := by
    unfold pRank
    apply csSup_le'
    rintro r ⟨A, -, hA⟩
    by_contra hr
    apply hnd
    have h1 : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)
    rw [← hA] at h1
    exact h1.trans (Subgroup.card_subgroup_dvd_card A)
  omega

omit [Finite X] in
theorem comm_of_mem_center {K : Subgroup X} {y : X} (hy : y ∈ (center ↥K).map K.subtype) :
    y ∈ K ∧ ∀ k ∈ K, y * k = k * y := by
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z.2, fun k hk => ?_⟩
  exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)).symm

theorem exists_twoA_comm (hInv : HeldInvolAutFact) (hBC : HeldTwoBCentralizerFact)
    {L : Subgroup X} (hL : Nonempty (↥L ≃* Blueprint.NativeSporadic.He)) {t : X}
    (htN : t ∈ normalizer (L : Set X)) (htt : t * t = 1) (htC : t ∉ centralizer (L : Set X)) :
    ∃ u : X, HeldTwoA L u ∧ t * u = u * t := by
  have htt' : t * t ∈ centralizer (L : Set X) := by rw [htt]; exact one_mem _
  rcases hInv X L hL t htN htt' htC with ⟨y, hyL, hy2, hyc⟩ | ⟨-, hw, -, -⟩
  ·
    have hcomm : ∀ x ∈ L, x * y = y * x → t * x = x * t := by
      intro x hxL hxy
      have h1 : x * (y⁻¹ * t) = (y⁻¹ * t) * x := mem_centralizer_iff.mp hyc x hxL
      calc t * x = y * ((y⁻¹ * t) * x) := by group
        _ = y * (x * (y⁻¹ * t)) := by rw [h1]
        _ = (y * x) * (y⁻¹ * t) := by group
        _ = (x * y) * (y⁻¹ * t) := by rw [hxy]
        _ = x * t := by group
    by_cases hK : gsFixedLayer L y = ⊥
    · obtain ⟨-, -, -, -, w₁, hw₁H, -, -, hw₁A, -⟩ := hBC X L hL y hyL hy2 hK
      obtain ⟨hw₁L, hw₁y⟩ := mem_inf.mp hw₁H
      exact ⟨w₁, hw₁A, hcomm w₁ hw₁L (mem_centralizer_singleton_iff.mp hw₁y)⟩
    · exact ⟨y, ⟨hyL, hy2, hK⟩, hcomm y hyL rfl⟩
  · exact hw

end HeZ

theorem heldZStarEndStep_of_facts
    (hOutS : HeldOuterSolvableFact) (hInv : HeldInvolAutFact) (hAK : HeldTwoAKFact)
    (hB2 : HeldTwoBFact) (hSyl : HeldSylowFourFact) (hLay : HeldTwoALayerFact)
    (hFour : HeldTwoAFourFact) (hBC : HeldTwoBCentralizerFact) (hPair : HeldTwoAPairFact)
    (hGen : HeldTwoAGenerationFact) : HeldZStarEndStep := by
  intro X _ _ L hS _ _ h37
  obtain ⟨⟨hsimp, hnab, -⟩, -, hstd, ⟨eL⟩, hrank⟩ := id hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' 2 (HeZ.two_dvd_card_of_pRank_eq_one hrank)
  have ha : orderOf (a' : X) = 2 := by rw [Subgroup.orderOf_coe, ha']
  have haC : (a' : X) ∈ centralizer (L : Set X) := a'.2
  generalize (a' : X) = a at ha haC
  obtain ⟨g, hga, hne⟩ := HeZ.exists_conj_comm_ne hsimp hnab ha
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  have ht₁t₁ : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [haa]; group
  have ht₁1 : g * a * g⁻¹ ≠ 1 := fun h => ha1 (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have ht₁N : g * a * g⁻¹ ∈ normalizer (L : Set X) :=
    HeZ.centralizer_le_normalizer hstd haC ha (mem_centralizer_singleton_iff.mpr hga)
  have ht₁C : g * a * g⁻¹ ∉ centralizer (L : Set X) := fun h =>
    HeZ.false_of_pair hrank haC h haa ht₁t₁ ha1 ht₁1 (fun h' => hne h'.symm) hga.symm
  obtain ⟨u₁, hu₁, hcomm₁⟩ := HeZ.exists_twoA_comm hInv hBC ⟨eL⟩ ht₁N ht₁t₁ ht₁C
  obtain ⟨y, hy1, hyZ, hy⟩ := HeZ.key hOutS hInv hAK hB2 hSyl hLay hFour hBC hstd eL hrank h37 ha
    haC hga hne hu₁ hcomm₁
  obtain ⟨hyK, hyc⟩ := HeZ.comm_of_mem_center hyZ
  have hKL : ∀ v : X, gsFixedLayer L v ≤ L := fun v => (gsFixedLayer_le_inf L v).trans inf_le_left
  obtain ⟨w, hwK, hwA, hwZ, huwZ⟩ := hPair X L ⟨eL⟩ u₁ hu₁
  have hwa : w * a = a * w := mem_centralizer_iff.mp haC w (hKL u₁ hwK)
  have hcomm₂ : g * a * g⁻¹ * w = w * (g * a * g⁻¹) := by
    rw [hy]
    calc a * y * w = a * (w * y) := by rw [mul_assoc, hyc w hwK]
      _ = (w * a) * y := by rw [← mul_assoc, hwa]
      _ = w * (a * y) := by group
  obtain ⟨y', -, hy'Z, hy'⟩ := HeZ.key hOutS hInv hAK hB2 hSyl hLay hFour hBC hstd eL hrank h37
    ha haC hga hne hwA hcomm₂
  have hyy' : y = y' := mul_left_cancel (hy.symm.trans hy')
  subst hyy'
  obtain ⟨-, hy'c⟩ := HeZ.comm_of_mem_center hy'Z
  have hyL : L ≤ centralizer ({y} : Set X) := by
    rw [← hGen X L ⟨eL⟩ u₁ w hu₁ hwA hwK hwZ huwZ]
    exact sup_le (fun k hk => mem_centralizer_singleton_iff.mpr (hyc k hk).symm)
      (fun k hk => mem_centralizer_singleton_iff.mpr (hy'c k hk).symm)
  have hyLC : y ∈ L ⊓ centralizer (L : Set X) :=
    mem_inf.mpr ⟨hKL u₁ hyK, mem_centralizer_iff.mpr fun l hl =>
      mem_centralizer_singleton_iff.mp (hyL hl)⟩
  rw [HeZ.inf_centralizer_eq_bot (HeZ.center_eq_bot_of_held eL), mem_bot] at hyLC
  exact hy1 hyLC

end CFSG.ComponentClassification.GrSLit
