module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6TwoDiag
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcOuter
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcThreeToral
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToral
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Isotropic
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamTw
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamD4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6Holds
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.TauCetiBridge CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

theorem five_dvd_cases {n : ℕ} (hn : 1 ≤ n) (h5 : ¬ 5 ∣ n) :
    5 ∣ n - 1 ∨ 5 ∣ n + 1 ∨ 5 ∣ n ^ 2 + 1 := by
  have hmod : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h | h | h | h
  · left
    omega
  · right
    right
    have h2 : n ^ 2 % 5 = 4 := by rw [Nat.pow_mod, h]
    generalize n ^ 2 = m at h2 ⊢
    omega
  · right
    right
    have h2 : n ^ 2 % 5 = 4 := by rw [Nat.pow_mod, h]
    generalize n ^ 2 = m at h2 ⊢
    omega
  · right
    left
    omega

theorem five_dvd_sub_or_add_of_dvd_pow_six {n : ℕ} (hn : 1 ≤ n) (h : 5 ∣ n ^ 6 - 1) :
    5 ∣ n - 1 ∨ 5 ∣ n + 1 := by
  have hmod : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hpos : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · exfalso
    have h6 : n ^ 6 % 5 = 0 := by rw [Nat.pow_mod, h0]
    generalize n ^ 6 = m at h6 h hpos
    omega
  · left
    omega
  · exfalso
    have h6 : n ^ 6 % 5 = 4 := by rw [Nat.pow_mod, h2]
    generalize n ^ 6 = m at h6 h hpos
    omega
  · exfalso
    have h6 : n ^ 6 % 5 = 4 := by rw [Nat.pow_mod, h3]
    generalize n ^ 6 = m at h6 h hpos
    omega
  · right
    omega


section ThreeFE

theorem localTwoCrossFamCat_three_F4 : LocalTwoCrossFamCat 3 .F4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_three hinj
    (innerPlaneBalance_adjointF4_three K hpK)
    (outerFields_adjointF4_odd q K hK Nat.prime_three le_rfl hpK)

theorem localTwoCrossFamCat_three_E7 : LocalTwoCrossFamCat 3 .E7 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E7) (K := K)
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_three hinj
    (innerPlaneBalance_adjointE7_three K hpK)
    (outerFields_adjointE7_odd q K hK Nat.prime_three le_rfl hpK)

theorem localTwoCrossFamCat_three_E8 : LocalTwoCrossFamCat 3 .E8 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three hpq
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K)
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_three hinj
    (innerPlaneBalance_adjointE8_three K hpK)
    (outerFields_adjointE8_odd q K hK Nat.prime_three le_rfl hpK)

end ThreeFE

section FiveE

theorem localTwoCrossFamCat_five_F4 (h4 : F4InnerFiveFour) : LocalTwoCrossFamCat 5 .F4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpc : ¬ 5 ∣ q.card := not_dvd_card_of_ne Nat.prime_five hpq
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact hpc
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  have hin : InnerPlaneBalance 5 (adjointGroup Tag.F4 K) := by
    rcases five_dvd_cases hq1 hpc with h | h | h
    · exact innerPlaneBalance_adjointF4_five K hpK (Or.inl (by rw [hK]; exact h))
    · exact innerPlaneBalance_adjointF4_five K hpK (Or.inr (by rw [hK]; exact h))
    · exact (h4 q hv (fun h' => hpq h'.symm) h).of_mulEquiv e.symm
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_five hinj hin
    (outerFields_adjointF4_odd q K hK Nat.prime_five (by norm_num) hpK)

theorem localTwoCrossFamCat_five_E6 (h1 : E6InnerFiveOne) (h4 : E6InnerFiveFour) :
    LocalTwoCrossFamCat 5 .E6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hq5 : q.p ≠ 5 := fun h => hpq h.symm
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpc : ¬ 5 ∣ q.card := not_dvd_card_of_ne Nat.prime_five hpq
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact hpc
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  have hin : InnerPlaneBalance 5 (CatT ⟨.E6 q, hv⟩) := by
    rcases five_dvd_cases hq1 hpc with h | h | h
    · exact h1 q hv hq5 h
    · exact innerPlaneBalance_E6_five_dvd_add_one q hv hq5 h
    · exact h4 q hv hq5 h
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_five hinj (hin.of_mulEquiv e.symm)
    (outerFields_adjointE6_ge_five q K hK Nat.prime_five le_rfl hpK)

theorem localTwoCrossFamCat_five_E7 (h1 : E7InnerFiveOne) (h2 : E7InnerFiveTwo)
    (h4 : E7InnerFiveFour) : LocalTwoCrossFamCat 5 .E7 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hq5 : q.p ≠ 5 := fun h => hpq h.symm
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpc : ¬ 5 ∣ q.card := not_dvd_card_of_ne Nat.prime_five hpq
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact hpc
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E7) (K := K)
  have hin : InnerPlaneBalance 5 (CatT ⟨.E7 q, hv⟩) := by
    rcases five_dvd_cases hq1 hpc with h | h | h
    · exact h1 q hv hq5 h
    · exact h2 q hv hq5 h
    · exact h4 q hv hq5 h
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_five hinj (hin.of_mulEquiv e.symm)
    (outerFields_adjointE7_odd q K hK Nat.prime_five (by norm_num) hpK)

theorem localTwoCrossFamCat_five_E8 (h4 : E8InnerFiveFour) : LocalTwoCrossFamCat 5 .E8 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hq5 : q.p ≠ 5 := fun h => hpq h.symm
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpc : ¬ 5 ∣ q.card := not_dvd_card_of_ne Nat.prime_five hpq
  have hpK : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    exact hpc
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E8) (K := K)
  have hin : InnerPlaneBalance 5 (adjointGroup Tag.E8 K) := by
    rcases five_dvd_cases hq1 hpc with h | h | h
    · exact innerPlaneBalance_adjointE8_five_split K hpK (by rw [hK]; exact h)
    · exact innerPlaneBalance_adjointE8_five_neg K hpK (by rw [hK]; exact h)
    · exact (h4 q hv hq5 h).of_mulEquiv e.symm
  exact isLocallyBalancedAbs_two_of_model e Nat.prime_five hinj hin
    (outerFields_adjointE8_odd q K hK Nat.prime_five (by norm_num) hpK)

end FiveE


section ThreeE6

theorem exists_inner_ne_one_of_le_e6Inndiag_nine (K : Type) [Field K] [Finite K]
    {D : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcard : Nat.card D = 3 ^ 2)
    (hDd : D ≤ e6Inndiag K) : ∃ d ∈ D, d ∈ innerAut (adjointGroup Tag.E6 K) ∧ d ≠ 1 := by
  classical
  obtain ⟨Φ, -, hker, hdvd⟩ := exists_outer_hom_E (K := K) (τ := Tag.E6) (Or.inl rfl)
  set N := CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup Tag.E6 K)
    with hN
  set π := QuotientGroup.mk' N with hπ
  by_contra hno
  push Not at hno
  have hinj : Function.Injective (π.domRestrict D) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨d, hd⟩ hk
    have hk' : π d = 1 := hk
    have hdN : d ∈ N := (QuotientGroup.eq_one_iff d).1 hk'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hno d hd hdN)
  have himg : D.map π ≤ Φ.ker := by
    rintro _ ⟨d, hd, rfl⟩
    have hdd : d ∈ ((N ⊔ (rootDiagAutHom Tag.E6 K).range : Subgroup _) : Set _) := hDd hd
    rw [Subgroup.normal_mul] at hdd
    obtain ⟨i, hi, r, ⟨a, rfl⟩, rfl⟩ := hdd
    rw [hker]
    refine ⟨a, ?_⟩
    change π (rootDiagAutHom Tag.E6 K a) = π (i * rootDiagAutHom Tag.E6 K a)
    have hpi : π i = 1 := (QuotientGroup.eq_one_iff i).2 hi
    rw [map_mul, hpi, one_mul]
  have h3 : Nat.card Φ.ker ∣ 3 := by
    have h := hdvd
    rwa [show Tag.E6.cartan.det.natAbs = 3 by rw [det_cartan_E6]; rfl] at h
  have hle : Nat.card (D.map π) ≤ 3 :=
    (Subgroup.card_le_of_le himg).trans (Nat.le_of_dvd (by norm_num) h3)
  have heq : Nat.card (D.map π) = Nat.card D := by
    rw [← MonoidHom.domRestrict_range]
    exact Nat.card_range_of_injective hinj
  rw [heq, hcard] at hle
  norm_num at hle

theorem isLocallyBalancedAbs_three_adjointE6 (hX3 : E6HeisenbergDiagThreeBalance) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) : IsLocallyBalancedAbs 3 2 (adjointGroup Tag.E6 K) := by
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.E6) (K := K)
  intro D hD hcard H hH _
  by_cases hDd : D ≤ e6Inndiag K
  · by_cases hsmall : Nat.card K = 2 ∨ Nat.card K = 4
    · obtain ⟨d, hdD, hdin, hd1⟩ := exists_inner_ne_one_of_le_e6Inndiag_nine K hcard hDd
      exact localDeltaIn_eq_bot_of_innerOneBalanceThree
        (SmallQ3E6.innerOneBalanceThree_E6_small K hsmall) hD hdD hdin hd1 hH
    · push Not at hsmall
      obtain ⟨K₁, hfin, hroot⟩ := exists_cubeExt K
      by_cases hiso : E6DiagIsotropic K K₁ D
      · exact e6IsotropicDiagBalance_holds K h3 hsmall.1 K₁ hroot D hDd hD hcard hiso H hH
      · exact hX3 K h3 hsmall.1 hsmall.2 K₁ hroot D hDd hD hcard hiso H hH
  · obtain ⟨x, hxD, hxo⟩ := Set.not_subset.1 hDd
    have hx1 : x ≠ 1 := fun h => hxo (h ▸ one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore Nat.prime_three hinj hH hxD hx1
      (fieldCoreAt_E6_of_not_mem_e6Inndiag hℓ hℓ3 hf K hK (hD.2 x hxD) hxo)

theorem localTwoCrossFamCat_three_E6 (hX3 : E6HeisenbergDiagThreeBalance) :
    LocalTwoCrossFamCat 3 .E6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_three_adjointE6 hX3 q.prime_p (fun h => hpq h.symm) q.exponent_pos K
      (hK.trans (TauCeti.PrimePower.card_def q)))

theorem isLocallyBalancedAbs_three_twistedE6 (hX3 : TwistedE6HeisenbergDiagThreeBalance)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ))) :
    IsLocallyBalancedAbs 3 2 (twistedE6RootGroup K σ) := by
  intro D hD hcard H hH _
  by_cases hDd : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  · by_cases h2 : ℓ ^ f = 2
    · have hK4 : Nat.card K = 4 := by rw [hK, h2]; norm_num
      have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, h2]
      obtain ⟨d, hdD, hdin, hd1⟩ := twistedE6TwoDiagMeetsInn_holds K hK4 σ hσ2 D hDd hcard
      exact localDeltaIn_eq_bot_of_innerOneBalanceThree
        (SmallQ3.innerOneBalanceThree_twE6_two SmallQ3.twE6TwoFusion_holds
            SmallQ3.twE6TwoRigid_holds K hK4 σ hσ2) hD hdD hdin hd1 hH
    · obtain ⟨K₁, hfin, hroot⟩ := exists_cubeExt K
      by_cases hiso : TwistedE6DiagIsotropic K σ K₁ D
      · exact twistedE6IsotropicDiagBalance_holds ℓ f hℓ hℓ3 hf h2 K hK σ hσ K₁ hroot D hDd hD
          hcard hiso H hH
      · exact hX3 ℓ f hℓ hℓ3 hf h2 K hK σ hσ K₁ hroot D hDd hD hcard hiso H hH
  · obtain ⟨x, hxD, hxo⟩ := Set.not_subset.1 hDd
    have hx1 : x ≠ 1 := fun h => hxo (h ▸ one_mem _)
    exact localDeltaIn_eq_bot_of_fieldCore Nat.prime_three hinj hH hxD hx1
      (fieldCoreAt_twistedE6_of_not_mem_inndiag hℓ hℓ3 hf K
        (by rw [hK, ← pow_mul, mul_comm]) σ hσ (hD.2 x hxD) hxo)

theorem localTwoCrossFamCat_three_twistedE6 (hX3 : TwistedE6HeisenbergDiagThreeBalance) :
    LocalTwoCrossFamCat 3 .twistedE6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 3 ≠ q.p := fun h => hc (by simp [h])
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hinj := CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv e
    (conj_injective_cat_twistedE6 q hv)
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_three_twistedE6 hX3 q.prime_p (fun h => hpq h.symm)
      q.exponent_pos K hK σ hσ hinj)

end ThreeE6


section TriD4

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

theorem localTwoCrossFamCat_three_trialityD4 (hin : TriD4InnerThreeBalance)
    (hout : TriD4OuterThreeBalance) : LocalTwoCrossFamCat 3 .trialityD4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hq3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  refine IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_of_kinds Nat.prime_three hinj
      (innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      ((hin q hv hq3).of_mulEquiv e.symm) ?_)
  intro D hD _ hDin
  obtain ⟨x, hxD, hxo⟩ := Set.not_subset.1 hDin
  exact ⟨x, hxD, hxo, Or.inr (coreFreeAt_three_graphFixedRootGroup_D4 hout q.prime_p hq3
    q.exponent_pos hK σ hσ x (hD.2 x hxD) hxo)⟩

theorem outerFields_trialityD4_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hpq : p ≠ q.p)
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (hK : Nat.card K = (q.p ^ q.exponent) ^ 3)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (e : CatT ⟨.trialityD4 q, hv⟩ ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hinj : Function.Injective (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    OuterFields p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : Finite (CatT ⟨.trialityD4 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨Θ, hΘ, hker⟩ := exists_hom_trialityD4 q.prime_p q.exponent_pos K hK σ hσ
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  refine outerFields_of_hom Θ hp hinj (fun x hx _ => by rw [hker] at hx; exact hx) ?_
  by_cases hpc : p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  · refine Or.inr fun x hxp hxo => ?_
    have hx1 : Θ x ≠ 1 := fun h1 => hxo (by
      have h2 : x ∈ Θ.ker := h1
      rw [hker] at h2
      exact h2)
    have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
    have hpf : p ∣ q.exponent := by
      have h3 := dvd_exponent_of_ringAut q.prime_p (by have := q.exponent_pos; omega) hK3 hp hx1
        (by rw [← map_pow, hxp, map_one])
      rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · exact h3
    have hdvd' : p ∣ Nat.card (CatT ⟨.trialityD4 q, hv⟩) := by
      rw [Nat.card_congr e.toEquiv]
      exact hpc
    obtain ⟨m, hm, hd⟩ := ((exact_E_type_and_triality_cross_prime_factor_exhaustion hp
      (by omega) (Ne.symm hpq) (chevalleyModel_cat_trialityD4 hv)).1 hdvd').2.2.2.2 rfl
    have hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
        p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1 := by
      by_cases hd6 : p ∣ (q.p ^ q.exponent) ^ 6 - 1
      · exact Or.inl hd6
      · exact Or.inr (dvd_phi12_of_exhaustion (Nat.one_le_pow _ _ q.prime_p.pos) hd6 hm hd)
    exact fieldCoreAt_D4 q.prime_p q.exponent_pos K hK σ hσ Θ hΘ hp (by omega)
      (fun δ hδ => not_coprime_card_trialityFieldImage' q.prime_p q.exponent_pos K hK σ hσ hp
        (by omega) hpf hdq δ hδ)
      (orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo) hxo
  · exact Or.inl (elemAbelian_card_eq_one_of_not_dvd hp hpc)

theorem localTwoCrossFamCat_five_trialityD4 : LocalTwoCrossFamCat 5 .trialityD4 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hq5 : q.p ≠ 5 := fun h => hpq h.symm
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinjCat := conj_injective_cat_trialityD4 q hv
  have hinj := CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv e hinjCat
  have hin : InnerPlaneBalance 5 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    by_cases h2 : 5 ∣ q.card ^ 6 - 1
    · exact (innerPlaneBalance_trialityD4_five q hv hq5
        (five_dvd_sub_or_add_of_dvd_pow_six hq1 h2)).of_mulEquiv e.symm
    · exact (innerPlaneBalance_of_rankLE1 Nat.prime_five hinjCat
        (rankLE1_cat_trialityD4 q hv Nat.prime_five (by norm_num) hpq h2)).of_mulEquiv e.symm
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_of_model (MulEquiv.refl _) Nat.prime_five hinj hin
      (outerFields_trialityD4_ge_five Nat.prime_five le_rfl q hv hpq K σ hK hσ e hinj))

end TriD4

section TwE6Five

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (fieldAut_isCyclic)

theorem outerFields_twistedE6_ge_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hpq : p ≠ q.p) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 2) (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ))) :
    OuterFields p (twistedE6RootGroup K σ) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hpq0 : ¬ p ∣ q.p ^ q.exponent := fun h =>
    hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  obtain ⟨Θ, hΘ, hker⟩ := exists_hom_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp (by omega)
  have : IsCyclic (RingAut K) := fieldAut_isCyclic K
  refine outerFields_of_hom Θ hp hinj (fun x hx hxp => hker x hx hxp) ?_
  by_cases h0 : degCountTw (orderOf ((q.card : ℕ) : ZMod p)) = 0
  · refine Or.inl fun F hF => ?_
    rw [hqc] at h0
    exact elemAbelian_card_eq_one_of_degCountTw_zero q.prime_p q.exponent_pos K hK σ hσ hp
      (by omega) hpq0 rfl h0 hF
  · refine Or.inr fun x hxp hxo => ?_
    have hxord := orderOf_eq_of_pow_eq_one_of_not_mem hp hxp hxo
    have hx1 : Θ x ≠ 1 := fun h1 => hxo (hker x h1 hxp)
    have hpf : p ∣ q.exponent := by
      have h3 := dvd_exponent_of_ringAut q.prime_p (n := 2 * q.exponent)
        (by have := q.exponent_pos; omega) hK2 hp hx1 (by rw [← map_pow, hxp, map_one])
      rcases (Nat.Prime.dvd_mul hp).1 h3 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · exact h3
    have hpos := Nat.pos_of_ne_zero h0
    refine fieldCoreAt_twistedE6 q.prime_p q.exponent_pos K hK2 σ hσ Θ hΘ hp (by omega) ?_
      hxord hxo
    intro κ hκ σ₀ hσ₀ hkcard
    have hdp : q.exponent / p * p = q.exponent := Nat.div_mul_cancel hpf
    have hd1 : 1 ≤ q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
    have : Finite (fixSubfield κ) := Subtype.finite
    have hk2 : Nat.card (fixSubfield κ) = (q.p ^ (q.exponent / p)) ^ 2 := by
      rw [hkcard, ← pow_mul, mul_comm]
    have hσ₀' : ∀ c : fixSubfield κ, σ₀ c = c ^ (q.p ^ (q.exponent / p)) := fun c =>
      Subtype.ext (by rw [hσ₀ c, SubmonoidClass.coe_pow])
    have hcast : (((q.p ^ q.exponent : ℕ)) : ZMod p) =
        (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p) := by
      conv_lhs => rw [← hdp, pow_mul, Nat.cast_pow (q.p ^ (q.exponent / p)) p, ZMod.pow_card]
    have hcnt' : 0 < degCountTw (orderOf (((q.p ^ (q.exponent / p) : ℕ)) : ZMod p)) := by
      rw [← hcast, ← hqc]
      exact hpos
    have hpq1 : ¬ p ∣ q.p ^ (q.exponent / p) := fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
    have : Finite (ModGL TwistTag.E6.tag (fixSubfield κ)) := finite_modGL
    have : Finite (twistedE6RootGroup (fixSubfield κ) σ₀) := Subtype.finite
    have hcard : Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀) =
        Nat.card (twistedE6RootGroup (fixSubfield κ) σ₀) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [hcard]
    exact not_coprime_card_twistedE6_of_pos q.prime_p hd1 (fixSubfield κ) hk2 σ₀ hσ₀' hp
      (by omega) hpq1 hcnt'

theorem localTwoCrossFamCat_five_twistedE6 (h2 : TwistedE6InnerFiveTwo)
    (h4 : TwistedE6InnerFiveFour) : LocalTwoCrossFamCat 5 .twistedE6 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ hc _
  change d = _ at hd
  subst hd
  have hpq : 5 ≠ q.p := fun h => hc (by simp [h])
  have hq5 : q.p ≠ 5 := fun h => hpq h.symm
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hpc : ¬ 5 ∣ q.card := not_dvd_card_of_ne Nat.prime_five hpq
  have hq1 : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  have hinj := CFSG.HardMathSupport.Timmesfeld.LocalTwo.conj_injective_of_mulEquiv e
    (conj_injective_cat_twistedE6 q hv)
  have hin : InnerPlaneBalance 5 (CatT ⟨.twistedE6 q, hv⟩) := by
    rcases five_dvd_cases hq1 hpc with h | h | h
    · exact innerPlaneBalance_twistedE6_five_dvd_sub_one q hv hq5 h
    · exact h2 q hv hq5 h
    · exact h4 q hv hq5 h
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_two_of_model (MulEquiv.refl _) Nat.prime_five hinj
      (hin.of_mulEquiv e.symm)
      (outerFields_twistedE6_ge_five Nat.prime_five le_rfl q hpq K σ hK hσ hinj))

end TwE6Five

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
