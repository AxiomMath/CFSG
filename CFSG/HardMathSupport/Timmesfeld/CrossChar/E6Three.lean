module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeField
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTwField
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedDiag

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge CFSG.RankThree.Chevalley

@[expose] def E6ThreeDiagonal :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f - 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
    ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ e6Inndiag K → ¬ D ≤ innerAut (adjointGroup Tag.E6 K) →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥

@[expose] def TwistedE6ThreeDiagonal :
    Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → 3 ∣ ℓ ^ f + 1 → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = ℓ ^ (2 * f) → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 D → Nat.card D = 3 ^ 3 →
      D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ D ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (twistedE6RootGroup K σ))) →
          localDeltaIn 3 H D = ⊥

theorem rootDiagAut_mem_innerAut_of_not_dvd
    (K : Type) [Field K] [Finite K] (h : ¬ 3 ∣ Nat.card K - 1)
    (a : Fin Tag.E6.rank → Kˣ) : rootDiagAut Tag.E6 K a ∈ innerAut (adjointGroup Tag.E6 K) := by
  classical
  set M := Tag.E6.cartan.transpose with hM
  set R := (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ) M).range with hR
  have h3 : R.index ∣ 3 := by
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.index_range_monomialHom_dvd K M).2
    rwa [hM, Matrix.det_transpose, det_cartan_E6] at h1
  have hcard : R.index ∣ (Nat.card K - 1) ^ Tag.E6.rank := by
    have h1 := R.index_dvd_card
    rwa [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.card_units] at h1
  have h1 : R.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
    · exact h1
    · rw [h1] at hcard
      exact absurd (Nat.prime_three.dvd_of_dvd_pow hcard) h
  rw [Subgroup.index_eq_one] at h1
  obtain ⟨t, ht⟩ : a ∈ R := h1 ▸ Subgroup.mem_top a
  rw [← ht, monomialHom_transpose_cartan]
  exact rootDiagAut_cartanChar_mem_inner t

theorem e6Inndiag_eq_innerAut_of_not_dvd
    (K : Type) [Field K] [Finite K] (h : ¬ 3 ∣ Nat.card K - 1) :
    e6Inndiag K = innerAut (adjointGroup Tag.E6 K) := by
  refine sup_eq_left.2 ?_
  rintro _ ⟨a, rfl⟩
  exact rootDiagAut_mem_innerAut_of_not_dvd K h a

theorem twistedE6Inndiag_eq_inn_of_mod_three
    {ℓ f : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hq : ℓ ^ f % 3 = 1) :
    twistedE6Inn K σ ⊔ twistedE6Diag K σ = twistedE6Inn K σ := by
  refine sup_eq_left.2 ?_
  rintro _ ⟨u, rfl⟩
  exact CFSG.SeitzReduction.EPilot.twistedE6_compatDiagAutHom_mem_inner hq
    (by rw [hK, ← pow_mul, mul_comm]) σ hσ u

section Models


theorem isLocallyBalancedAbs_adjointE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (hin : IsInnerLocallyBalanced 3 (adjointGroup Tag.E6 K))
    (hdiag : 3 ∣ ℓ ^ f - 1 → ∀ D : Subgroup (MulAut (adjointGroup Tag.E6 K)),
      IsElemAbelian 3 D → Nat.card D = 3 ^ 3 → D ≤ e6Inndiag K →
      ¬ D ≤ innerAut (adjointGroup Tag.E6 K) →
      ∀ H : Subgroup (MulAut (adjointGroup Tag.E6 K)), innerAut (adjointGroup Tag.E6 K) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (adjointGroup Tag.E6 K))) →
          localDeltaIn 3 H D = ⊥) :
    IsLocallyBalancedAbs 3 3 (adjointGroup Tag.E6 K) := by
  intro D hD hcard H hH hDH
  by_cases hDin : D ≤ innerAut (adjointGroup Tag.E6 K)
  · exact hin D hD hcard hDin H hH hDH
  by_cases hDd : D ≤ e6Inndiag K
  · by_cases h3 : 3 ∣ ℓ ^ f - 1
    · exact hdiag h3 D hD hcard hDd hDin H hH hDH
    · rw [← hK] at h3
      rw [e6Inndiag_eq_innerAut_of_not_dvd K h3] at hDd
      exact absurd hDd hDin
  obtain ⟨x, hxD, hxo⟩ := IsConcreteLE.not_le_iff_exists.1 hDd
  have hx1 : x ≠ 1 := fun h => hxo (h ▸ one_mem _)
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := Tag.E6) (K := K))
  exact localDeltaIn_eq_bot_of_fieldCore Nat.prime_three hinj hH hxD hx1
    (fieldCoreAt_E6_of_not_mem_e6Inndiag hℓ hℓ3 hf K hK (hD.2 x hxD) hxo)

theorem isLocallyBalancedAbs_twistedE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hin : IsInnerLocallyBalanced 3 (twistedE6RootGroup K σ))
    (hdiag : 3 ∣ ℓ ^ f + 1 → ∀ D : Subgroup (MulAut (twistedE6RootGroup K σ)),
      IsElemAbelian 3 D → Nat.card D = 3 ^ 3 → D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      ¬ D ≤ innerAut (twistedE6RootGroup K σ) →
      ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
        D ≤ Subgroup.normalizer (H : Set (MulAut (twistedE6RootGroup K σ))) →
          localDeltaIn 3 H D = ⊥) :
    IsLocallyBalancedAbs 3 3 (twistedE6RootGroup K σ) := by
  intro D hD hcard H hH hDH
  by_cases hDin : D ≤ innerAut (twistedE6RootGroup K σ)
  · exact hin D hD hcard hDin H hH hDH
  by_cases hDd : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ
  · have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
    rcases (by omega : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2) with h1 | h2
    · rw [twistedE6Inndiag_eq_inn_of_mod_three K hK σ hσ h1] at hDd
      exact absurd hDd hDin
    · exact hdiag (by omega) D hD hcard hDd hDin H hH hDH
  obtain ⟨x, hxD, hxo⟩ := IsConcreteLE.not_le_iff_exists.1 hDd
  have hx1 : x ≠ 1 := fun h => hxo (h ▸ one_mem _)
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  exact localDeltaIn_eq_bot_of_fieldCore Nat.prime_three hinj hH hxD hx1
    (fieldCoreAt_twistedE6_of_not_mem_inndiag hℓ hℓ3 hf K hK σ hσ (hD.2 x hxD) hxo)

end Models

section Families


theorem crossCharFamAt_E6_three_of (hin : CrossCharInnerAt .E6 fun _ p => p = 3)
    (hdiag : E6ThreeDiagonal) : CrossCharFamAt .E6 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  have hinC := hin ⟨d, hv⟩ hk 3 hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.E6 q := hk
  subst hq
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hK' : Nat.card K = q.p ^ q.exponent := hK.trans (TauCeti.PrimePower.card_def q)
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_adjointE6_three q.prime_p hℓ3
    q.exponent_pos K hK' (hinC.of_mulEquiv e.symm)
    fun h3 => hdiag q.p q.exponent q.prime_p hℓ3 q.exponent_pos h3 K hK')

theorem crossCharFamAt_twistedE6_three_of (hin : CrossCharInnerAt .twistedE6 fun _ p => p = 3)
    (hdiag : TwistedE6ThreeDiagonal) : CrossCharFamAt .twistedE6 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc rfl
  have hinC := hin ⟨d, hv⟩ hk 3 hp hp2 hc rfl
  obtain ⟨q, hq⟩ : ∃ q, d = TauCeti.LieTypeIndex.twistedE6 q := hk
  subst hq
  have hℓ3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  exact IsLocallyBalancedAbs.of_mulEquiv e (isLocallyBalancedAbs_twistedE6_three q.prime_p hℓ3
    q.exponent_pos K hK2 σ hσ (hinC.of_mulEquiv e.symm)
    fun h3 => hdiag q.p q.exponent q.prime_p hℓ3 q.exponent_pos h3 K hK2 σ hσ)

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
