module

public import CFSG.LocalAnalysis.RankThreeUC.K518HRkAux
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.RankThree.PartOne.KCRootAxis

private theorem card_SL2_field (K : Type) [Field K] [Finite K] :
    Nat.card (SL₂ K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h := Matrix.card_SL_field (𝔽 := K) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h, Nat.card_eq_fintype_card (α := K)]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have e1 : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1]
  ring

private theorem exists_fieldAut_of_pow_mem_inner {F : Type} [Field F] [CharP F 2] [Finite F]
    {ℓ : ℕ} [Fact ℓ.Prime] {φ : MulAut (SL₂ F)}
    (hφI : φ ∉ (MulAut.conj : SL₂ F →* MulAut (SL₂ F)).range)
    (hφℓ : φ ^ ℓ ∈ (MulAut.conj : SL₂ F →* MulAut (SL₂ F)).range) :
    ∃ (M : SL₂ F) (σ : F ≃+* F), φ = MulAut.conj M * slFieldAut F σ ∧ orderOf σ = ℓ := by
  obtain ⟨M, σ, hφ⟩ := exists_conj_mul_slFieldAut φ
  refine ⟨M, σ, hφ, ?_⟩
  let π : MulAut (SL₂ F) →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (SL₂ F) :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (SL₂ F))
  have h1 : π (MulAut.conj M) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨M, rfl⟩
  have h2 : π φ = outFieldHom F σ := by
    rw [hφ, map_mul, h1, one_mul]; rfl
  have hσ1 : σ ≠ 1 := by
    intro h
    apply hφI
    rw [hφ, h, map_one, mul_one]
    exact ⟨M, rfl⟩
  have hσℓ : σ ^ ℓ = 1 := by
    have h3 : π (φ ^ ℓ) = 1 := (QuotientGroup.eq_one_iff _).mpr hφℓ
    rw [map_pow, h2, ← map_pow] at h3
    exact outFieldHom_bijective.1 (h3.trans (map_one _).symm)
  exact orderOf_eq_prime hσℓ hσ1

private theorem exists_fixed_order_sl2 {F : Type} [Field F] [CharP F 2] [Finite F]
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card (SL₂ F))
    {σ : F ≃+* F} (hσ : orderOf σ = ℓ) :
    ∃ z : SL₂ F, orderOf z = ℓ ∧ slFieldAut F σ z = z := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hn2, hn⟩ := FiniteField.card F 2
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hF : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hn2 hn1 hF
  obtain ⟨hdn, S₀, hS₀, hS₀card⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdn hS₀card
  have hq : Nat.card F = (Nat.card S₀) ^ ℓ := by
    rw [hS₀card, ← pow_mul, Nat.div_mul_cancel hdn, hF]
  have hSL := card_SL2_field F
  have hdvd' : ℓ ∣ Nat.card F ^ 2 - 1 := by
    rw [hSL] at hdvd
    rcases (Nat.Prime.dvd_mul hℓ.out).mp hdvd with h | h
    · exfalso
      rw [hF] at h
      have := Nat.Prime.dvd_of_dvd_pow hℓ.out h
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp this)
    · exact h
  have hmod : Nat.card F ≡ Nat.card S₀ [MOD ℓ] := by
    rw [hq]
    refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
    push_cast
    exact ZMod.pow_card _
  have hdvd₀ : ℓ ∣ Nat.card S₀ ^ 2 - 1 := by
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h2 : 1 ≤ Nat.card S₀ ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have h3 : 1 ≡ Nat.card F ^ 2 [MOD ℓ] := (Nat.modEq_iff_dvd' h1).mpr hdvd'
    have h4 : Nat.card F ^ 2 ≡ Nat.card S₀ ^ 2 [MOD ℓ] := hmod.pow 2
    exact (Nat.modEq_iff_dvd' h2).mp (h3.trans h4)
  have hdvdSL₀ : ℓ ∣ Nat.card (SL₂ S₀) := by
    rw [card_SL2_field S₀]
    exact Dvd.dvd.mul_left hdvd₀ _
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' ℓ hdvdSL₀
  have hinj : Function.Injective
      (Matrix.SpecialLinearGroup.map S₀.subtype : SL₂ S₀ →* SL₂ F) := by
    intro a b hab
    ext i j
    have := congrArg (fun m : SL₂ F => (m : Matrix (Fin 2) (Fin 2) F) i j) hab
    simpa using this
  refine ⟨Matrix.SpecialLinearGroup.map S₀.subtype z₀, ?_, ?_⟩
  · rw [orderOf_injective _ hinj, hz₀]
  · ext i j
    have h1 : ((z₀ : Matrix (Fin 2) (Fin 2) S₀) i j : F) ∈ (S₀ : Set F) := (z₀ i j).2
    rw [hS₀] at h1
    exact h1 σ (Subgroup.mem_zpowers σ)

theorem k518RkSL2_holds : K518RkSL2 := by
  intro F _ _ hchar ℓ hℓ hℓ2 hdvd ψ ⟨k, hk⟩ hψ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F 2 := (ringChar.eq_iff).mp hchar
  obtain ⟨φ, hφψ, hφI, hφℓ⟩ := exists_mem_zpowers_notMem_pow_mem_of_orderOf _ hk hψ
  obtain ⟨M, σ, hφ, hσ⟩ := exists_fieldAut_of_pow_mem_inner hφI hφℓ
  obtain ⟨z, hz, hzσ⟩ := exists_fixed_order_sl2 hℓ2 hdvd hσ
  have hfinj : ∀ τ : F ≃+* F,
      slFieldAut F τ ∈ (MulAut.conj : SL₂ F →* MulAut (SL₂ F)).range → τ = 1 := by
    rintro τ ⟨N, hN⟩
    have h : MulAut.conj N * slFieldAut F 1 = MulAut.conj 1 * slFieldAut F τ := by
      rw [map_one, mul_one, map_one, one_mul]; exact hN
    exact (conj_mul_slFieldAut_inj h).2.symm
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hℓ.one_lt.ne hσ
  have hinj : Function.Injective (slFieldAut F) := by
    rw [injective_iff_map_eq_one]
    intro τ hτ
    exact hfinj τ (by rw [hτ]; exact one_mem _)
  have hc1 : (MulAut.conj z) ^ ℓ = 1 := by
    rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have hc2 : MulAut.conj z ≠ 1 := by
    intro h
    have hzc : z ∈ Subgroup.center (SL₂ F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := DFunLike.congr_fun h g
      change z * g * z⁻¹ = g at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [sl2_center_eq_bot, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz
    exact hℓ.one_lt.ne hz
  refine two_le_pRank_sup_zpowers_of_commute (x := MulAut.conj z) (y := slFieldAut F σ)
    ⟨z, rfl⟩ ?_ ?_ (orderOf_eq_prime hc1 hc2) (by rw [orderOf_injective _ hinj, hσ]) ?_
  · have : slFieldAut F σ = (MulAut.conj M)⁻¹ * φ := by rw [hφ, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left ⟨M, rfl⟩))
      (Subgroup.mem_sup_right hφψ)
  · exact fun h => hσ1 (hfinj σ h)
  · refine MulEquiv.ext fun g => ?_
    change z * (slFieldAut F σ g) * z⁻¹ = slFieldAut F σ (z * g * z⁻¹)
    rw [map_mul, map_mul, map_inv, hzσ]

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H
