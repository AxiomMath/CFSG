module

public import CFSG.LocalAnalysis.RankThreeUC.K518HRkDefs
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkPSU
public import CFSG.LocalAnalysis.RankThreeUC.K518HRkTor
public import CFSG.RankThree.PartOne.CTP.UnitaryTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms

theorem hasRankTwoPair_of_descend {G G' : Type*} [Group G] [Group G'] (d : MulAut G →* MulAut G')
    (hd : Function.Injective d) (hinn : (inner G).map d = inner G') (ψ : MulAut G) {ℓ : ℕ}
    (h : HasRankTwoPair (inner G' ⊔ Subgroup.zpowers (d ψ)) ℓ) :
    HasRankTwoPair (inner G ⊔ Subgroup.zpowers ψ) ℓ := by
  apply HasRankTwoPair.of_map d hd
  rw [Subgroup.map_sup, hinn, MonoidHom.map_zpowers]
  exact h

private theorem map_inner_centerQuotientHom (G : Type*) [Group G] :
    (inner G).map (centerQuotientHom G) = inner (G ⧸ Subgroup.center G) := by
  have key : ∀ g : G, centerQuotientHom G (MulAut.conj g) =
      MulAut.conj (QuotientGroup.mk g : G ⧸ Subgroup.center G) := by
    intro g
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    change onCenterQuotient (MulAut.conj g) (QuotientGroup.mk' (Subgroup.center G) y) = _
    rw [onCenterQuotient_apply_mk]
    change (QuotientGroup.mk (g * y * g⁻¹) : G ⧸ Subgroup.center G) = _
    simp [MulAut.conj_apply]
  ext a
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk g, (key g).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, key g⟩

section Descent

variable {f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 f F)

theorem exists_injective_descent_gramSU (hq : 4 ≤ 2 ^ f) :
    ∃ d : MulAut (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) →*
        MulAut (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)),
      Function.Injective d ∧
        (inner (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))).map d =
          inner (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  have hnq : ¬ (3 = 3 ∧ 2 ^ f = 2) := by rintro ⟨-, h2⟩; omega
  have hperf : Group.IsPerfect (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
    CFSG.RankThree.Classical.isPerfect_gramSU_one h le_rfl hnq
  have hZ := CFSG.RankThree.PartOne.CTP.center_gramSU_one_eq h hq
  let eZ : gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ⧸
      Subgroup.center (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ≃*
      primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  refine ⟨(MulAut.congr eZ).toMonoidHom.comp
    (centerQuotientHom (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))), ?_, ?_⟩
  · exact (MulAut.congr eZ).injective.comp (centerQuotientHom_injective _)
  · rw [← Subgroup.map_map, map_inner_centerQuotientHom]
    exact inner_map_congr eZ

private theorem not_dvd_card_normOneScalars [Finite F] {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ¬ ℓ ∣ 2 ^ f + 1) :
    ¬ ℓ ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3) := by
  intro hdvd
  obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hzo' : orderOf z = ℓ := (Subgroup.orderOf_mk z hz).symm.trans hzo
  obtain ⟨c, hc, -, hzc⟩ := hz
  have h1 : z ^ (2 ^ f + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hzc, ← map_pow]
    have : c ^ (2 ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← h.norm_eq_pow]
      exact hc
    rw [this, map_one]
    rfl
  exact hℓq (hzo' ▸ orderOf_dvd_of_pow_eq_one h1)

theorem hasRankTwoPair_gramSU_of_not_dvd [Finite F] (hf : 2 ≤ f) {ℓ : ℕ} [hℓF : Fact ℓ.Prime]
    (hℓq : ¬ ℓ ∣ 2 ^ f + 1)
    (hdvd : ℓ ∣ Nat.card (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    {ψ : MulAut (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))} {k : ℕ}
    (hψ : orderOf ψ = ℓ ^ k)
    (hψI : ψ ∉ inner (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) :
    HasRankTwoPair (inner (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⊔
      Subgroup.zpowers ψ) ℓ := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨d, hd, hinn⟩ := exists_injective_descent_gramSU h hq
  have hdvdP : ℓ ∣ Nat.card (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (normOneScalars h (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3)
    rw [h1] at hdvd
    rcases (Nat.Prime.dvd_mul hℓF.out).mp hdvd with h2 | h2
    · exact h2
    · exact absurd h2 (not_dvd_card_normOneScalars h hℓq)
  obtain ⟨k', hk'⟩ := (Nat.dvd_prime_pow hℓF.out).mp (hψ ▸ orderOf_map_dvd d ψ)
  have hαI : d ψ ∉ inner (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
    intro hmem
    rw [← hinn] at hmem
    obtain ⟨c, hc, hcψ⟩ := hmem
    exact hψI (hd hcψ ▸ hc)
  exact hasRankTwoPair_of_descend d hd hinn ψ
    (hasRankTwoPair_primeFormP h hf isPrimeFormGram_one hℓq hdvdP hk'.2 hαI)

end Descent

theorem k518RkSU3_holds : K518RkSU3 := by
  intro F _ _ _ f hf hcard ℓ hℓ hℓ2 hdvd ψ ⟨k, hk⟩ hψ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨W, hW⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix (p := 2) hcard 3
  let e : CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 3 ≃*
      gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    (CFSG.LieType.Universal.Unitary.conjEquiv W hW).trans (CFSG.RankThree.PartOne.CTP.suEquiv h)
  refine two_le_pRank_of_hasRankTwoPair ?_
  refine hasRankTwoPair_of_descend (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    (inner_map_congr e) ψ ?_
  by_cases hℓq : ℓ ∣ 2 ^ f + 1
  · exact hasRankTwoPair_gramSU_of_dvd h hℓ2 hℓq le_sup_left
  · have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      have h216 : Nat.card (CFSG.LieType.Universal.Unitary.SU
          (CFSG.LieType.BorelTits.unitaryInvolution F 2 1) 3) = 216 := by
        rw [CFSG.LieType.Steinberg.card_SU_three (p := 2) (f := 1) hcard]
        norm_num
      rw [h216] at hdvd
      have h27 : ℓ ∣ 2 ^ 3 * 3 ^ 3 := by simpa using hdvd
      rcases (Nat.Prime.dvd_mul hℓ).mp h27 with h2 | h3
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h2))
      · exact hℓq (by simpa using hℓ.dvd_of_dvd_pow h3)
    refine hasRankTwoPair_gramSU_of_not_dvd h hf2 hℓq ?_ (k := k) ?_ ?_
    · rw [← Nat.card_congr e.toEquiv]
      exact hdvd
    · exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective ψ).trans hk
    · intro hmem
      rw [← inner_map_congr e] at hmem
      obtain ⟨c, hc, hcψ⟩ := hmem
      exact hψ ((MulAut.congr e).injective hcψ ▸ hc)

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H
