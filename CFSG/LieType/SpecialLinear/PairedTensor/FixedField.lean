module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LieType.SpecialLinear

open FixedPoints

theorem orderOf_eq_two_of_trans_self {F : Type*} [Field F] [Finite F] (σ : F ≃+* F)
    (hσ2 : σ.trans σ = RingEquiv.refl F) (hσ1 : σ ≠ RingEquiv.refl F) :
    orderOf σ = 2 := by
  have hmul : σ * σ = σ.trans σ := by
    ext x
    simp [RingAut.mul_apply]
  have hpow : σ ^ 2 = 1 := by
    rw [pow_two, hmul, hσ2, RingAut.one_eq_refl]
  exact orderOf_eq_prime hpow (by rw [RingAut.one_eq_refl]; exact hσ1)

theorem nat_card_fixedBy_eq_nat_card_fixedSubfield {F : Type*} [Field F] [Finite F]
    (σ : F ≃+* F) :
    Nat.card {c : F // σ c = c} =
      Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F) := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers σ) F
  refine Nat.card_congr ?_
  refine
    { toFun := fun c =>
        ⟨c.1, by
          show ∀ g : Subgroup.zpowers σ, g • c.1 = c.1
          intro g
          rw [Subgroup.smul_def]
          exact smul_eq_self_of_mem_zpowers g.2 c.2⟩
      invFun := fun x =>
        ⟨x.1, by
          have hx : (⟨σ, Subgroup.mem_zpowers σ⟩ : Subgroup.zpowers σ) • x.1 = x.1 := x.2 _
          simpa [Subgroup.smul_def, RingHom.smul_def] using hx⟩
      left_inv := fun c => by ext; rfl
      right_inv := fun x => by ext; rfl }

theorem even_and_nat_card_fixed_of_order_two {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (σ : F ≃+* F)
    (hσ2 : σ.trans σ = RingEquiv.refl F) (hσ1 : σ ≠ RingEquiv.refl F) :
    Even f ∧ Nat.card {c : F // σ c = c} = 2 ^ (f / 2) := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers σ) F
  have hord : orderOf σ = 2 := orderOf_eq_two_of_trans_self σ hσ2 hσ1
  have hcard : Nat.card F = Nat.card R ^ orderOf σ := by
    simpa [R] using CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F σ
  have hm : Nat.card R ^ 2 = 2 ^ f := by
    rw [hord, hF] at hcard
    exact hcard.symm
  have hm_dvd : Nat.card R ∣ 2 ^ f := by
    rw [← hm, pow_two]
    exact dvd_mul_right _ _
  obtain ⟨s, _hsle, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hm_dvd
  have hpow : 2 ^ f = 2 ^ (2 * s) := by
    rw [← hm, hs, ← pow_mul, Nat.mul_comm]
  have hf : f = 2 * s := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hfeven : Even f := even_iff_exists_two_mul.mpr ⟨s, hf⟩
  have hdiv : f / 2 = s := by
    rw [hf]
    simp
  refine ⟨hfeven, ?_⟩
  rw [nat_card_fixedBy_eq_nat_card_fixedSubfield σ, hs, hdiv]

theorem nat_card_fixed_eq_pow_half_of_order_two {F : Type*} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (σ : F ≃+* F)
    (hσ2 : σ.trans σ = RingEquiv.refl F) (hσ1 : σ ≠ RingEquiv.refl F) :
    Nat.card {c : F // σ c = c} = 2 ^ (f / 2) :=
  (even_and_nat_card_fixed_of_order_two hF σ hσ2 hσ1).2

end CFSG.LieType.SpecialLinear
