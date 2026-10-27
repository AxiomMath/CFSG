module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecGroup
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenOneEight

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X7Sec
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.HardMathSupport.Cooperstein.Coordinator

open scoped MatrixGroups Matrix

theorem center_eq_bot_and_even_of_not_injective {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {Λ : Type} [Group Λ] {φ : SL(3, F) →* Λ} (hcov : Cover φ)
    (hφ : ¬ Function.Injective φ) : Subgroup.center Λ = ⊥ ∧ Even n := by
  classical
  obtain ⟨x, hxφ, hx1⟩ : ∃ x, φ x = 1 ∧ x ≠ 1 := by
    by_contra h
    push Not at h
    exact hφ ((injective_iff_map_eq_one φ).2 h)
  obtain ⟨c, hc3, hcx⟩ := hcov.ker_le x hxφ
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact hx1 (Subtype.ext (by rw [hcx, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hprim : IsPrimitiveRoot (c : F) 3 := by
    have h := IsPrimitiveRoot.orderOf c
    rw [hoc] at h
    exact IsPrimitiveRoot.coe_units_iff.2 h
  refine ⟨?_, ?_⟩
  ·
    rw [← hcov.map_scalars, eq_bot_iff]
    rintro _ ⟨y, ⟨d, hd3, hdy⟩, rfl⟩
    have hd3' : (d : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hd3, Units.val_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hd3'
    have hy : y = x ^ i := by
      refine Subtype.ext ?_
      rw [Matrix.SpecialLinearGroup.coe_pow, hdy, hcx, ← hi, map_pow]
    rw [Subgroup.mem_bot, hy, map_pow, hxφ, one_pow]
  ·
    have h3 : 3 ∣ Fintype.card Fˣ := hoc ▸ orderOf_dvd_card
    rw [Fintype.card_units, hF] at h3
    by_contra hne
    obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.1 hne
    have h4 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have key : ∀ m : ℕ, m % 3 = 2 → ¬ 3 ∣ m - 1 := fun m hm hdvd => by omega
    exact key _ h4 h3

theorem exists_irrFFOffender_of_center_eq_bot {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {H L : Subgroup (MulAut V)} (hLF : L = quasithinGenFitting H)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : CFSG.pCore 2 ↥H = ⊥) (hc : Subgroup.center ↥L = ⊥)
    (hFF : IsFFModule H) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (LW E : Subgroup (MulAut W)),
      (∀ w : W, w * w = 1) ∧ CFSG.IsQuasisimple ↥LW ∧ X1.IsIrrOn LW ∧ Nonempty (↥L ≃* ↥LW) ∧
        E ≤ Subgroup.normalizer (LW : Set (MulAut W)) ∧ E ≠ ⊥ ∧ IsElemAbelian2 E ∧
        IsQuadratic E ∧ Nat.card W ≤ Nat.card E * Nat.card (fixV E) := by
  have hV' : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  obtain ⟨A, hAH, hAne, hAel, hAoff⟩ := hFF
  obtain ⟨B, -, hB⟩ := exists_isBestOffender_le hAH hAne hAel hAoff
  have hLH : L ≤ H := hLF ▸ quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting H
  have hLcomp : Family.IsComp L H :=
    ⟨hLH, IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hHN)
      (IsSubnormal.refl H), ⟨hLq.1.commutator_eq_top, hLq.2.1⟩⟩
  have hLB : ⁅L, B⁆ ≠ ⊥ := commutator_ne_bot_of_elemAbelian hLF hO2 hB.1 hB.2.1 hB.2.2.1
  obtain ⟨hBN, -, ⟨sec⟩⟩ := Layer.Actor.irreducibleSectionProp V hV' H L B hLcomp hB hLB
  set ρ : ↥L →* MulAut sec.W := sec.τW.comp (Subgroup.inclusion le_sup_left) with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hφ : ∃ k, ρ.rangeRestrict k ≠ 1 := by
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 sec.lbar_ne_bot
    obtain ⟨k, hk⟩ := hsurj a
    exact ⟨k, hk ▸ ha⟩
  have hinj : Function.Injective ρ.rangeRestrict := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hLq hφ).trans hc.le
  exact ⟨sec.W, inferInstance, inferInstance, ρ.range,
    (sec.τW.comp (Subgroup.inclusion le_sup_right)).range,
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_sq hV' sec, sec.lbar_quasisimple,
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_isIrrOn sec,
    ⟨MulEquiv.ofBijective ρ.rangeRestrict ⟨hinj, hsurj⟩⟩,
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.irrSection_range_le_normalizer sec hBN,
    sec.abar_ne_bot, sec.abar_elem, sec.abar_quadratic, sec.abar_offender⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenOneEight
