module

public import CFSG.LargeExtraspecial.AS35QIxCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS35QIx

variable {G : Type} [Group G] [Finite G] {S : Setting G}

@[expose] def invCenter (Y : Subgroup S.O) (τ : S.O) : Subgroup S.O where
  carrier := {x | x ∈ Y ∧ (∀ y ∈ Y, x * y = y * x) ∧ τ * x * τ⁻¹ = x⁻¹}
  mul_mem' {a b} ha hb := by
    refine ⟨Y.mul_mem ha.1 hb.1, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hb.2.1 y hy, ← mul_assoc, ha.2.1 y hy, mul_assoc]
    · have hab : a * b = b * a := ha.2.1 b hb.1
      calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
        _ = (b * a)⁻¹ := by rw [ha.2.2, hb.2.2]; group
        _ = (a * b)⁻¹ := by rw [hab]
  one_mem' := ⟨Y.one_mem, fun y _ => by rw [one_mul, mul_one], by group⟩
  inv_mem' {a} ha := by
    refine ⟨Y.inv_mem ha.1, fun y hy => ?_, ?_⟩
    · calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha.2.1 y hy]
        _ = y * a⁻¹ := by group
    · calc τ * a⁻¹ * τ⁻¹ = (τ * a * τ⁻¹)⁻¹ := by group
        _ = a⁻¹⁻¹ := by rw [ha.2.2]

namespace IxLift

variable (T : IxLift S)

theorem mem_zpowers_of_comm_tb (hS : S.SixHyp) {Y : Subgroup S.O} (hYM : Y ≤ S.Mbar)
    (hYn : ∀ m ∈ S.Mbar, ∀ x ∈ Y, m * x * m⁻¹ ∈ Y) (hY3 : IsPGroup 3 Y) {c : S.O} (hcY : c ∈ Y)
    (hct : c * T.tb = T.tb * c) : c ∈ zpowers T.ζ := by
  have := AS35QTh.finite_O S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPf := T.pbarFacts hS
  have hX3 : IsPGroup 3 T.X := IsPGroup.of_card (n := 3) (by rw [T.hX27]; norm_num)
  have hXN : T.X ≤ normalizer (Y : Set S.O) := fun x hx =>
    Setting.mem_normalizer_of_conj_le (hYn x (T.hXM hx)) (hYn _ (S.Mbar.inv_mem (T.hXM hx)))
  have hR3 : IsPGroup 3 (Y ⊔ T.X : Subgroup S.O) := hY3.to_sup_of_normal_left' hX3 hXN
  have hRM : (Y ⊔ T.X : Subgroup S.O) ≤ S.Mbar := sup_le hYM T.hXM
  have hRn : ∀ p ∈ S.PbarAsc T.g, ∀ x ∈ (Y ⊔ T.X : Subgroup S.O), p * x * p⁻¹ ∈ Y ⊔ T.X := by
    intro p hp x hx
    have hpM : p ∈ S.Mbar := hPf.le_Mbar hp
    have hle : (Y ⊔ T.X : Subgroup S.O) ≤
        (Y ⊔ T.X : Subgroup S.O).comap (MulAut.conj p).toMonoidHom := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact le_sup_left (b := T.X) (hYn p hpM y hy)
      · exact le_sup_right (a := Y) (T.hXn p hpM y hy)
    exact hle hx
  have hle := hPf.card_centralizer_le (S14.asc512FiveEightStmt G S hS T.g T.hgD T.hgM) hRM
    (AS35V.odd_card_of_isPGroup_three hR3) hRn
  have hζC : zpowers T.ζ ≤ (Y ⊔ T.X : Subgroup S.O) ⊓ centralizer ({T.tb} : Set S.O) :=
    zpowers_le.mpr (mem_inf.mpr ⟨le_sup_right (a := Y) T.hζX,
      mem_centralizer_singleton_iff.mpr T.zeta_comm_tb⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hζC (by
    rw [Nat.card_zpowers, AS35V.orderOf_eq_three_of_pow T.hζ3 T.hζ1]
    exact hle)
  rw [heq]
  exact mem_inf.mpr ⟨le_sup_left (b := T.X) hcY, mem_centralizer_singleton_iff.mpr hct⟩

include T in
theorem comm_of_mem_center (hS : S.SixHyp) {Y : Subgroup S.O} (hYM : Y ≤ S.Mbar)
    (hYn : ∀ m ∈ S.Mbar, ∀ x ∈ Y, m * x * m⁻¹ ∈ Y) (hY3 : IsPGroup 3 Y) {c : S.O} (hcY : c ∈ Y)
    (hc : ∀ x ∈ Y, c * x = x * c) : ∀ m ∈ S.Mbar, m * c = c * m := by
  have := AS35QTh.finite_O S
  have hζM := T.comm_zeta hS
  have hPf := T.pbarFacts hS
  have hodd := AS35V.odd_card_of_isPGroup_three hY3
  have hτ2 : orderOf T.tb = 2 := Setting.orderOf_eq_two_of_isTypeA' hPf.typeA
  obtain ⟨c₀, hc₀Y, hc₀t, w, hwY, hwt, rfl⟩ := AS35V.exists_fixed_mul_inverted hτ2 hodd
    (Setting.mem_normalizer_of_conj_le (hYn _ T.tb_mem_Mbar)
      (hYn _ (S.Mbar.inv_mem T.tb_mem_Mbar))) hcY
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (T.mem_zpowers_of_comm_tb hS hYM hYn hY3 hc₀Y hc₀t)
  have hc₀M : ∀ m ∈ S.Mbar, m * c₀ = c₀ * m := fun m hm => by
    rw [← hk]
    exact (Commute.zpow_right (hζM m hm) k).eq
  have hw1 : w = 1 := by
    by_contra hw1
    have hwc : ∀ y ∈ Y, w * y = y * w := by
      intro y hy
      have h1 := hc y hy
      have h2 := hc₀M y (hYM hy)
      calc w * y = c₀⁻¹ * (c₀ * w * y) := by group
        _ = c₀⁻¹ * (y * (c₀ * w)) := by rw [h1]
        _ = c₀⁻¹ * (y * c₀) * w := by group
        _ = c₀⁻¹ * (c₀ * y) * w := by rw [h2]
        _ = y * w := by group
    refine hPf.false_of_inverts_subgroup (A := invCenter Y T.tb)
      (Odd.of_dvd_nat hodd (card_dvd_of_le fun x hx => hx.1)) (fun p hp x hx => ?_)
      (fun x hx => hx.2.2) ⟨hwY, hwc, hwt⟩ hw1
    have hpM : p ∈ S.Mbar := hPf.le_Mbar hp
    refine ⟨hYn p hpM x hx.1, fun y hy => ?_, hPf.conj_inverted hp hx.2.2⟩
    have hy' : p⁻¹ * y * p⁻¹⁻¹ ∈ Y := hYn _ (S.Mbar.inv_mem hpM) y hy
    have e := hx.2.1 _ hy'
    calc p * x * p⁻¹ * y = p * (x * (p⁻¹ * y * p⁻¹⁻¹)) * p⁻¹ := by group
      _ = p * ((p⁻¹ * y * p⁻¹⁻¹) * x) * p⁻¹ := by rw [e]
      _ = y * (p * x * p⁻¹) := by group
  rw [hw1, mul_one]
  exact hc₀M

end IxLift

end AS35QIx

namespace S14

theorem asc512ThomasIndexTwoStmt : Asc512ThomasIndexTwoStmt := by
  intro G _ _ S hS hth Y hYM hYn hY3 c hcY hc
  obtain ⟨T₀⟩ := AS35QIx.exists_ixSetup hS hth
  obtain ⟨T⟩ := T₀.exists_lift hS
  exact T.comm_of_mem_center hS hYM hYn hY3 hcY hc

end S14

end CFSG.LargeExtraspecial
