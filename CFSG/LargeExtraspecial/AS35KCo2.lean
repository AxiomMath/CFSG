module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.LargeExtraspecial.AS35DFourSeven
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {H : Type} [Group H] (T : Setting H)

theorem conj_z_cases_of_zGen {α : H ≃* H}
    (h : (∀ l ∈ T.zGen, α l = l) ∨ ∀ l ∈ T.zGen, α l = T.z * l * T.z⁻¹) :
    (∀ g : H, α (g * T.z * g⁻¹) = g * T.z * g⁻¹) ∨
      ∀ g : H, α (g * T.z * g⁻¹) = T.z * (g * T.z * g⁻¹) * T.z⁻¹ :=
  h.imp (fun h g => h _ (T.conj_mem_zGen g)) fun h g => h _ (T.conj_mem_zGen g)

theorem eq_one_or_z_of_forall_commute [Finite H] {c : H} (hc : ∀ q ∈ T.QG, c * q = q * c) :
    c = 1 ∨ c = T.z := by
  classical
  have hmem : c ∈ centralizer (T.QG : Set H) :=
    mem_centralizer_iff.mpr fun q hq => (hc q hq).symm
  rw [T.centralizer_QG_eq, mem_zpowers_iff_mem_range_orderOf, T.orderOf_z] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, rfl⟩ := hmem
  interval_cases k
  · exact Or.inl (pow_zero _)
  · exact Or.inr (pow_one _)

theorem zGen_eq_top_of_forall_inner (hC : centralizer (T.zGen : Set H) = ⊥)
    (h : ∀ α : MulAut T.zGen, ∃ g : T.zGen, α = MulAut.conj g) : T.zGen = ⊤ := by
  have := T.zGen_normal
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, hg⟩ := h (MulAut.conjNormal x)
  have hxg : (g : H)⁻¹ * x ∈ centralizer (T.zGen : Set H) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun β : MulAut T.zGen => ((β ⟨l, hl⟩ : T.zGen) : H)) hg
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc l * ((g : H)⁻¹ * x) = (g : H)⁻¹ * ((g : H) * l * (g : H)⁻¹) * x := by group
      _ = (g : H)⁻¹ * (x * l * x⁻¹) * x := by rw [← h1]
      _ = (g : H)⁻¹ * x * l := by group
  rw [hC, mem_bot] at hxg
  have hx : x = g := by
    calc x = (g : H) * ((g : H)⁻¹ * x) := by group
      _ = g := by rw [hxg, mul_one]
  rw [hx]
  exact g.2

end Setting

namespace S14

theorem card_timmesfeldPSU_six_le_card_Co2 :
    Nat.card (CFSG.Open.timmesfeldPSU 6) ≤ Nat.card CFSG.Blueprint.NativeSporadic.Co2 := by
  rw [Nat.card_congr ((timmesfeldPSUEquiv (n := 6) (by norm_num)).trans
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv unitaryFieldData_two_one
      (n := 6) (by norm_num))).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl
      (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) (by norm_num),
    CFSG.Sporadic.Co2.card_Co2]
  decide

theorem aschTwoAut_of_co2
    {H : Type} [Group H] [Finite H] (T : Setting H)
    (hC : centralizer (T.zGen : Set H) = ⊥) (hw : T.width = 4)
    (e : T.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    (∀ α : H ≃* H, (∀ q ∈ T.QG, α q = q) →
      (∀ g : H, α (g * T.z * g⁻¹) = g * T.z * g⁻¹) ∨
        ∀ g : H, α (g * T.z * g⁻¹) = T.z * (g * T.z * g⁻¹) * T.z⁻¹) ∧
    (∀ g : H, ∃ l ∈ T.zGen, g * T.z * g⁻¹ = l * T.z * l⁻¹) ∧
    Nat.card (CFSG.Open.timmesfeldPSU (T.width + 2)) ≤ Nat.card T.zGen := by
  have htop := T.zGen_eq_top_of_forall_inner hC
    (CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model T.zGen e)
  refine ⟨fun α hα => ?_, fun g => ⟨g, htop ▸ mem_top g, rfl⟩, ?_⟩
  · obtain ⟨g, hg⟩ := CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner_model H
      (((MulEquiv.subgroupCongr htop).trans topEquiv).symm.trans e) α
    have hgc : ∀ q ∈ T.QG, g * q = q * g := fun q hq => by
      have h1 : g * q * g⁻¹ = q := by
        rw [← MulAut.conj_apply, ← hg]
        exact hα q hq
      calc g * q = g * q * g⁻¹ * g := by group
        _ = q * g := by rw [h1]
    refine T.conj_z_cases_of_zGen ?_
    rcases T.eq_one_or_z_of_forall_commute hgc with rfl | rfl
    · exact Or.inl fun l _ => by rw [hg, MulAut.conj_apply, one_mul, inv_one, mul_one]
    · exact Or.inr fun l _ => by rw [hg, MulAut.conj_apply]
  · rw [hw, Nat.card_congr e.toEquiv]
    exact card_timmesfeldPSU_six_le_card_Co2

end S14

end CFSG.LargeExtraspecial
