module

public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Defs
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Dih
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Y

variable {Y : Type} [Group Y] [Finite Y]

theorem kBar_comm_of_map_comm (Λ : Subgroup Y) (a c : ↥Λ)
    (h : barMk Y (a : Y) * barMk Y (c : Y) = barMk Y (c : Y) * barMk Y (a : Y)) :
    (QuotientGroup.mk a : kBar Λ) * QuotientGroup.mk c = QuotientGroup.mk c * QuotientGroup.mk a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N' : Subgroup ↥Λ := (pPrimeCore 2 Y).subgroupOf Λ
  have hN'n : N'.Normal := (pPrimeCore_normal : (pPrimeCore 2 Y).Normal).subgroupOf Λ
  let ι : ↥N' →* ↥(pPrimeCore 2 Y) :=
    (Λ.subtype.comp N'.subtype).codRestrict (pPrimeCore 2 Y) (fun m => m.2)
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : (ι a).val = (ι b).val := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hN'odd : Odd (Nat.card ↥N') :=
    Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := Y)))
      (Subgroup.card_dvd_of_injective ι hι)
  have hle : N' ≤ pPrimeCore 2 ↥Λ :=
    GroupTheory.le_pPrimeCore_of_normal hN'n (Nat.coprime_two_left.2 hN'odd)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  apply hle
  rw [Subgroup.mem_subgroupOf, ← ker_barMk, MonoidHom.mem_ker]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  rw [h]
  group

theorem not_comm_of_involution (Λ : Subgroup Y) (hcen : Subgroup.center (kBar Λ) = ⊥) {z : Y}
    (hzΛ : z ∈ Λ) (hz2 : orderOf z = 2) :
    ¬ ∀ c ∈ Λ, barMk Y z * barMk Y c = barMk Y c * barMk Y z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hall
  have hmem : (QuotientGroup.mk (⟨z, hzΛ⟩ : ↥Λ) : kBar Λ) ∈ Subgroup.center (kBar Λ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    exact (kBar_comm_of_map_comm Λ c ⟨z, hzΛ⟩ (hall c c.2).symm)
  rw [hcen, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  have hord : orderOf (⟨⟨z, hzΛ⟩, hmem⟩ : ↥(pPrimeCore 2 ↥Λ)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hz2
  have hdvd := orderOf_dvd_natCard (⟨⟨z, hzΛ⟩, hmem⟩ : ↥(pPrimeCore 2 ↥Λ))
  rw [hord] at hdvd
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥Λ)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥Λ))
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem pump_dichotomy {s w z b : Y} (hs : orderOf s = 2) (hwc : ∀ y : Y, w * y = y * w)
    {Λ : Subgroup Y} (hΛC : Λ ≤ centralizer ({s} : Set Y))
    (hΛ : TwoComponents.IsTwoComponent (Λ.subgroupOf (centralizer ({s} : Set Y))))
    (hcen : Subgroup.center (kBar Λ) = ⊥) (hzΛ : z ∈ Λ) (hz2 : orderOf z = 2)
    (hb : b * z * b⁻¹ = w * z) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧
      ((conjSub (barMk Y s)⁻¹ L = L ∧ Λ.map (barMk Y) ≤ L ∧ barMk Y w ∈ L ∧
          ∀ l ∈ L, barMk Y w * l = l * barMk Y w) ∨
        (conjSub (barMk Y s)⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub (barMk Y s)⁻¹ L⁆ = ⊥,
          Λ.map (barMk Y) ≤ (swapDiag hAB).range)) := by
  obtain ⟨-, -, L, hL, hcases, -, -, -⟩ := TwoThin.pumpupY_structure hs hΛC hΛ
  refine ⟨L, hL, ?_⟩
  rcases hcases with ⟨hst, hΛL⟩ | hdiag
  · left
    refine ⟨hst, hΛL, ?_⟩
    have hzL : barMk Y z ∈ L := hΛL ⟨z, hzΛ, rfl⟩
    have hwcen : ∀ y : barQ Y, barMk Y w * y = y * barMk Y w := fun y => by
      obtain ⟨y', rfl⟩ := barMk_surjective (Y := Y) y
      rw [← map_mul, ← map_mul, hwc y']
    set L' : Subgroup (barQ Y) := L.map (MulAut.conj (barMk Y b)).toMonoidHom with hL'
    have hL'c : CFSG.IsComponent L' := LocalCores.isComponent_map_mulEquiv _ hL
    have hf₁ : barMk Y (w * z) ∈ L' := by
      refine ⟨barMk Y z, hzL, ?_⟩
      rw [← hb, map_mul, map_mul, map_inv]
      simp [MulAut.conj_apply]
    rcases LocalCores.distinct_components_commute hL hL'c with hLL' | hcomm
    · have hf₁L : barMk Y (w * z) ∈ L := hLL' ▸ hf₁
      have hπw : barMk Y w = barMk Y (w * z) * (barMk Y z)⁻¹ := by rw [map_mul]; group
      have hwL : barMk Y w ∈ L := by
        rw [hπw]
        exact L.mul_mem hf₁L (L.inv_mem hzL)
      exact ⟨hwL, fun l _ => hwcen l⟩
    · exfalso
      have hle : L ≤ centralizer ((L' : Subgroup (barQ Y)) : Set (barQ Y)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
      refine not_comm_of_involution Λ hcen hzΛ hz2 (fun c hc => ?_)
      have hcL : barMk Y c ∈ L := hΛL ⟨c, hc, rfl⟩
      have h1 : barMk Y (w * z) * barMk Y c = barMk Y c * barMk Y (w * z) :=
        (Subgroup.mem_centralizer_iff.1 (hle hcL)) _ hf₁
      have hzπ : barMk Y z = (barMk Y w)⁻¹ * barMk Y (w * z) := by rw [map_mul]; group
      rw [hzπ]
      calc (barMk Y w)⁻¹ * barMk Y (w * z) * barMk Y c
          = (barMk Y w)⁻¹ * (barMk Y (w * z) * barMk Y c) := by group
        _ = (barMk Y w)⁻¹ * (barMk Y c * barMk Y (w * z)) := by rw [h1]
        _ = ((barMk Y w)⁻¹ * barMk Y c) * barMk Y (w * z) := by group
        _ = (barMk Y c * (barMk Y w)⁻¹) * barMk Y (w * z) := by
          rw [show (barMk Y w)⁻¹ * barMk Y c = barMk Y c * (barMk Y w)⁻¹ from by
            have := hwcen (barMk Y c)
            calc (barMk Y w)⁻¹ * barMk Y c = (barMk Y w)⁻¹ * (barMk Y c * barMk Y w) * (barMk Y w)⁻¹ := by group
              _ = (barMk Y w)⁻¹ * (barMk Y w * barMk Y c) * (barMk Y w)⁻¹ := by rw [this]
              _ = barMk Y c * (barMk Y w)⁻¹ := by group]
        _ = barMk Y c * ((barMk Y w)⁻¹ * barMk Y (w * z)) := by group
  · right
    obtain ⟨hne, hAB, hΛΔ⟩ := hdiag
    exact ⟨hne, hAB, hΛΔ⟩

end Y

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
