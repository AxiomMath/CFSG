module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSCentralExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverModel

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift
  CFSG.EvenSporadicStandard.TwoHS

theorem sq_eq_one_of_card_centralizer
    {E : Type} [Group E] [Finite E]
    (hperf : Group.IsPerfect E) (hZ : Nat.card (center E) = 2)
    (hq : IsSporadic (E ⧸ center E) .HS) {m : E}
    (hm : orderOf (QuotientGroup.mk m : E ⧸ center E) = 2)
    (hC : Nat.card ↥(centralizer ({(QuotientGroup.mk m : E ⧸ center E)} :
      Set (E ⧸ center E))) = 7680) : m ^ 2 = 1 := by
  let q : E →* E ⧸ center E := QuotientGroup.mk' (center E)
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqk : q.ker = center E := QuotientGroup.ker_mk' _
  obtain ⟨e₀⟩ := id hq
  let θ : (E ⧸ center E) ≃* ↥hsP := (e₀ : (E ⧸ center E) ≃* NativeSporadic.HS).trans hsPermEquiv
  obtain ⟨a₁, a₂, a₃, n, hE8, -, -⟩ := cover_datum
  have hE8' := hE8.map θ.symm.toMonoidHom θ.symm.injective
  obtain ⟨b₁, -, -, hb1, -, -, hb₁sq, -, -, -, -, -⟩ := hE8'.exists_lift hqs hqk.le
  have hb1ne : q b₁ ≠ 1 := by
    rw [hb1]
    exact hE8'.ne_one
  have hbord : orderOf (q b₁) = 2 := by
    refine orderOf_eq_prime ?_ hb1ne
    rw [← map_pow, hb₁sq, map_one]
  have hCb : Nat.card ↥(centralizer ({q b₁} : Set (E ⧸ center E))) = 7680 :=
    Zassenhaus.card_centralizer_eq_of_sq_eq_one hperf hZ hq q hqs hqk hb₁sq hb1ne
  have hconj : IsConj (QuotientGroup.mk m : E ⧸ center E) (q b₁) :=
    Zassenhaus.isConj_of_card_centralizer_eq_hs hq _ _ hm hbord (hC.trans hCb.symm)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨c', rfl⟩ := hqs c
  have hqn : q (c' * m * c'⁻¹) = q b₁ := by
    rw [map_mul, map_mul, map_inv]
    exact hc
  have hw : (c' * m * c'⁻¹)⁻¹ * b₁ ∈ center E := by
    rw [← hqk, MonoidHom.mem_ker, map_mul, map_inv, hqn, inv_mul_cancel]
  set w := (c' * m * c'⁻¹)⁻¹ * b₁ with hwdef
  have hw2 : w ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := center E) (x := (⟨w, hw⟩ : center E))
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hbw : b₁ = (c' * m * c'⁻¹) * w := by
    rw [hwdef]
    group
  have hwc : ∀ g : E, g * w = w * g := fun g => Subgroup.mem_center_iff.1 hw g
  have hsq : (c' * m * c'⁻¹) ^ 2 = 1 := by
    have h1 : b₁ ^ 2 = (c' * m * c'⁻¹) ^ 2 * w ^ 2 := by
      rw [hbw, pow_two, pow_two, pow_two]
      calc c' * m * c'⁻¹ * w * (c' * m * c'⁻¹ * w)
          = c' * m * c'⁻¹ * (w * (c' * m * c'⁻¹)) * w := by group
        _ = c' * m * c'⁻¹ * ((c' * m * c'⁻¹) * w) * w := by rw [← hwc (c' * m * c'⁻¹)]
        _ = c' * m * c'⁻¹ * (c' * m * c'⁻¹) * (w * w) := by group
    rw [hb₁sq, hw2, mul_one] at h1
    exact h1.symm
  calc m ^ 2 = c'⁻¹ * ((c' * m * c'⁻¹) * (c' * m * c'⁻¹)) * c' := by
        rw [pow_two]
        group
    _ = c'⁻¹ * (c' * m * c'⁻¹) ^ 2 * c' := by rw [pow_two]
    _ = 1 := by rw [hsq]; group

end CFSG.EvenSporadicStandard.HSStd.PumpHS
