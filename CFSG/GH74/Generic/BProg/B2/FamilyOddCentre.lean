module

public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace FamilyOddCentre

theorem odd_central_eq_one {Y : Type} [Group Y] [Finite Y] (hcore : pPrimeCore 2 Y = ⊥)
    {L : Subgroup Y} (hL : IsComponent L) {z : Y} (hz : z ∈ L) (hzc : ∀ g ∈ L, g * z = z * g)
    (hodd : Odd (orderOf z)) : z = 1 := by
  have hsub : (Subgroup.zpowers z).IsSubnormal := by
    have hle : Subgroup.zpowers z ≤ L := (Subgroup.zpowers_le).2 hz
    refine Subgroup.IsSubnormal.trans hle ?_ hL.2
    have hN : ((Subgroup.zpowers z).subgroupOf L).Normal := by
      refine ⟨fun w hw g => ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hw)
      rw [Subgroup.mem_subgroupOf]
      have hcomm : ((g : Y) * w * (g : Y)⁻¹) = (w : Y) := by
        rw [← hk]
        have hg : (g : Y) * z = z * g := hzc g g.2
        have h1 : (g : Y) * z * (g : Y)⁻¹ = z := by rw [hg]; group
        calc (g : Y) * z ^ k * (g : Y)⁻¹ = ((g : Y) * z * (g : Y)⁻¹) ^ k := conj_zpow.symm
          _ = z ^ k := by rw [h1]
      show (g * w * g⁻¹ : L).1 ∈ Subgroup.zpowers z
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm]; exact hw
    exact hN.isSubnormal
  have hcard : Odd (Nat.card (Subgroup.zpowers z)) := by
    rw [Nat.card_zpowers]; exact hodd
  have hbot := Walter.eq_bot_of_isSubnormal_of_odd hcore hsub hcard
  have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

theorem eq_one_of_odd_central {Y J : Type} [Group Y] [Finite Y] [Group J]
    (hcore : pPrimeCore 2 Y = ⊥) {L : Subgroup Y} (hL : IsComponent L) (e : L ≃* J) {z : J}
    (hzc : ∀ g : J, g * z = z * g) (hzodd : Odd (orderOf z)) : z = 1 := by
  have hcen : ∀ g ∈ L, g * ((e.symm z : L) : Y) = ((e.symm z : L) : Y) * g := by
    intro g hg
    have h1 : (⟨g, hg⟩ : L) * e.symm z = e.symm z * ⟨g, hg⟩ := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hzc _
    exact congrArg Subtype.val h1
  have hord : Odd (orderOf ((e.symm z : L) : Y)) := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hzodd
  have h1 := odd_central_eq_one hcore hL (e.symm z).2 hcen hord
  have h2 : e.symm z = 1 := Subtype.ext h1
  have := congrArg e h2
  simpa using this

end FamilyOddCentre

theorem weakSig2NormG4_of_odd_central {J : Type} [Group J]
    (hz : ∃ z : J, z ≠ 1 ∧ (∀ g : J, g * z = z * g) ∧ Odd (orderOf z)) : WeakSig2NormG4 J := by
  obtain ⟨z, hz1, hzc, hzodd⟩ := hz
  intro Y _ _ hcore _ L hL hLJ D W hD hk hW hDW hC hN
  obtain ⟨e⟩ := hLJ
  exact absurd (FamilyOddCentre.eq_one_of_odd_central hcore hL e hzc hzodd) hz1

end CFSG.GH74.Generic.BProg.B2
