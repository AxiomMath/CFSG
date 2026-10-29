module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.Input43
public import CFSG.GF2Type.Aschbacher1976Common.NotWeaklyClosed

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG

theorem cyclicFourNotWeaklyClosed :
    CyclicFourNotWeaklyClosed := by
  intro G _ _ _ z hset Z hzZ hZcyc hZ4
  obtain ⟨hnab, -, hchar, he, -⟩ := hset
  obtain ⟨x, hx⟩ := hZcyc.exists_generator
  have hZx : Subgroup.zpowers (x : G) = Z := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact Subgroup.zpow_mem Z x.2 k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      simpa using congrArg Subtype.val hk
  have hxo : orderOf (x : G) = 4 := by
    rw [← Nat.card_zpowers, hZx, hZ4]
  have hnwc := CFSG.GF2Type.Aschbacher1976Common.not_weaklyClosed_of_charTwo hnab hchar
    (by omega) hxo
  rw [hZx] at hnwc
  unfold CFSG.EvenSporadicStandard.Finkelstein77.WeaklyClosedInNormalizer at hnwc
  push Not at hnwc
  obtain ⟨h, hle, hne⟩ := hnwc
  have hconj : conjugate Z h⁻¹ = Z.map (MulAut.conj h).toMonoidHom := by
    unfold conjugate
    rw [inv_inv]
  exact ⟨h⁻¹, hconj ▸ hle, hconj ▸ hne⟩

end CFSG.GF2Type.Aschbacher1976HigherCenter
