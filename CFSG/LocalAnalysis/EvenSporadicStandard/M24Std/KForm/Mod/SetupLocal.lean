module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Setting
public import CFSG.LocalAnalysis.ComponentClassification.FixedNormalCentralizer

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixed_pCore_le_center {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal] {z : K}
    {ψ : ↥(centralizer ({z} : Set K)) →* Z2S6}
    (hψ : ModData z (alternatingGroup (Fin 6)) ψ) :
    CFSG.pCore 2 ↥(fixedSubgroup (MulAut.conjNormal (H := S) z)) ≤
      center ↥(fixedSubgroup (MulAut.conjNormal (H := S) z)) := by
  let C := centralizer ({z} : Set K)
  let T : Subgroup C := S.subgroupOf C
  let eF := CFSG.ComponentClassification.FixedNormalCentralizer.equivalence S z
  have hmap : (CFSG.pCore 2 T).map eF.toMonoidHom =
      CFSG.pCore 2 ↥(fixedSubgroup (MulAut.conjNormal (H := S) z)) :=
    CFSG.pCore_map_iso 2 eF
  rw [← hmap]
  rintro x ⟨y, hy, rfl⟩
  let P : Subgroup C := (CFSG.pCore 2 T).map T.subtype
  have hPp : IsPGroup 2 P :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥T)) T.subtype
  haveI hPn : P.Normal := by
    dsimp only [P]
    exact ConjAct.normal_of_characteristic_of_normal
  have hz : ((eF.toMonoidHom y : ↥(fixedSubgroup (MulAut.conjNormal (H := S) z))) : K) ∈
      zpowers z := by
    have hmem : (T.subtype (y : T) : K) ∈ zpowers z :=
      hψ.le_zpowers_of_normal_two hPp (T.subtype (y : T))
        (Subgroup.mem_map_of_mem T.subtype hy)
    rw [show ((eF.toMonoidHom y :
        ↥(fixedSubgroup (MulAut.conjNormal (H := S) z))) : K) =
        (T.subtype (y : T) : K) from rfl]
    exact hmem
  rw [Subgroup.mem_center_iff]
  intro f
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hfz : Commute (f : K) z := by
    have h2 : z * (f : K) * z⁻¹ = (f : K) := by
      have h1 : (MulAut.conjNormal (H := S) z) (f : S) = (f : S) := f.property
      simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val h1
    have h3 : z * (f : K) = (f : K) * z := by
      calc z * (f : K) = z * (f : K) * z⁻¹ * z := by group
        _ = (f : K) * z := by rw [h2]
    exact h3.symm
  apply Subtype.ext
  apply Subtype.ext
  show (f : K) * ((eF.toMonoidHom y :
      ↥(fixedSubgroup (MulAut.conjNormal (H := S) z))) : K) =
    ((eF.toMonoidHom y : ↥(fixedSubgroup (MulAut.conjNormal (H := S) z))) : K) * (f : K)
  rw [← hk]
  exact hfz.zpow_right k

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
