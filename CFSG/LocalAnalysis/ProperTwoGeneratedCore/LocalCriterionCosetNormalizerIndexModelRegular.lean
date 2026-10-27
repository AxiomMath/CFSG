module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {L : Type u} {F : Type v} [Group L] [Group F]

theorem simpleBender_borel_every_sylow_regular [Finite F] {B : Subgroup F}
    (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup F) (Q : Sylow 2 B) :
    (Q : Subgroup B).Normal ∧
      IsRegularOn ((Q : Subgroup B).map B.subtype)
        {omega : F ⧸ B | omega ≠ QuotientGroup.mk 1} := by
  obtain ⟨P, hP, hreg⟩ := simpleBender_borel_normalSylow_regular hB hmodel
  let := Sylow.unique_of_normal P hP
  have hQP : Q = P := Subsingleton.elim _ _
  simpa only [hQP] using And.intro hP hreg

theorem simpleBender_borel_preimage_sylow_regular [Finite L] [Finite F]
    (f : L →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (B : Subgroup F) (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup F)
    (R : Sylow 2 (B.comap f)) :
    letI : MulAction L (F ⧸ B) := MulAction.compHom (F ⧸ B) f
    IsRegularOn ((R : Subgroup (B.comap f)).map (B.comap f).subtype)
      {omega : F ⧸ B | omega ≠ QuotientGroup.mk 1} := by
  let fb : B.comap f →* B := f.subgroupComap B
  have hfb : Function.Surjective fb := f.subgroupComap_surjective B hf
  let Q : Sylow 2 B := R.mapSurjective hfb
  let A : Subgroup L := (R : Subgroup (B.comap f)).map (B.comap f).subtype
  have hA : IsPGroup 2 A := R.isPGroup'.map (B.comap f).subtype
  have himage : A.map f = (Q : Subgroup B).map B.subtype := by
    change ((R : Subgroup (B.comap f)).map (B.comap f).subtype).map f =
      ((R.mapSurjective hfb : Sylow 2 B) : Subgroup B).map B.subtype
    rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hreg : IsRegularOn (A.map f)
      {omega : F ⧸ B | omega ≠ QuotientGroup.mk 1} := by
    rw [himage]
    exact (simpleBender_borel_every_sylow_regular hB hmodel Q).2
  exact regularOn_compHom_of_odd_kernel f hodd A hA _ hreg

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
