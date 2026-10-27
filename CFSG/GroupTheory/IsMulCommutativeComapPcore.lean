module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG

open scoped commutatorElement

theorem isMulCommutative_comap_quotient_pCore {L Q : Type} [Group L] [Group Q]
    (pi : L →* Q) (hpi : Function.Surjective pi) (hker : IsPGroup 2 (MonoidHom.ker pi))
    {B : Subgroup Q}
    (h : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B)) :
    IsMulCommutative (↥(B.comap pi) ⧸ CFSG.pCore 2 ↥(B.comap pi)) := by
  let C : Subgroup L := B.comap pi
  let f : C →* ↥B :=
    { toFun := fun x => ⟨pi x, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  let P : Subgroup C := (CFSG.pCore 2 ↥B).comap f
  have hfker : f.ker = (MonoidHom.ker pi).subgroupOf C := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    change f x = 1 ↔ pi x = 1
    rw [Subtype.ext_iff]
    rfl
  have hker2 : IsPGroup 2 f.ker := by
    rw [hfker]
    have h1 : IsPGroup 2 (C ⊓ MonoidHom.ker pi : Subgroup L) := hker.to_le inf_le_right
    have h2 : IsPGroup 2 ((C ⊓ MonoidHom.ker pi : Subgroup L).subgroupOf C) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    rwa [Subgroup.inf_subgroupOf_left] at h2
  have hP2 : IsPGroup 2 P :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).comap_of_ker_isPGroup f hker2
  have hPle : P ≤ CFSG.pCore 2 C := le_sSup ⟨inferInstance, hP2⟩
  have hcommB : _root_.commutator ↥B ≤ CFSG.pCore 2 ↥B :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp h
  have hcomm : _root_.commutator C ≤ P := by
    change ⁅(⊤ : Subgroup C), ⊤⁆ ≤ P
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_comap]
    change f ⁅x, y⁆ ∈ CFSG.pCore 2 ↥B
    rw [map_commutatorElement]
    exact hcommB (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) trivial trivial)
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (hcomm.trans hPle)

end CFSG
