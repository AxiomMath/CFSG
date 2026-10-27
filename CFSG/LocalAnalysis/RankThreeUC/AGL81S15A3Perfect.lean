module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Curtis.Proving.ActsTrivially
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutCentralAtDef
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.C1
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Curtis.Proving

theorem action_trivial_of_perfect {A L : Type*} [Group A] [Group L]
    (hcard : Nat.card A = 4)
    (hperf : Group.IsPerfect L) (ρ : L →* MulAut A) : ρ.range = ⊥ := by
  classical
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Group.IsPerfect L := hperf
  haveI hsolvPerm : Group.IsSolvable (Equiv.Perm A) :=
    Equiv.Perm.isSolvable (α := A) (by omega)
  have hinj : Function.Injective (MulAut.toPerm A : MulAut A →* Equiv.Perm A) := by
    intro f g h
    ext x
    exact congrFun (congrArg (fun e : Equiv.Perm A => (e : A → A)) h) x
  haveI hsolvAut : Group.IsSolvable (MulAut A) :=
    Group.isSolvable_of_isSolvable_injective (f := (MulAut.toPerm A : MulAut A →* Equiv.Perm A))
      hinj
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  haveI : Group.IsSolvable ρ.range := inferInstance
  have hsub : Subsingleton ρ.range := by
    by_contra h
    haveI : Nontrivial ρ.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable ρ.range inferInstance
  exact Subgroup.eq_bot_of_subsingleton ρ.range

end CFSG.LocalAnalysis.RankThreeUC.S15
