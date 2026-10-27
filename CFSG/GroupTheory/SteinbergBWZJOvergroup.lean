module

public import CFSG.RankThree.PGroups.ZJCenterIntersection

public section

namespace CFSG.GroupTheory.ZJ

open Subgroup CFSG.RankThree.PGroups

variable {S : Type*} [Group S] [Finite S]

omit [Finite S] in
theorem isMulCommutative_subgroupOf {P B : Subgroup S} (hB : IsMulCommutative B) :
    IsMulCommutative (B.subgroupOf P) :=
  ⟨⟨fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : B => (t : S))
      (hB.is_comm.comm ⟨((x : P) : S), x.2⟩ ⟨((y : P) : S), y.2⟩)⟩⟩

end CFSG.GroupTheory.ZJ
