module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32AC38d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_isSolvable_range_F4 (h29 : Thm14_7_29_F4)
    (hW : C.Wt = tildeOf (fsuV1 T V) (conjClosure V H)) (hs : Group.IsSolvable ↥C.ψ.range) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker2 : IsPGroup 2 ↥C.ψ.ker := by
    rintro ⟨k, hk⟩
    have hkQ : (k : G) ∈ pCoreOf 2 H := C.mem_pCoreOf_of_ψ hW k.2 hk
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hkQ⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hm
    simpa using this
  have : Group.IsNilpotent ↥C.ψ.ker := hker2.isNilpotent
  have : Group.IsSolvable ↥C.ψ.ker := inferInstance
  have hsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_ker_le_range C.ψ.ker.subtype C.ψ.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  exact C.S.hz.2.2 (h29 G T L V C.S.hyp H C.S.hz.1.1 C.S.hz.2.1 hsolv)

end Ctx38

end CFSG.Quasithin.H13.L32A.C
