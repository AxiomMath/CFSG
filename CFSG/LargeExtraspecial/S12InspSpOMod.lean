module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.S12InspPSLDec
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem spo_t_mem {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    ∃ htX : t ∈ S.Xbar12 g, (⟨t, htX⟩ : S.Xbar12 g) ≠ 1 ∧
      (⟨t, htX⟩ : S.Xbar12 g) * ⟨t, htX⟩ = 1 ∧
      finrank (ZMod 2) (commSpace (S.actX12 g ⟨t, htX⟩)) ≤ 2 := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  refine ⟨htX, fun h => htA.2.1 ?_, Subtype.ext (Subtype.ext htA.2.2.1), htA.2.2.2.1.le⟩
  have := congrArg (fun x : S.Xbar12 g => ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
  simpa using this

end Setting

end CFSG.LargeExtraspecial
