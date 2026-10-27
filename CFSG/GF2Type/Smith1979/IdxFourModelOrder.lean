module

public import CFSG.GF2Type.Smith1979.IdxFourModelChain
public import Certificates.Certificate17600
public import Certificates.Certificate17601
public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
import Certificates.Data.Kernel.IdxFourChainK
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.IdxFourChainCard
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GF2Type.Smith1979.IdxFourModelBasic
public import CFSG.GF2Type.Smith1979.IdxFourModelChainInputs
public import Mathlib.GroupTheory.Schreier
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

theorem card_M0 : Nat.card M0 = 39191040 :=
  Certificates.certificate17600

theorem card_E0 : Nat.card E0 = 9797760 :=
  Certificates.certificate17601.1

theorem eq_one_of_fix_e0Base {U : V12 ≃ₗ[ZMod 2] V12}
    (hU : U ∈ E0) (hfix : ∀ b ∈ Chain.e0Base, Chain.codePerm U b = b) : U = 1 := by
  have key : ∀ b ∈ Chain.e0Base, U (vecOf b) = vecOf b := fun b hb => by
    have h := congrArg Fin.val (hfix b hb)
    rw [Chain.codePerm_apply] at h
    rw [← vecOf_codeOf (U (vecOf b)), h]
  refine Certificates.certificate17601.2 U hU fun b hb => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact key 12 (by decide)
  · exact key 20 (by decide)
  · exact key 264 (by decide)
  · exact key 36 (by decide)
  · exact key 63 (by decide)

end CFSG.GF2Type.Smith1979.IdxFour
