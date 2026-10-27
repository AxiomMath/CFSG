module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCenterTrans
import CFSG.Sporadic.Bridge.J4Surj
import CFSG.Sporadic.Schreier.J4SEleven
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.Sporadic.J4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

private theorem zmod11_two_generates :
    ∀ t : ZMod 11, t ≠ 0 → ∃ m : ℕ, ((2 : ℤ) : ZMod 11) ^ m = t := by
  have h : ∀ t : ZMod 11, t ≠ 0 → ∃ m : Fin 10, ((2 : ℤ) : ZMod 11) ^ (m : ℕ) = t := by
    decide +kernel
  intro t ht
  obtain ⟨m, hm⟩ := h t ht
  exact ⟨m, hm⟩


private theorem zin_Q11 : Zin Q11 = Subgroup.zpowers qz := center_Q11

private theorem j4_centerTransAt : CenterTransAt (Q11Sylow : Subgroup J) := by
  rw [Q11Sylow_coe]
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine centerTransAt_of_generator (p := 11) Q11 (z := qz) (n := nrm₂) (δ := 2) zin_Q11
    orderOf_qz nrm₂_mem_normalizer ?_ zmod11_two_generates
  simpa using nrm₂_qz

theorem j4_transCenter :
    ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerTransitiveCenter 11 K := by
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  haveI : Finite J := Finite.of_equiv K eKJ.toEquiv
  exact @normalizerTransitiveCenter_of_equiv K J _ (Subgroup.toGroup J) _ _ 11 (by norm_num) eKJ
    Q11Sylow j4_centerTransAt

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
