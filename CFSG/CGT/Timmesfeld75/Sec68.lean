module

public import CFSG.CGT.Timmesfeld75.Sec68Basic
public import CFSG.CGT.Timmesfeld75.Sec68Stmt

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem step68_of (h214 : Lemma214) (hInv : InvolutionClassInput) (hIso : Section3IsoInput)
    (h57 : Step57) (h1 : Sec4NoA) (h63 : Sec63) (hC : Sec68CorB) : Step68 := by
  intro G _ T T₁ hy m hm hq hT hnat
  have : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hS : Sec3Global T := Sec3Global.of_inputs h214 hInv hP.wc
  have hI : Sec3IsoGlobal T := Sec3IsoGlobal.of_input hIso hy.nonab hS
  have hc : Sec6Ctx T T₁ 2 m := ⟨hy, hS, hI, hq, hT, Or.inr (Or.inl hnat)⟩
  refine hC G T T₁ m hy hm hq hT hnat (hc.classD_mul_of_comm h63 rfl) ?_ hc.center_eq
    hc.comm_mem_normIn_sup ?_
  · intro d hd hd1
    exact hc.closure_classD_comm h57 h1 h63 rfl hnat hd hd1
  · intro N hNH hNn hp
    exact Sec6Ctx.normal_two_subgroup_le hnat N hNH hNn hp

end CFSG.CGT.Timmesfeld75
