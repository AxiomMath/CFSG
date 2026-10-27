module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieQuasi
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefChar
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance

theorem lieUnipotentCore_of_defCharInnerCoreFree
    (h : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree) :
    LieUnipotentCore := by
  intro S _ _ hs hnc idx he p hp hp2 hpc x hx1 hxp
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hmem : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro k
      have := congrArg (fun f : MulAut S => f k) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc k * g = (g * k * g⁻¹) * g := by rw [this]
        _ = g * k := by group
    rw [b3Lie_center_eq_bot hnc] at hmem
    exact hmem
  set ψ : S →* MulAut S := MulAut.conj with hψ
  have hy1 : ψ x ≠ 1 := fun h1 => hx1 (hinj (by rw [h1, map_one]))
  have hyp : orderOf (ψ x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hy1
  have hmain := h S hs hnc idx he p hp hp2 hpc.symm (ψ x) ⟨x, rfl⟩ hyp (innerAut S) le_rfl
  have hC : innerAut S ⊓ Subgroup.centralizer ({ψ x} : Set (MulAut S)) =
      (Subgroup.centralizer ({x} : Set S)).map ψ := by
    ext z
    constructor
    · rintro ⟨⟨c, rfl⟩, hz⟩
      have hz' := Subgroup.mem_centralizer_singleton_iff.1 hz
      refine ⟨c, ?_, rfl⟩
      show c ∈ Subgroup.centralizer ({x} : Set S)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hz'
    · rintro ⟨c, hc, rfl⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
      refine ⟨⟨c, rfl⟩, ?_⟩
      show ψ c ∈ Subgroup.centralizer ({ψ x} : Set (MulAut S))
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
  rw [hC, ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p ψ hinj]
    at hmain
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 hmain

theorem bpSimpleLie_of_defChar
    (hD : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : BpSimpleLie :=
  bpSimpleLie_of_unipotentCore (lieUnipotentCore_of_defCharInnerCoreFree hD) hss hout

theorem b3SimpleLie_of_defChar
    (hD : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : B3SimpleLie :=
  b3SimpleLie_of_unipotentCore (lieUnipotentCore_of_defCharInnerCoreFree hD) hss hout

theorem input14_5Lie_of_defChar
    (hD : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hss : LieSemisimpleCent) (hout : LieDefCharOuter) : Input14_5Lie :=
  input14_5Lie_of_unipotentCore (lieUnipotentCore_of_defCharInnerCoreFree hD) hss hout

end CFSG.HardMathSupport.Solomon.Coordinator
