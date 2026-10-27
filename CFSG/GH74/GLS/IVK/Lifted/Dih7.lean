module

public import CFSG.GH74.GLS.IVK.Lifted.PGLQuot
public import CFSG.GH74.GLS.IVK.Lifted.CentSylow
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Closed

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ivk_1_2d_lifted_of_II4 (h44 : II4_44) (hII : II4_4_4_center) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.IVK_1_2d_lifted := by
  intro G _ _ z S K₁ K₂ q h hqodd K hK hSL w hwS hw2 hwN hwin hwF
  have hKc : K = K₁ ∨ K = K₂ := by simpa using hK
  have hOK := std4_hatOK h44 h hK
  have hM := m4_of_std hII h
  have hzK : z ∈ K := hM.z_mem_comp hKc
  have hKC := h.comp_isPCompIn hKc
  obtain ⟨F, hFf, hFin, hFq, ⟨e0⟩⟩ := hSL
  have hFodd : Odd (Nat.card F) := hFq ▸ hqodd
  have h3 : 3 < Nat.card F := three_lt_of_sl2_model hOK.sl2 hFodd e0
  let e : Hat K ≃* SpecialLinearGroup (Fin 2) F :=
    e0.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, sq] at this
  have hφ2 : phi K w hwN * phi K w hwN = 1 := phi_mul_self K hwN hww
  have hwin' : ¬ phi K w hwN ∈ innOf (Hat K) := fun hh => hwin ((phi_mem_inn_iff K hwN).1 hh)
  have hα2 : MulAut.congr e (phi K w hwN) * MulAut.congr e (phi K w hwN) = 1 := by
    rw [← map_mul, hφ2, map_one]
  have hσ : (gammaOf hFodd h3 (MulAut.congr e (phi K w hwN))).right = 1 := by
    by_contra hσ
    apply hwF
    refine ⟨hwN, ?_⟩
    exact ⟨hOK.quasi, hOK.kgrp, hOK.rank, exists_pow_two_orderOf hφ2,
      fixedCond_of_congr e (fixedCond_of_field_part hFodd h3 _ hα2 hσ)⟩
  exact ⟨F, hFf, hFin, hFq,
    exists_pglQuot hFodd h3 e hzK hKC.1 h.orderOf_z hOK.sl2.2 hwN hww hwin' hσ⟩

end CFSG.GH74.GLS.IVK.Lifted
