module

public import CFSG.GH74.GLS.IVK.Lifted.Out

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {z : G}

theorem hout49 {Kb : Subgroup (CentralizerBar z)} {Fq : Type} [Field Fq] [Finite Fq]
    (e : ↥Kb ≃* StatedSL 2 Fq) (hodd : Odd (Nat.card Fq)) (h5 : 5 ≤ Nat.card Fq) :
    ∀ α β : MulAut ↥Kb, ∃ k : ↥Kb, α * β * α⁻¹ * β⁻¹ = MulAut.conj k := by
  intro α β
  let e' : ↥Kb ≃* Matrix.SpecialLinearGroup (Fin 2) Fq :=
    e.trans (specialLinearGroupEquivStatedSL 2 Fq).symm
  obtain ⟨s, hs⟩ := CFSG.GH74.GLS.IVK.Lifted.out_abelian_sl hodd (by omega) (MulAut.congr e' α)
    (MulAut.congr e' β)
  refine ⟨e'.symm s, ?_⟩
  apply (MulAut.congr e').injective
  have hc : (MulAut.congr e') (MulAut.conj (e'.symm s)) = MulAut.conj s := by
    ext x
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [hc]
  simp only [map_mul, map_inv]
  exact hs.symm

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
