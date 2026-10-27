module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10
public import CFSG.GH74.GLS.C3.Layer1.Th2BalA7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.GH74.GLS.Th2.Bal CFSG.GH74.GLS.IVK

theorem center_eq_bot_of_conj_injective {L : Type*} [Group L]
    (hinj : Function.Injective (MulAut.conj : L →* MulAut L)) : Subgroup.center L = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply hinj
  ext g
  have := Subgroup.mem_center_iff.mp hx g
  simp only [MulAut.conj_apply, map_one, MulAut.one_apply]
  rw [mul_inv_eq_iff_eq_mul]
  exact this.symm

theorem b_ivk_10_5 :
    B_ivk_10_5 := by
  intro L _ _ _ hmodel
  rcases hmodel with ⟨p, f, hp, hf, hodd, hLie⟩ | ⟨⟨φ⟩⟩
  · obtain ⟨F, _, _, e0, hF, hcard⟩ := exists_l2Field_of_lieModel hodd hLie
    have hc : Subgroup.center L = ⊥ := center_eq_bot_of_conj_injective (conj_injective_of_L2 e0)
    let eKL : L ⧸ Subgroup.center L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    refine ⟨isLocallyKBalanced_three_of_l2 hF (eKL.trans e0), fun hnot => Or.inr ?_⟩
    by_cases hfm : IsFM9 (p ^ f)
    · exact absurd (isLocallyKBalanced_two_of_fm9 hF (hcard ▸ hfm) (eKL.trans e0)) hnot
    · exact ⟨p, f, hp, hf, ⟨hodd, hfm⟩, hLie⟩
  · have hc : Subgroup.center L = ⊥ := center_eq_bot_of_conj_injective (a7Theta_conj_injective φ)
    let eKL : L ⧸ Subgroup.center L ≃* L :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact ⟨isLocallyKBalanced_three_of_a7 (eKL.trans φ), fun _ => Or.inl ⟨φ⟩⟩

end CFSG.GH74.GLS
