module

public import CFSG.GH74.Generic.S3.V1InnerNeg
public import CFSG.GH74.KGroups.L3EpsUniInv
public import CFSG.GH74.KGroups.L3EpsUniGraph

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvData GraphData)
open CFSG.GH74.KGroups.L3Eps.Uni (dU IsCover levS exists_cover_of_equiv theta_dU_sq theta_dU_ne_one invData_of_cover
  graphData_of_cover)

theorem libData_uni {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) : LibData .PSU p f := by
  intro K _ _ hX
  obtain ⟨hadm, F, _, _, hF, ⟨e₀⟩⟩ := hX
  have hf : 1 ≤ f := hadm.2.1
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hS : SingleInv K := SingleInv.of_mulEquiv e₀.symm (singleInv_psu hU hp2)
  refine ⟨fun x hx2 hx1 => ?_, fun c hc2 hout => ?_⟩
  · obtain ⟨θ₀, hθ₀⟩ := exists_cover_of_equiv hU e₀
    obtain ⟨g, hg⟩ := hS (θ₀ (dU hq)) x (theta_dU_sq hq θ₀) (theta_dU_ne_one hU hq hθ₀) hx2 hx1
    have hθ : IsCover hU ((MulAut.conj g).toMonoidHom.comp θ₀) := hθ₀.comp_equiv (MulAut.conj g)
    refine ⟨levS hq ((MulAut.conj g).toMonoidHom.comp θ₀), ?_⟩
    have hinv := invData_of_cover hU hp2 h5 hq hθ
    have hθt : ((MulAut.conj g).toMonoidHom.comp θ₀) (dU hq) = x := by
      simpa [MulAut.conj_apply] using hg
    rwa [hθt] at hinv
  · obtain ⟨θ, hθ⟩ := exists_cover_of_equiv hU e₀
    exact graphData_of_cover hU hp2 h5 hq hθ hc2 hout

theorem b_S3_v1_inner_neg_uni : B_S3_v1_inner_neg_uni := by
  intro G _ _ hG p f v w Iv Iw Ivw P hconf _ v₁ hv₁R hv₁2 hv₁1 hv₁v _
  exact v1_inner_of_lib (libData_uni hconf.prime.1 hconf.prime.2.1 hconf.prime.2.2) hconf hv₁R hv₁2 hv₁1 hv₁v

end CFSG.GH74.Generic.S3
