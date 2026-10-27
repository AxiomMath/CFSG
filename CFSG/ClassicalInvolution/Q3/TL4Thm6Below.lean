module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Desc
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.ClassicalInvolution.Q3.TA3SmallDescent
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem thm6RBelow_three_of_simple {n : ℕ} (h : Thm6SimpleLe n) : Thm6RBelow 3 (n + 1) := by
  intro Y _ _ hY R S t hd hcR hE2 hQ he
  have hc : TightCls Y R S t := tightClsR_three_iff.mp hcR
  have hNc := TA3.fstarCenter_le_center hd hc hE2
  have hN2 := TA3.isPGroup_fstarCenter hc
  have htN := TA3.not_mem_fstarCenter hc hE2
  by_cases htw : ∃ c ∈ TA3.fstarCenter Y, c ≠ 1 ∧ ∃ y : Y, y * t * y⁻¹ = t * c
  · obtain ⟨c, hcN, hc1, y, hy⟩ := htw
    exact absurd he (hd.not_edgeless_of_twin (hNc hcN) hc1 hy)
  have hnt : ∀ y : Y, ∀ m ∈ TA3.fstarCenter Y, y * t * y⁻¹ = t * m → m = 1 := by
    intro y m hm hy
    by_contra h1
    exact htw ⟨m, hm, h1, y, hy⟩
  have hF := TA3.genFittingFStar_quotient_fstarCenter Y hQ hNc
  have := TA3.isSimpleGroup_fstarBar Y hQ
  have : IsSimpleGroup ↥(genFittingFStar (Y ⧸ TA3.fstarCenter Y)) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hnab : ∃ a b : genFittingFStar (Y ⧸ TA3.fstarCenter Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := TA3.exists_ne_comm_fstarBar Y hQ
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h' => ?_⟩
    exact hab (by simpa using congrArg (MulEquiv.subgroupCongr hF) h')
  have hcard : Nat.card (Y ⧸ TA3.fstarCenter Y) ≤ n :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans
      (Nat.lt_succ_iff.mp hY)
  rcases h (Y ⧸ TA3.fstarCenter Y) hcard hnab _ _ _ (TwistQ.datum hd hN2 htN hnt)
      (TwistQ.cls hd hNc hN2 htN hc) (fun h' => hE2 (TwistQ.inO2_of hN2 h'))
      (Thm6.edgeless_map hd hNc hN2 htN hnt he) with hg | hx
  · exact Or.inl (TwistQ.good_of hd hNc hN2 htN hnt hg)
  · exact Or.inr (Thm6.thm6Exit_of_fstarQuot hQ hNc hx)

end CFSG.ClassicalInvolution.Q3.TL4
