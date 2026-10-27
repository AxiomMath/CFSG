module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Facts
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HQuot
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Model
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HTE6Comp
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HU62End
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HO8End
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HRestrict
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf
public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup iInf_fixSubgroup_closure)


theorem i2610FactTE6_holds : I2610FactTE6 := by
  intro Γ _ _ K W hK hcat hWN hW hW27 hWK J hJ hJc
  obtain ⟨F, _, _, σ, hF, hσ, ⟨eS⟩⟩ := exists_twistedE6RootGroup_of_catalogIs_isTE6two hcat
  haveI : Finite (CFSG.LieType.Chevalley.twistedE6RootGroup F σ) := Subtype.finite
  obtain ⟨A, hA, h9, I, hI, ⟨e₁⟩⟩ := exists_quot_component hK hWN hW hW27 hWK eS hJ
  have hIc : catalogIs (PSimple 3 I) isL2prime := I2018.catalogIs_congr' e₁ hJc
  obtain ⟨s, hs, b, hbA, hgen⟩ := exists_conj_gen_of_elemAbelian_nine hF σ hσ hA h9
  have haA : MulAut.conj s ∈ A := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  rw [← hgen, iInf_fixSubgroup_closure, iInf_pair] at hI
  have hperf : ⁅I, I⁆ = I :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hI
  obtain ⟨L, hLs, hLq, hIL, hT, hnorm⟩ := exists_component_of_perfect_le_twE6 hF σ hσ hs
    (hI.1.trans inf_le_left) hperf (glaPComponent_ne_bot' hI)
  have hLb : L.map b.toMonoidHom = L := hnorm b (isElemAbelian_commute hA hbA haA)
  have hI' := glaPComponent_subgroupOf_restrictAut Nat.prime_three hLs hLb hI hIL
  have hβ : (CFSG.LocalAnalysis.ComponentInitial.restrictAut b L hLb) ^ 3 = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have hy := DFunLike.congr_fun (hA.2 _ hbA) ↑y
    simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply,
      CFSG.LocalAnalysis.ComponentInitial.coe_restrictAut] using hy
  obtain ⟨⟨d, hv⟩, hd, ⟨eL⟩⟩ := hT
  have hno : ¬ catalogIs (PSimple 3 (I.subgroupOf L)) isL2prime := by
    cases d with
    | twistedA r q =>
      obtain ⟨hq, rfl⟩ := hd
      exact not_catalogIs_isL2prime_of_quot_u62 hLq hq eL hβ hI'
    | D r q =>
      obtain ⟨hq, rfl⟩ := hd
      exact not_catalogIs_isL2prime_of_quot_o8plus hLq hq eL hβ hI'
    | _ => exact hd.elim
  obtain ⟨e₂⟩ := K144.pSimple_subgroupOf_equiv (p := 3) hIL
  exact hno (I2018.catalogIs_congr' e₂.symm hIc)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
