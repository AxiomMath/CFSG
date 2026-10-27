module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Comp
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HQuot
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HSp6
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HF4Model
import CFSG.LocalAnalysis.GLTheoremA.CatB.I2610HRestrict
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144PSimple
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Trans
import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp6
import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup iInf_fixSubgroup_closure)


theorem i2610FactF4_holds : I2610FactF4 := by
  intro Γ _ _ K W hK hcat hWN hW hW27 hWK J hJ hJc
  obtain ⟨F, _, _, hF, ⟨eS⟩⟩ := exists_adjointGroup_of_catalogIs_isF4two hcat
  obtain ⟨A, hA, h9, I, hI, ⟨e₁⟩⟩ := exists_quot_component hK hWN hW hW27 hWK eS hJ
  have hIc : catalogIs (PSimple 3 I) isL2prime := I2018.catalogIs_congr' e₁ hJc
  obtain ⟨a, haA, b, hbA, ha1, -, hgen⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LocalTwo.exists_gen_pair Nat.prime_three hA h9
  rw [← hgen, iInf_fixSubgroup_closure, iInf_pair] at hI
  obtain ⟨x, rfl⟩ := exists_eq_conj_of_pow_three_F4 hF (hA.2 _ haA)
  have hx3 : x ^ 3 = 1 := by
    have h1 : MulAut.conj (x ^ 3) = 1 := by
      rw [map_pow]
      exact hA.2 _ haA
    have h2 := LevelLieSp6.mem_center_of_conj_eq_one h1
    rwa [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at h2
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact ha1 (map_one _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hperf : ⁅I, I⁆ = I :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_perfect hI
  obtain ⟨L, hLc, hIL, hT, hnorm⟩ := exists_component_of_perfect_le hF hxo
    (hI.1.trans inf_le_left) hperf (glaPComponent_ne_bot' hI)
  have hLb : L.map b.toMonoidHom = L := hnorm b (isElemAbelian_commute hA hbA haA)
  have hI' := glaPComponent_subgroupOf_restrictAut Nat.prime_three hLc.1 hLb hI hIL
  have hβ : (CFSG.LocalAnalysis.ComponentInitial.restrictAut b L hLb) ^ 3 = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    have hy := DFunLike.congr_fun (hA.2 _ hbA) ↑y
    simpa only [pow_three, MulAut.mul_apply, MulAut.one_apply,
      CFSG.LocalAnalysis.ComponentInitial.coe_restrictAut] using hy
  obtain ⟨F', _, _, hF', ⟨eL⟩⟩ := hT
  have hno := not_catalogIs_isL2prime_of_quot_sp6 hLc.2.2 hF' eL hβ hI'
  obtain ⟨e₂⟩ := K144.pSimple_subgroupOf_equiv (p := 3) hIL
  exact hno (I2018.catalogIs_congr' e₂.symm hIc)

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610
