module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7U4AntiMain
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecAssembly
public import Certificates.Certificate43
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddAssembly
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieu
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7U4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks

theorem unitaryFourExclusion : Sp4Rec.UnitaryFourExclusion := by
  intro H _ _ c p f hp hp2 hG
  classical
  have hGn : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨φ₀⟩⟩ := hG
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (φ₀ ⟨c.b, c.b_mem_G⟩)
  have hpc := c.pairConfig φ₀
  rw [← hg] at hpc
  obtain ⟨l, Q, hN, hl4, hQu, hgQ⟩ := exists_frame_of_pairConfig h hp2 hpc
  have hl : h.bar l * l = 1 := by rw [mul_comm]; exact hN
  have hl0 : l ≠ 0 := ne_zero_of_norm h hl
  set φ : ↥(generalizedFitting H) ≃* StatedProj (StatedSU 4 (p ^ f) K) :=
    φ₀.trans (uconj h Q hQu) with hφ
  set g₀ := conjSU h Q hQu g with hg₀def
  have hg₀ : ((g₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = X1 l := by
    rw [hg₀def, coe_conjSU, Matrix.mul_assoc, hgQ, ← Matrix.mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hφb : φ ⟨c.b, c.b_mem_G⟩ = QuotientGroup.mk g₀ := by
    rw [hφ, MulEquiv.trans_apply, ← hg, uconj_mk]
  have hpc₀ := c.pairConfig φ
  rw [hφb] at hpc₀
  have hfac := pairConfig_factorsU h hp2 hl0 hg₀ hpc₀
  have hKcard : Nat.card c.K ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by
    have h1 : Nat.card ((c.K.subgroupOf (generalizedFitting H)).map φ.toMonoidHom) =
        Nat.card c.K := by
      rw [Subgroup.card_map_of_injective φ.injective]
      exact Nat.card_congr (subgroupOfEquivOfLe c.K_le_G).toEquiv
    rw [← h1]
    exact card_factorU_le h (hfac.elim (fun h' => Or.inl h'.1) (fun h' => Or.inr h'.1))
  have hsimple := c.simple
  have : IsSimpleGroup (StatedProj (StatedSU 4 (p ^ f) K)) := φ.symm.isSimpleGroup
  have hnab : ∃ x y : StatedProj (StatedSU 4 (p ^ f) K), x * y ≠ y * x := by
    obtain ⟨u, v, huv⟩ := c.exists_ne_commute_G
    refine ⟨φ u, φ v, fun e => huv (φ.injective ?_)⟩
    rw [map_mul, map_mul, e]
  have hZ := OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  let psi : ↥(generalizedFitting H) ≃* unitaryPSU h 4 :=
    φ.trans (unitaryPSUEquiv h (by norm_num)).symm
  have : Finite (unitaryPSU h 4) := Finite.of_equiv _ psi.toEquiv
  have hq := c.isQuasisimple_J_of_fixed psi fun α hα2 hα1 L hL =>
    CatalogueBUnitaryB.odd_unitary_involution_fixed_p_components h hp2 (n := 4) (by norm_num) α
      (orderOf_eq_prime hα2 hα1) 2 Nat.prime_two L hL
  obtain ⟨ρ, hinj, hρW, -, hρg⟩ := OutcomeLocal.socle_extension c.centralizer_eq_bot φ hZ
  have hα : ∀ y, ρ c.a (ρ c.a y) = y := by
    intro y
    have ha2 : c.a * c.a = 1 := by rw [← pow_two, ← c.orderOf_a, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, ha2, map_one, MulAut.one_apply]
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := exists_lift h hp2 (ρ c.a) hα
  rcases hcase with ⟨hψA, c₀, hAA⟩ | ⟨hψA, z, hAA⟩
  · exact false_of_inner h c hp2 φ hinj hρW hZ hKcard hq hAu hψ hψA hAA
  · exact false_of_anti h c φ hinj hρW hρg hl hl4 hg₀ hφb hfac hAu hψ hψA hAA

end Catalog7U4

end CFSG.ComponentClassification.GSThmB
