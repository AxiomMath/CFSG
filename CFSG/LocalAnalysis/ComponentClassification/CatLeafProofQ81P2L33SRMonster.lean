module

public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Monster.Generated CFSG.Monster.Existence
open CFSG.Monster.Existence.InvolutionOddCore CFSG.Monster.B.TwoA
open CFSG.ComponentClassification.BMCase

theorem not_isPGroup_of_simple_nonabelian {G : Type*} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) : ¬ IsPGroup 2 G := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial G := hs.toNontrivial
  have hc := hP.center_nontrivial
  rw [CatLeaf.center_eq_bot_of_simple hna] at hc
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl

theorem not_isPGroup_cent_tGmat :
    ¬ IsPGroup 2 ↥(cent tGmat) := by
  intro hP
  have hC : IsPGroup 2 Cfull := hP.of_equiv
    (((cent tGmat).equivMapOfInjective Gmat.subtype Gmat.subtype_injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.Monster.Existence.InvolutionOddCore.map_subtype_centralizer tGmat)))
  have hD : IsPGroup 2 Dfull := hC.to_quotient ZstarF
  obtain ⟨-, -, ⟨A, -, -, -, -, hAs, hAna, -⟩, -⟩ := full_short_centralizer_almost_simple.{0}
  exact not_isPGroup_of_simple_nonabelian hAs hAna (hD.to_subgroup A)

theorem twoNilpFor_M
    : TwoNilpFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .M := by
  intro Y _ _ hY hs hna a ha hP
  exfalso
  obtain ⟨e⟩ := hY
  have hO : pPrimeCore 2 ↥(fixedPoints a) = ⊥ :=
    N36.pPrimeCore_fixedPoints_eq_bot_of_mulAut hna
      (fun i hi => N36.mulAut_oddCore_eq_bot CatalogueU.sporadicOddCoreFree_M hna e i hi) ha
  have h2 := isPGroup_of_pPrimeCore_eq_bot hO hP
  let ψ : Y ≃* Gmat := MulEquiv.ofBijective _ (catalog_fM_comp_mulEquiv_bijective e)
  obtain ⟨t, rfl⟩ := inner_of_equiv ψ gmat_automorphisms_inner_unconditional a
  have hZ : center Y = ⊥ := CatLeaf.center_eq_bot_of_simple hna
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t]
    exact ha
  rw [← Hin.centralizer_eq_fixedPoints_conj] at h2
  have h3 := h2.of_equiv (gmatCentralizerEquiv ψ t)
  have hψt : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  rcases Census.generated_group_two_involution_classes (ψ t) hψt with hx | hx
  · obtain ⟨-, -, -, -, hcard, -⟩ := isTwoBCentralizer_Gmat _ hx
    exact not_isPGroup_of_three_dvd (by rw [hcard, twoBCentralizerOrder]; norm_num) h3
  · obtain ⟨c, hc⟩ := isConj_iff.1 hx
    rw [← hc] at h3
    exact not_isPGroup_cent_tGmat (h3.of_equiv (conjCentralizerEquiv c tGmat).symm)

end CFSG.ComponentClassification.HarrisLit.L33.SR
