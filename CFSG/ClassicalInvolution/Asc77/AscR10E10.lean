module

public import CFSG.ClassicalInvolution.Asc77.AscR10E9
public import CFSG.ClassicalInvolution.Asc77.AscR10E2
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2IsogenyE7
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi



open CFSG.ClassicalInvolution.Asc77.T3CII (GenSq eq_of_map_eq_of_genSq
  commute_of_map_commute_of_genSq)

section Pair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits

variable {p e : ℕ} [Fact p.Prime]

theorem eq_of_mem_longestFundamental_E7_three (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .E7 0 p e)
    {R R' : Subgroup (E7sc p e)} (hR : R ∈ longestFundamental (e7Datum (GaloisField p e)))
    (hR' : R' ∈ longestFundamental (e7Datum (GaloisField p e)))
    {c c' : E7sc p e} (hc : c ∈ R) (hc' : c' ∈ R') (ho : orderOf c = 2) (ho' : orderOf c' = 2)
    (h : ((e7Isogeny (GaloisField p e) c : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = e7Isogeny (GaloisField p e) c') : R = R' := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .E7 (e7Datum (GaloisField p e)) :=
    fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e7Datum (GaloisField p e)) thetaE7 ∈
      Generic.fundamentalSubgroups .E7 (e7Datum (GaloisField p e)) :=
    ⟨1, thetaE7, Or.inl (isLongestRoot_e7Datum hadm isRoot_thetaE7),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨g, hg⟩ := hsingle _ hθmem R (longestFundamental_subset .E7 _ hR)
  obtain ⟨g', hg'⟩ := hsingle _ hθmem R' (longestFundamental_subset .E7 _ hR')
  have hd : g⁻¹ * c * g ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 :=
    Generic.mem_conjSub_iff.1 (hg ▸ hc)
  have hd' : g'⁻¹ * c' * g' ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 :=
    Generic.mem_conjSub_iff.1 (hg' ▸ hc')
  have ord : ∀ (y x : E7sc p e), orderOf x = 2 → orderOf (y⁻¹ * x * y) = 2 := fun y x hx => by
    rw [← hx]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective x
    simpa [MulAut.conj_apply] using this
  have z1 := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hd (ord g c ho)
  have z1' := e7Isogeny_involution hp2 hadm isRoot_thetaE7 hd' (ord g' c' ho')
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at z1 z1'
  set gb := e7Isogeny (GaloisField p e) g with hgb
  set gb' := e7Isogeny (GaloisField p e) g' with hgb'
  have hcg : (e7Isogeny (GaloisField p e) c : ModGL .E7 (GaloisField p e)) =
      (gb : ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 *
        (gb : ModGL .E7 (GaloisField p e))⁻¹ := by
    rw [← z1]
    group
  have hcg' : (e7Isogeny (GaloisField p e) c' : ModGL .E7 (GaloisField p e)) =
      (gb' : ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 *
        (gb' : ModGL .E7 (GaloisField p e))⁻¹ := by
    rw [← z1']
    group
  have hu : (((gb'⁻¹ * gb : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e))) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        (((gb'⁻¹ * gb : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h2 := hcg.symm.trans (h.trans hcg')
    calc (↑gb')⁻¹ * ↑gb * signDiagE7 (GaloisField p e) thetaE7 =
        (↑gb')⁻¹ * (↑gb * signDiagE7 (GaloisField p e) thetaE7 * (↑gb)⁻¹) * ↑gb := by group
      _ = (↑gb')⁻¹ * (↑gb' * signDiagE7 (GaloisField p e) thetaE7 * (↑gb')⁻¹) * ↑gb := by rw [h2]
      _ = signDiagE7 (GaloisField p e) thetaE7 * ((↑gb')⁻¹ * ↑gb) := by group
  have hconj := map_conj_stdRankOne_theta_E7 hK hu
  have hRε : R.map (e7Isogeny (GaloisField p e)) =
      (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7).map (MulAut.conj gb).toMonoidHom := by
    rw [hg]
    show ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map
      (MulAut.conj g).toMonoidHom).map (e7Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  have hRε' : R'.map (e7Isogeny (GaloisField p e)) =
      (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7).map (MulAut.conj gb').toMonoidHom := by
    rw [hg']
    show ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map
      (MulAut.conj g').toMonoidHom).map (e7Isogeny (GaloisField p e)) = _
    rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  have hmap : R.map (e7Isogeny (GaloisField p e)) = R'.map (e7Isogeny (GaloisField p e)) := by
    rw [hRε, hRε']
    have h3 : (MulAut.conj gb).toMonoidHom =
        (MulAut.conj gb').toMonoidHom.comp (MulAut.conj (gb'⁻¹ * gb)).toMonoidHom := by
      ext x
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [h3, ← Subgroup.map_map, hconj]
  exact eq_of_map_eq_of_genSq (e7Isogeny (GaloisField p e)) ker_e7Isogeny_le_center
    e7Isogeny_ker_sq
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hR)
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hR') hmap

theorem conj_stdRankOne_theta_E7_three (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .E7 0 p e) {u : E7sc p e}
    (hu : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e))) :
    (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e7Datum (GaloisField p e)) thetaE7 := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hθ := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) isRoot_thetaE7
  refine eq_of_map_eq_of_genSq (e7Isogeny (GaloisField p e)) ker_e7Isogeny_le_center
    e7Isogeny_ker_sq
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide)
      (map_conj_mem_longestFundamental u hθ))
    (genSq_of_mem_longestFundamental3 (t := .E7) hq3 trivial hadm (by decide) (by decide) hθ) ?_
  rw [map_conj_map_e7, map_stdRankOne_e7_root isRoot_thetaE7]
  exact map_conj_stdRankOne_theta_E7 hK hu

end Pair

section Split

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {p e : ℕ} [Fact p.Prime]

theorem linearBlockStandardPair_theta_deltaE7_three (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .E7 0 p e) {c₁ : E7sc p e}
    (hc₁ : c₁ ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7) (ho₁ : orderOf c₁ = 2) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7)
      (stdRankOne (e7Datum (GaloisField p e)) deltaE7) := by
  have hδ₀ := isPartnerE7_deltaE7
  have hθlong : ModelFacts.IsLongestRoot (e7Datum (GaloisField p e)) thetaE7 :=
    isLongestRoot_e7Datum hadm isRoot_thetaE7
  obtain ⟨δ', hδ'l, hδ'p, W, hW⟩ := exists_standardPair_partner_E7 p e hadm hθlong
  have hδ'root : IsRoot .E7 δ' :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p e)).1
      ((isLongestRoot_iff _ _).1 hδ'l).1
  have hδ'PF : IsPartnerE7 δ' := isPartnerE7_of_isPartner hδ'root hδ'p
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup (E7sc p e),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W'
        (stdRankOne (e7Datum (GaloisField p e)) thetaE7)
        (stdRankOne (e7Datum (GaloisField p e)) δ') := ⟨W, hW⟩
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerE7 (F := GaloisField p e) hδ'PF
  have hnG : n ∈ adjointGroup .E7 (GaloisField p e) := parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JE7 hn)
  obtain ⟨ν, hν⟩ := e7Isogeny_surjective (GaloisField p e)
    (⟨n⁻¹, inv_mem hnG⟩ : ↥(adjointGroup .E7 (GaloisField p e)))
  have hν' : ((e7Isogeny (GaloisField p e) ν : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = n⁻¹ := congrArg Subtype.val hν
  have hνθ : ((e7Isogeny (GaloisField p e) ν : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) ν : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)) := by
    rw [hν']
    exact (rootDiagUnit_thetaDiag_comm_levi_E7 (-1 : (GaloisField p e)ˣ) (inv_mem hn)).symm
  obtain ⟨c', hc'R, hc'o, hc'ε⟩ := exists_involution_stdRankOne_E7 hp2 hadm hc₁ ho₁ hδ'root
  obtain ⟨c₀, hc₀R, hc₀o, hc₀ε⟩ := exists_involution_stdRankOne_E7 hp2 hadm hc₁ ho₁ hδ₀.1
  have hRδ' := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) hδ'root
  have hRδ₀ := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) hδ₀.1
  have hν_R : (stdRankOne (e7Datum (GaloisField p e)) δ').map (MulAut.conj ν).toMonoidHom =
      stdRankOne (e7Datum (GaloisField p e)) deltaE7 := by
    refine eq_of_mem_longestFundamental_E7_three hp2 hq3 hadm
        (map_conj_mem_longestFundamental ν hRδ')
      hRδ₀ (c := ν * c' * ν⁻¹) (c' := c₀) ⟨c', hc'R, rfl⟩ hc₀R (a2_orderOf_conj_eq_two hc'o ν)
      hc₀o ?_
    rw [hc₀ε]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hν', hc'ε]
    have h1 : n * signDiagE7 (GaloisField p e) deltaE7 * n⁻¹ =
        signDiagE7 (GaloisField p e) δ' := hnd
    rw [← h1]
    group
  have hpair := linearBlockStandardPair_map_conj hW' ν
  rw [conj_stdRankOne_theta_E7_three hp2 hq3 hadm hνθ, hν_R] at hpair
  exact ⟨_, hpair⟩

theorem linearBlockStandardPair_of_split_E7_three (hp2 : p ≠ 2) (hq3 : p ^ e = 3)
    (hadm : StatedLieAdmissible .E7 0 p e) {c₁ : E7sc p e}
    (hc₁ : c₁ ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7) (ho₁ : orderOf c₁ = 2)
    {R₂ : Subgroup (E7sc p e)} (hR₂ : R₂ ∈ longestFundamental (e7Datum (GaloisField p e)))
    {c₂ u : E7sc p e} (hc₂ : c₂ ∈ R₂) (ho₂ : orderOf c₂ = 2)
    (hu : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)))
    (hcu : ((e7Isogeny (GaloisField p e) (u * c₂ * u⁻¹) :
        ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) =
      signDiagE7 (GaloisField p e) deltaE7) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7) R₂ := by
  have hδ₀ := isPartnerE7_deltaE7
  obtain ⟨c₀, hc₀R, hc₀o, hc₀ε⟩ := exists_involution_stdRankOne_E7 hp2 hadm hc₁ ho₁ hδ₀.1
  have hRδ₀ := stdRankOne_mem_longestFundamental_E7 hadm (p := p) (e := e) hδ₀.1
  have hR₂u : R₂.map (MulAut.conj u).toMonoidHom =
      stdRankOne (e7Datum (GaloisField p e)) deltaE7 :=
    eq_of_mem_longestFundamental_E7_three hp2 hq3 hadm (map_conj_mem_longestFundamental u hR₂) hRδ₀
      (c := u * c₂ * u⁻¹) (c' := c₀) ⟨c₂, hc₂, rfl⟩ hc₀R (a2_orderOf_conj_eq_two ho₂ u) hc₀o
      (hcu.trans hc₀ε.symm)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaE7_three hp2 hq3 hadm hc₁ ho₁
  have huinv : ((e7Isogeny (GaloisField p e) u⁻¹ : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
      signDiagE7 (GaloisField p e) thetaE7 *
        ((e7Isogeny (GaloisField p e) u⁻¹ : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e)) := by
    simp only [map_inv, Subgroup.coe_inv]
    calc ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e))⁻¹ * signDiagE7 (GaloisField p e) thetaE7 =
        (↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e))⁻¹ *
          (signDiagE7 (GaloisField p e) thetaE7 *
            (↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e))) *
          (↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e))⁻¹ := by group
      _ = (↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e))⁻¹ *
          ((↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e)) *
            signDiagE7 (GaloisField p e) thetaE7) *
          (↑(e7Isogeny (GaloisField p e) u) : ModGL .E7 (GaloisField p e))⁻¹ := by rw [hu]
      _ = _ := by group
  have hfin := linearBlockStandardPair_map_conj hW₁ u⁻¹
  rw [conj_stdRankOne_theta_E7_three hp2 hq3 hadm huinv, ← hR₂u, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

end Split

end CFSG.ClassicalInvolution.ModelFacts.Levi
