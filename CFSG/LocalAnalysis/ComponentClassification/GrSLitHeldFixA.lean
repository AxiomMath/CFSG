module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIso

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.PSL3Four.Native

theorem isL34Type_of_isPComponent_centralizer_heA0
    (L : Subgroup ↥(centralizerIn heP (heGenPerm 0))) (hL : IsPComponent 2 L) :
    IsL34Type (L ⧸ Open.fusionZStar L) := by
  have hO : pPrimeCore 2 (centralizerIn heP (heGenPerm 0)) = ⊥ := by
    rw [pPrimeCore_two_eq_oddCore]
    exact heInner0_oddCore card_heP_cent0
  let e : ↥(centralizerIn heP (heGenPerm 0)) ≃* heInnerGrp0 :=
    MulEquiv.subgroupCongr heInnerGrp0_eq.symm
  have hB := LocalCores.isComponent_map_mulEquiv e (isComponent_of_isPComponent hO hL)
  obtain ⟨⟨hDs, hDnab⟩, -, hDle, hDi⟩ := heD_facts
  have hker : Group.IsSolvable heRho0.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 heRho0.ker :=
      IsPGroup.of_card (n := 2) (by rw [card_heRho0_ker]; norm_num)
    have : Group.IsNilpotent heRho0.ker := hp.isNilpotent
    infer_instance
  let eD : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range ≃*
      genGroup 105 heDGens heDPerm :=
    subgroupOfEquivOfLe hDle
  have hs : IsSimpleGroup ((genGroup 105 heDGens heDPerm).subgroupOf heRho0.range) :=
    eD.isSimpleGroup
  have hnc : ∃ a b : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnab
    refine ⟨eD.symm a, eD.symm b, fun h => hab ?_⟩
    simpa using congrArg eD h
  obtain ⟨e₁⟩ := nonempty_quotient_center_equiv heRho0.rangeRestrict
    heRho0.rangeRestrict_surjective hker _ hDi hs hnc hB
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective e.toMonoidHom e.injective
  let e₂ : L ⧸ Open.fusionZStar L ≃* (genGroup 105 heDGens heDPerm) :=
    (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_isPComponent hO hL)).trans
      ((QuotientGroup.congr _ _ eL (map_center_eq eL)).trans (e₁.trans eD))
  exact LieType.CurtisTits.lieModel_of_mulEquiv e₂.symm
    (Or.inl ⟨by decide, statedClassicalModel_heD⟩)

end CFSG.ComponentClassification.GrSLit.HeldFix
