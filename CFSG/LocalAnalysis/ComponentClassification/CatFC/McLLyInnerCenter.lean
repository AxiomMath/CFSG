module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.HNCenter
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSUFi22

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_alternatingGroup_eight_mcl : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

theorem exists_component_centralizer_of_conj_inner {S : Type} [Group S] (u : S)
    {D : Subgroup ↥(fixedSubgroup (MulAut.conj u))} (hD : IsComponent D) :
    ∃ B : Subgroup ↥(centralizer ({u} : Set S)), IsComponent B ∧
      Nat.card (center B) = Nat.card (center D) := by
  let φ := MulEquiv.subgroupCongr (SeitzReduction.F4Pilot.fixedSubgroup_conj u)
  exact ⟨D.map φ.toMonoidHom, ComponentClassification.CatLeaf.isComponent_map_mulEquiv φ hD,
    (Nat.card_congr (Subgroup.centerCongr
      (D.equivMapOfInjective φ.toMonoidHom φ.injective)).toEquiv).symm⟩

section McLCentre


theorem card_mcl_involution_centralizer {S : Type} [Group S]
    (e : S ≃* NativeSporadic.Carrier .McL) {u : S} (hu : orderOf u = 2) :
    Nat.card (centralizer ({u} : Set S)) = 40320 := by
  obtain ⟨-, hcen, ⟨q⟩⟩ :=
    Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate (T := S)
      ⟨e⟩ hu
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (centralizer ({u} : Set S)))
  rw [hcen, Nat.card_congr q.toEquiv, card_alternatingGroup_eight_mcl, Nat.card_zpowers,
    Subgroup.orderOf_mk, hu] at h
  omega

theorem mcl_inner_component_center {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .McL) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hin : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) : Nat.card (center ↥D) = 2 := by
  obtain ⟨u, rfl⟩ := hin
  have hu : orderOf u = 2 := SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  obtain ⟨B, hB, hZ⟩ := exists_component_centralizer_of_conj_inner u hD
  rw [← hZ]
  have hC := card_mcl_involution_centralizer e hu
  have hperf :=
    (Sporadic.Recognition.McLCentralizer.mcl_involution_centralizer_alt8_of_certificate (T := S)
      ⟨e⟩ hu).1
  obtain ⟨θ⟩ := ComponentClassification.RestrictedStd.Spor.mcl_inner_comps e u hu B hB
  have hBq : Nat.card (B ⧸ center B) = 20160 := by
    rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
  have hBc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center B)
  rw [hBq] at hBc
  have hpos : 0 < Nat.card (center B) := Nat.card_pos
  have := hperf
  have htop : B = ⊤ := eq_top_of_perfect_of_card_le_two_mul (by omega)
  subst htop
  rw [Subgroup.card_top, hC] at hBc
  omega

end McLCentre

section LyCentre


theorem ly_inner_component_center {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Ly) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hin : σ ∈ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) : Nat.card (center ↥D) = 2 := by
  obtain ⟨u, rfl⟩ := hin
  have hu : orderOf u = 2 := SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  obtain ⟨B, hB, hZ⟩ := exists_component_centralizer_of_conj_inner u hD
  rw [← hZ]
  obtain ⟨hq, hcen, -⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ u hu
  have hB' : B = ⊤ := SeitzReduction.UnitaryPilot.component_eq_top_of_central_kernel
    (QuotientGroup.mk' (center ↥(centralizer ({u} : Set S)))) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hq.2.1 hq.1.commutator_eq_top hB
  subst hB'
  rw [Nat.card_congr (Subgroup.centerCongr Subgroup.topEquiv).toEquiv]
  exact hcen

end LyCentre

end CFSG.ComponentClassification.CatFC
