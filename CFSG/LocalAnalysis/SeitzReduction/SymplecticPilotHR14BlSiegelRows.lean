module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegelMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegelKinds
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordFixed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlCoordTorusMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPNonembed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OPLagrangian
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlParamMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_map_conj)

theorem exists_le_spATorus_commutator_ne_two {κ : Sp2mKind} (hcen : SpOmegaSiegelCentralInput κ)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hn : 4 ≤ n) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp n K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hroot : ∀ k : Fin n, RootKindSp e t f k κ) (hglob : SpOmegaRowGlobal e t f κ) {j : ℕ}
    (hj : 2 * j = n) :
    ∃ Z : Subgroup (StatedSp n K), Z ≤ spATorus K n j ∧
      ∀ h ∈ centralizer (modelToG e Z : Set G), orderOf (t * h * t⁻¹ * h⁻¹) ≠ 2 := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hcen' := hcen G L hset n f K hn ⟨j, by omega⟩ hKc hf e t ht hKt hroot hglob
  refine ⟨(siegelTorus K n).map (MulAut.conj (oddSwapSp K n)).toMonoidHom,
    map_conj_oddSwapSp_siegelTorus_le j, fun h hh => ?_⟩
  set l : G := ((e.symm (oddSwapSp K n) : L) : G) with hl
  have hlL : l ∈ L := (e.symm (oddSwapSp K n)).2
  have hlt : l * t = t * l := mem_centralizer_iff.1 htC l hlL
  rw [modelToG_map_conj] at hh
  have hh' : l⁻¹ * h * l ∈ centralizer (modelToG e (siegelTorus K n) : Set G) := by
    rw [mem_centralizer_iff]
    intro τ hτ
    have h1 : (l * τ * l⁻¹) * h = h * (l * τ * l⁻¹) :=
      mem_centralizer_iff.1 hh (l * τ * l⁻¹) ⟨τ, hτ, rfl⟩
    calc τ * (l⁻¹ * h * l) = l⁻¹ * ((l * τ * l⁻¹) * h) * l := by group
      _ = l⁻¹ * (h * (l * τ * l⁻¹)) * l := by rw [h1]
      _ = l⁻¹ * h * l * τ := by group
  intro h2
  apply hcen' _ hh'
  have htl : t = l⁻¹ * t * l := by rw [mul_assoc, ← hlt, inv_mul_cancel_left]
  have h3 : t * (l⁻¹ * h * l) * t⁻¹ * (l⁻¹ * h * l)⁻¹ = l⁻¹ * (t * h * t⁻¹ * h⁻¹) * l := by
    conv_lhs => rw [htl]
    group
  have h4 := MulEquiv.orderOf_eq (MulAut.conj l⁻¹) (t * h * t⁻¹ * h⁻¹)
  simp only [MulAut.conj_apply, inv_inv] at h4
  rw [h3, h4, h2]

theorem spOmegaBClassExclusionCoord_of_central {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (hperf : SpACentralizerPerfectInput)
    (htoral : SpAToralInput) (h2part : SpACentralizerTwoPartInput)
    (hsh : SpOmegaBShapeInputCoord κ) (htor : SpOmegaBTorusInput κ)
    (hcen : SpOmegaSiegelCentralInput κ) : SpOmegaBClassExclusionCoord κ := by
  intro G _ _ L hset n f K _ _ _ hn hKc hf e t ht hKt hroot hglob htN K' _ _ Q hK' hQ hT hE hImg ε
    hθt j hj g hg hB
  obtain ⟨hZ, hodd⟩ := spGlobal_inf_centralizer_eq_bot_and_odd (by omega) hKc hf e ht hKt hκ hglob
  refine false_of_spOmegaBType_central hset hn hKc hf e ht hKt htN hZ hodd hperf htoral h2part
    (SpOmegaModelBType ε) (fun g' hg' j' hj' hB' => ?_) (fun y hy => ?_) (fun j' hj' hj'n => ?_)
    j hj g hg hB
  · exact hsh G L hset n f K hn hKc hf e t ht hKt hroot hglob htN K' Q hK' hQ hT hE hImg ε hθt j'
      hj' g' hg' hB'
  · exact spOmegaBCosetInputCoord_holds κ G L hset n f K hn hKc hf e t ht hKt hroot hglob htN K' Q
      hK' hQ hT hE hImg ε hθt y hy
  · rcases lt_or_eq_of_le hj'n with h | h
    · exact Or.inl (htor G L hset n f K hn hKc hf e t ht hKt hroot hglob j' hj' h)
    · exact Or.inr (exists_le_spATorus_commutator_ne_two hcen hset hn hKc hf e ht hKt hroot hglob h)

section Rows

theorem spOmegaBClassExclusionCoord_omegaPlus_of_central
    (hcen : SpOmegaSiegelCentralInput .omegaPlus) : SpOmegaBClassExclusionCoord .omegaPlus :=
  spOmegaBClassExclusionCoord_of_central (Or.inl rfl) spACentralizerPerfectInput_holds
    spAToralInput_holds spACentralizerTwoPartInput_holds
    (spOmegaBShapeInputCoord_of_param omegaBSpParamInput_holds .omegaPlus)
    spOmegaBTorusInput_omegaPlus hcen

theorem spOmegaBClassExclusionCoord_omegaMinus_of_central
    (hcen : SpOmegaSiegelCentralInput .omegaMinus) : SpOmegaBClassExclusionCoord .omegaMinus :=
  spOmegaBClassExclusionCoord_of_central (Or.inr rfl) spACentralizerPerfectInput_holds
    spAToralInput_holds spACentralizerTwoPartInput_holds
    (spOmegaBShapeInputCoord_of_param omegaBSpParamInput_holds .omegaMinus)
    spOmegaBTorusInput_omegaMinus hcen

theorem spOmegaRowUniqueInput_omegaMinus_of_central
    (hcen : SpOmegaSiegelCentralInput .omegaMinus) : SpOmegaRowUniqueInput .omegaMinus :=
  spOmegaRowUniqueInput_omegaMinus_of_coord spOmegaLagrangianATwoInput_omegaMinus
    (spOmegaBClassExclusionCoord_omegaMinus_of_central hcen)

theorem spOmegaRowUniqueInput_omegaPlus_of_central (hdata : OmegaMinusNonembeddingDataInput)
    (hmodel : OmegaLagrangianATwoModelInput) (hcen : SpOmegaSiegelCentralInput .omegaPlus) :
    SpOmegaRowUniqueInput .omegaPlus :=
  spOmegaRowUniqueInput_omegaPlus_of_coord (omegaMinusSpNonembeddingInput_of_data hdata)
    (spOmegaLagrangianATwoInput_omegaPlus_of_model hmodel)
    (spOmegaBClassExclusionCoord_omegaPlus_of_central hcen)

end Rows

end CFSG.SeitzReduction.SymplecticPilot
