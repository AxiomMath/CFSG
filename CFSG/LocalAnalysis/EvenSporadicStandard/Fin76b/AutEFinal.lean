module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEApply
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFactsJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final3Base
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Model

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}

theorem autEFact_of_model (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) {X : Type*}
    [Group X] [Finite X] (φ : X ≃* L) {T Ex : Subgroup X} {tx : X} (hM : PinModel X T Ex tx)
    (hR : RootFactsClass X) (hA : AutEClass X) : AutEFact ↥E := by
  obtain ⟨ι, hι, -, hrange, hTι, hιt⟩ := h.exists_embedding hM φ
  have hEι : E = Ex.map ι := hE.eq_map_of_pinModel h hM ι hι hrange hTι hιt
  have htx2 : orderOf tx = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hM.t_sq) hM.t_ne
  have hsq : ∃ g : X, g * g = tx := by
    have hne : {x | x ∈ T ∧ x * x = tx}.Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      have := hM.roots_ge
      rw [hempty, Set.ncard_empty] at this
      omega
    obtain ⟨x, -, hx⟩ := hne
    exact ⟨x, hx⟩
  have hRf := hR tx htx2 hsq
  have hroots : {x : X | x * x = tx} = {x | x ∈ T ∧ x * x = tx} := by
    have hsub : {x | x ∈ T ∧ x * x = tx} ⊆ {x : X | x * x = tx} := fun x hx => hx.2
    exact (Set.eq_of_subset_of_ncard_le hsub (le_trans hRf.roots_le hM.roots_ge)
      (Set.toFinite _)).symm
  have hEx : rootGroup X tx = Ex := by
    rw [rootGroup, hroots, ← hM.E_eq]
  have hAx : AutEFact ↥Ex := by
    have := hA tx htx2 hsq
    rw [hEx] at this
    exact this
  exact AutEFact.of_mulEquiv
    ((Ex.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hEι.symm)) hAx

end Model

namespace J2

open CFSG.Sporadic.Schreier (j2P j2PermEquiv)

theorem autEClass_P :
    AutEClass ↥ComponentClassification.J2Cover.Models.P :=
  AutEClass.of_mulEquiv
    ((j2PermEquiv.symm.trans ComponentClassification.J2Cover.nativeEquivP).trans
      (MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP.symm))
    autEClass_j2P

theorem autEFact_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J2) :
    AutEFact ↥E := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_P
  exact autEFact_of_model h hE
    (((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
      ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm) hM rootFactsClass_P
    autEClass_P

end J2

namespace J3

open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

theorem autEFact_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J3) :
    AutEFact ↥E := by
  obtain ⟨e⟩ := hL
  obtain ⟨T, Ex, tx, hM⟩ := pinModel_j3P
  exact autEFact_of_model h hE (j3PermEquiv.symm.trans e.symm) hM rootFactsClass_j3P
    autEClass_j3P

end J3

theorem fin76bAutE :
    Fin76bAutE := by
  intro G _ _ L z t T₀ E Q x β B hconf hW y hyN hyβ hin
  have hE : AutEFact ↥E := by
    rcases hconf.sporadic with hL | hL
    · exact J2.autEFact_of_isSporadic hconf.cfg hconf.econfig hL
    · exact J3.autEFact_of_isSporadic hconf.cfg hconf.econfig hL
  have hβL : β ∈ L := hconf.B_le hconf.beta_mem
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hconf.beta_mem)
  have hβ3 : β ^ 3 = 1 := by
    rw [← hconf.beta_order]
    exact pow_orderOf_eq_one β
  have hβN : β ∈ normalizer (E : Set G) :=
    W_le_normalizer hW ⟨hβL, mem_centralizer_singleton_iff.2 hβt⟩
  have hβne : ∃ e ∈ E, β * e ≠ e * β := by
    by_contra hcon
    have hle : E ≤ centralizer ({β} : Set G) := fun e he =>
      mem_centralizer_singleton_iff.2 (Classical.not_not.1 fun hne => hcon ⟨e, he, Ne.symm hne⟩)
    have h8 := card_inf_centralizer_eq_eight hW hβL hβt hconf.beta_order
    rw [inf_of_le_left hle, hW.card_E] at h8
    omega
  exact autE_conclusion hE hβN hβ3 hβne hyN hyβ hin

end CFSG.EvenSporadicStandard.Fin76b
