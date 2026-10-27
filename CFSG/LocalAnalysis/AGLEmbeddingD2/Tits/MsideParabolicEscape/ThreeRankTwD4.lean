module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankSL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedD4
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional

theorem ng_zero_ne_one : (ng 0 : Fin (Tag.rank .G2)) ≠ ng 1 := by decide

theorem g2_cartan_ng_zero_one : Tag.cartan .G2 (ng 0) (ng 1) = -1 := by decide

theorem g2_cartan_ng_one_zero : Tag.cartan .G2 (ng 1) (ng 0) = -3 := by decide

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ}

set_option linter.unusedSectionVars false


theorem range_le_of_sl2 {G F : Type} [Group G] [Field F]
    (φ : Matrix.SpecialLinearGroup (Fin 2) F →* G) {S : Subgroup G}
    (hu : ∀ c, φ (sl2Upper c) ∈ S) (hl : ∀ c, φ (sl2Lower c) ∈ S) : φ.range ≤ S := by
  rintro _ ⟨s, rfl⟩
  have h : s ∈ S.comap φ :=
    (Subgroup.closure_le (S.comap φ)).2 (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hu c
      · exact hl c) (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 s)
  exact h

theorem hasSL2Node_d4tw_long (hσ : ∀ c, σ (σ (σ c)) = c) :
    HasSL2Node (twistedDatum σ) (ng 0) (fixedField σ) := by
  refine ⟨slLong σ hσ, slLong_injective hσ, fun c => ?_, fun c => ?_⟩
  · show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
    rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_upper]
    exact xPar_single_two_mem_twisted hσ c.2
  · show _ ∈ (twistedRootSubgroupD4 σ _).subgroupOf (twistedGroup σ)
    rw [Subgroup.mem_subgroupOf, slLong_val, slLongE_lower]
    exact xPar_neg_single_two_mem_twisted hσ c.2

theorem two_le_pRank_three_twistedD4 (hq : 2 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσq : ∀ c, σ c = c ^ q) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* DerivedCentralQuotient (twistedFixedGroup .D4 K σ)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) := by
  have hσ : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hK hσq
  have hZ := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.twistedGroup_center_eq_bot_of_card
    (σ := σ) hq hK hσq
  set E := twistedGroupEquivDerived σ hq hK hσq with hE
  have hker : ∀ z : twistedGroup σ, (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp
      E.toMonoidHom)) z = 1 → z ∈ Subgroup.center (twistedGroup σ) := by
    intro z hz
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥⁅twistedFixedGroup TwistTag.D4 K σ,
        twistedFixedGroup TwistTag.D4 K σ⁆)) (E z) = 1 := by
      apply e.symm.injective
      simpa using hz
    have h2 : E z ∈ Subgroup.center ↥⁅twistedFixedGroup TwistTag.D4 K σ,
        twistedFixedGroup TwistTag.D4 K σ⁆ := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply E.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.1 h2 (E g))
  obtain ⟨φl, hφl, hlu, hll⟩ := hasSL2Node_d4tw_long hσ
  obtain ⟨φs, hφs, hsu, hsl⟩ := hasSL2Node_d4tw hσ
  have hct := twistedDatum_isCTGroupDatum σ hσ
  have hext := twistedDatum_steinbergExtras σ hσ
  have hcomm := CFSG.AGLEmbedding.ToralCensus.commutes_rankOne_gTwo_long hct hext
    (rfl : (twistedDatum σ).divisible = ∅) (l := ng 0) (s := ng 1) ng_zero_ne_one
    g2_cartan_ng_zero_one g2_cartan_ng_one_zero
  have h1 : φl.range ≤ rankOne (twistedDatum σ).rootGroup (ng 0) :=
    range_le_of_sl2 φl (fun c => Subgroup.mem_sup_left (hlu c))
      (fun c => Subgroup.mem_sup_right (hll c))
  have h2 : φs.range ≤ rankOne (twistedDatum σ).rootGroup (ng 1) :=
    range_le_of_sl2 φs (fun c => Subgroup.mem_sup_left (hsu c))
      (fun c => Subgroup.mem_sup_right (hsl c))
  refine two_le_pRank_three_of_sl2_pair
    (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp E.toMonoidHom)) hker φl
    ((MulAut.conj (nHat σ (ng 1) * nHat σ (ng 0))).toMonoidHom.comp φs) hφl
    ((MulAut.conj (nHat σ (ng 1) * nHat σ (ng 0))).injective.comp hφs) (fun a b => ?_)
  exact hcomm (φl a) (h1 ⟨a, rfl⟩) _ ⟨φs b, h2 ⟨b, rfl⟩, rfl⟩

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank
