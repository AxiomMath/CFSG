module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuStage2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36Q
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputsHered

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
  CFSG.EvenSporadicStandard.RuStd.S2

section NoOther

variable {H : Type} [Group H] [Finite H]

theorem ruNoOtherAt_proved
    (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru) (hbal : RuBalanceAt H)
    (hGH1 : GHLemma53_1) (hOut : OutU43TwoGroup) :
    RuNoOtherAt H := by
  intro N L K t u hN hidx hkp hcov hQ hSol _ hTwoL ht ht2 _ M hM hKM hMK hMcov' hC2M
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  have hL : IsSporadic ↥L .Ru := hcov.isSporadic_of_mult hmult
  obtain ⟨s', hs', hMcov⟩ := hMcov'
  rcases List.mem_singleton.1 hs' with rfl
  have hMs : IsSporadic ↥M .Ru := hMcov.isSporadic_of_mult hmult
  have htH : t ∈ centralizer ({u} : Set H) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht u huL).symm
  have hMt : CFSG.conjugate M t = M := by
    by_contra hne
    have hcomp : IsCompIn (CFSG.conjugate M t) (centralizer ({u} : Set H)) :=
      hM.map_conj (Subgroup.inv_mem _ htH)
    have hs2 : IsSporadic ↥(CFSG.conjugate M t) .Ru := by
      obtain ⟨e⟩ := hMs
      exact ⟨(M.equivMapOfInjective (MulAut.conj t⁻¹).toMonoidHom
        (MulAut.conj t⁻¹).injective).symm.trans e⟩
    exact hne (ru_comp_unique hM hcomp hs2 hC2M).symm
  have hKM' : K ≤ M := by
    rw [hMt, sup_idem] at hKM
    exact hKM
  have hbalM := hbal N hN hidx hkp M u hu2 hM hMcov hC2M
  have hperfL : _root_.commutator ↥L = ⊤ := Group.isPerfect_def.1 hcov.isQuasisimple.1
  have hperfM : _root_.commutator ↥M = ⊤ := Group.isPerfect_def.1 hMcov.isQuasisimple.1
  have hLN : L ≤ N := le_of_perfect_of_index_le_four hN.normal (by omega) hperfL
  have hMN : M ≤ N := le_of_perfect_of_index_le_four hN.normal (by omega) hperfM
  have huN : u ∈ N := hLN huL
  have htN : t ∈ N := (sup_le hMN (zpowers_le.2 huN)) (hbalM ▸ htH)
  have hLle : L ≤ centralizer ({t} : Set H) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  have hcompL : IsCompIn L (centralizer ({t} : Set H)) :=
    isCompIn_of_normal hLle hcov.isQuasisimple
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).2
        (hSol.centralizer_le_normalizer ht ht2))
  have hbalL := hbal N hN hidx hkp L t ht2 hcompL hcov hTwoL
  have hz : Config ↥N (L.subgroupOf N) ⟨t, htN⟩ :=
    ruConfig_of_balance hN.isSimpleGroup hN.nonabelian (isSporadic_subgroupOf hLN hL)
      (by rw [Subgroup.orderOf_mk]; exact ht2)
      (mem_centralizer_iff.2 fun l hl =>
        Subtype.ext (mem_centralizer_iff.1 ht l (mem_subgroupOf.1 hl)))
      (centralizer_eq_sup_subgroupOf hLN htN hbalL)
  have hc₁ : Config ↥N (M.subgroupOf N) ⟨u, huN⟩ :=
    ruConfig_of_balance hN.isSimpleGroup hN.nonabelian (isSporadic_subgroupOf hMN hMs)
      (by rw [Subgroup.orderOf_mk]; exact hu2)
      (mem_centralizer_iff.2 fun m hm =>
        Subtype.ext (mem_centralizer_singleton_iff.1 (hM.1 (mem_subgroupOf.1 hm))))
      (centralizer_eq_sup_subgroupOf hMN huN hbalM)
  have hQN := ruPair_subgroupOf hLN hQ'
  have hLs' := isSporadic_subgroupOf hLN hL
  let u'' : ↥(L.subgroupOf N) := ⟨⟨u, huN⟩, mem_subgroupOf.2 huL⟩
  have hu''2 : orderOf u'' = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hu2
  have hcard'' : Nat.card ↥(centralizer ({u''} : Set ↥(L.subgroupOf N))) = 116480 := by
    rw [card_centralizer_subtype (L.subgroupOf N) u'']
    exact card_centralizer_of_ruPair hLs' hQN
  have hK'' : kComponent (L.subgroupOf N) u'' ≤ M.subgroupOf N := by
    unfold kComponent
    rw [map_derivedCentralizer_eq]
    rw [← ruPair_eq_derived hf hLs' hQN]
    exact fun x hx => mem_subgroupOf.2 (hKM' (mem_subgroupOf.1 hx))
  exact ruStage2_of_configs hGH1 hOut
    (fun y hy => isKGroupCat_centralizer_of_fStarSimple hN hkp hy) hz hLs' u'' hu''2 hcard''
    (isSporadic_subgroupOf hMN hMs) hK'' hc₁

theorem ruNoOtherHered_proved
    (hf : RuLocalFacts) (hmult : OddMultTrivial .Ru) (hbal : RuBalanceHered)
    (hGH1 : GHLemma53_1) (hOut : OutU43TwoGroup) :
    RuNoOtherHered :=
  fun H _ _ hH => ruNoOtherAt_proved hf hmult (hbal H hH) hGH1 hOut

end NoOther

end CFSG.EvenSporadicStandard.Induction
