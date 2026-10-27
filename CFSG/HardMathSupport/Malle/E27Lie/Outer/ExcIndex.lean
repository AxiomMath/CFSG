module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ExcFieldE
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem untwistedModel_of_bridgeAll {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid)
    {K : Type} [Group K] (e : K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    UntwistedChevalleyModel K τ (q.p ^ q.exponent) := by
  have hF := CFSG.TauCetiBridge.card_fieldOf q Nat.one_pos
  rw [pow_one] at hF
  obtain ⟨φ⟩ := hB q hv (CFSG.TauCetiBridge.fieldOf q 1) hF
  exact ⟨CFSG.TauCetiBridge.fieldOf q 1, inferInstance, inferInstance, hF.trans q.card_def,
    ⟨e.trans φ.symm⟩⟩

section


theorem twentySeven_dvd_fixedSubgroup_of_untwistedModel {τ : Tag} {q : PrimePower}
    (hτ : ∀ (F : Type) [Field F], Nat.card F = q.p ^ q.exponent →
      ∀ α : MulAut (adjointGroup τ F), α ^ 3 = 1 → α ∉ inner (adjointGroup τ F) →
        27 ∣ Nat.card (fixedSubgroup α))
    {K : Type} [Group K] (hm : UntwistedChevalleyModel K τ (q.p ^ q.exponent))
    (u : MulAut K) (hu3 : u ^ 3 = 1) (hout : ∀ k : K, u ≠ MulAut.conj k) :
    27 ∣ Nat.card (fixedSubgroup u) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let θ : K ≃* adjointGroup τ F := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ u]
  refine hτ F hF _ (by rw [← map_pow, hu3, map_one]) fun hin => ?_
  obtain ⟨k, hk⟩ := (CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ u).1 hin
  exact hout k hk.symm

end

section


theorem e27LieOuterAutAt_G2 : E27LieOuterAutAt (fun i => ∃ q, i = .G2 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv e
  refine false_of_dvd_twentySeven u hQ (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3
    hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_G2 q.prime_p q.exponent_pos h3 F hF α h3' hα

theorem e27LieOuterAutAt_F4 : E27LieOuterAutAt (fun i => ∃ q, i = .F4 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).f4 q hv e
  refine false_of_dvd_twentySeven u hQ (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3
    hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_F4 q.prime_p q.exponent_pos F hF α h3' hα

theorem e27LieOuterAutAt_E7 : E27LieOuterAutAt (fun i => ∃ q, i = .E7 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e7 q hv e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine false_of_dvd_twentySeven u hQ (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3
    hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_E7 q.exponent_pos F hF α h3' hα

theorem e27LieOuterAutAt_E8 : E27LieOuterAutAt (fun i => ∃ q, i = .E8 q) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - hQ -
  obtain ⟨i, hv⟩ := d
  obtain ⟨q, rfl⟩ := hd
  have hm := untwistedModel_of_bridgeAll
    (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e8 q hv e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine false_of_dvd_twentySeven u hQ (twentySeven_dvd_fixedSubgroup_of_untwistedModel ?_ hm u hu3
    hout)
  intro F _ hF α h3' hα
  exact twentySeven_dvd_fixedSubgroup_E8 q.exponent_pos F hF α h3' hα

end

end CFSG.HardMathSupport.Malle.E27Lie
