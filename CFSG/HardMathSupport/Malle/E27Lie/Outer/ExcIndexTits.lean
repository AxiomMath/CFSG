module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Defs
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.Sporadic.Schreier.TitsOuterTwo
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem e27LieOuterAutAt_tits : E27LieOuterAutAt (fun i => i = .tits) := by
  rintro K _ _ d hd ⟨e⟩ - u hu3 hout - - -
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .tits := hd
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  have hR : ReeTitsModel K .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl,
      TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩
  obtain ⟨-, -, hO, -⟩ := CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound K 2 1 hR
  let c : Outer K := QuotientGroup.mk' (inner K) u
  have h3 : c ^ 3 = 1 := by
    show QuotientGroup.mk' (inner K) u ^ 3 = 1
    rw [← map_pow, hu3, map_one]
  have h2 : c ^ 2 = 1 := by
    rw [← hO]
    exact pow_card_eq_one'
  have hc : c = 1 := by
    have : c = c ^ 3 * (c ^ 2)⁻¹ := by group
    rw [this, h3, h2]
    simp
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff (N := inner K) u).1 hc
  exact hout k hk.symm

end CFSG.HardMathSupport.Malle.E27Lie
