module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.TauCetiBridge.Minuscule TauCeti CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups
open KDRank3FieldAux

set_option linter.unusedSectionVars false

section Minuscule


theorem kdRank3Field_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) :
    KDRank3FieldAt ⟨.E6 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : TypeE6LieIndex := ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩ with hd
  have hfin : Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.steinberg) := hfin
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d.1
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hchar' : d.1.characteristic = p := hchar
  have hq : Fintype.card d.1.fixedField = p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.1.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_E6 q
    rw [he]
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e6Data_valid d.1.fixedField
    neighbour_cartan_E6 ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1],
      ![1, 2, 2, 3, 2, 1]] (by decide +kernel)
  have h1 := card_mul_le_localRank_of_commuting_SL2 (K := d.1.fixedField) hp hp2 hq
    (fun i => (toQuot (e6Embed d) hC).comp (ρ i))
    (fun i => toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i))
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B])
  have h2 := le_gla_of_carrier e hp h1
  have := q.exponent_pos
  simp at h2
  omega


theorem kdRank3Field_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) :
    KDRank3FieldAt ⟨.E7 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : TypeE7LieIndex := ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩ with hd
  have hfin : Finite (CFSGIndex.lie ⟨.E7 q, hv⟩).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.steinberg) := hfin
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d.1
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hchar' : d.1.characteristic = p := hchar
  have hq : Fintype.card d.1.fixedField = p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.1.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_E7 q
    rw [he]
  have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
    neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1]] (by decide +kernel)
  have h1 := card_mul_le_localRank_of_commuting_SL2 (K := d.1.fixedField) hp hp2 hq
    (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
    (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
    (fun i j hij A B => by simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B])
  have h2 := le_gla_of_carrier e hp h1
  have := q.exponent_pos
  simp at h2
  omega

end Minuscule

section Twisted


theorem kdRank3Field_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    KDRank3FieldAt ⟨.twistedE6 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩ with hd
  have hfin : Finite (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.steinberg) := hfin
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d.1
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hchar' : d.1.characteristic = p := hchar
  have hq : Fintype.card d.1.fixedField = p ^ q.exponent := by
    rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField,
      ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.1.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_twistedE6 q
    rw [he]
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  have h1 := card_mul_le_localRank_of_commuting_SL2 (K := d.1.fixedField) hp hp2 hq
    (fun i => (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) hinj
    (fun i i' hii A B => by
      simp only [MonoidHom.comp_apply, ← map_mul,
        te6SL2_commute (quadFrob d) (quadIncl d) hj hii A B])
  have h2 := le_gla_of_carrier e hp h1
  have := q.exponent_pos
  simp at h2
  omega

theorem kdRank3Field_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) :
    KDRank3FieldAt ⟨.trialityD4 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : ValidLieTypeIndex := ⟨.trialityD4 q, hv⟩ with hd
  have hq : d.fieldOrder = q.card := LieTypeIndex.fieldOrder_trialityD4 q
  have hpc : d.characteristic = q.p := LieTypeIndex.characteristic_trialityD4 q
  have hqp : q.p = p := hpc.symm.trans hchar
  have hp2' : q.p ≠ 2 := hqp ▸ hp2
  have hfe : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_trialityD4 q
  have hcard : Nat.card (cubeField d) = q.card ^ TwistTag.D4.order := by
    rw [card_cubeField, hq]
    rfl
  have hfinK : Finite (cubeField d) :=
    finite_frobeniusFixedSubfield _ _ _ (by have := d.fieldExponent_pos; omega)
  obtain ⟨e'⟩ := CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hp2' (cubeField d) hcard
    (cubeFrob d).toRingHom fun x => Subtype.ext (by
      change ((cubeFrob d x : cubeField d) : d.Closure) = _
      rw [coe_cubeFrob, hq, SubmonoidClass.coe_pow])
  have hfin : Finite (CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  have : Finite (CFSG.Blueprint.DerivedCentralQuotient
      (twistedFixedGroup .D4 (cubeField d) (cubeFrob d).toRingHom)) :=
    Finite.of_equiv _ e'.symm.toEquiv
  have h4 := four_le_localRank_derivedCentralQuotient_D4 (cubeFrob d) q.prime_p hp2' q.exponent_pos
    (cubeFrob_pow_three d) (by rw [card_cubeField, hq, PrimePower.card_def, ← pow_mul, mul_comm])
    (by rw [card_fixSubfield_cubeFrob, hq, PrimePower.card_def])
  have h5 := le_gla_of_carrier (e.trans e'.symm) q.prime_p h4
  rw [hqp] at h5
  omega

end Twisted

theorem kdRank3Field_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) :
    KDRank3FieldAt ⟨.reeG2 m, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hm : 1 ≤ m := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1)
  have hp3 : 3 = p := (LieTypeIndex.characteristic_reeG2 m).symm.trans hchar
  by_cases hm1 : m = 1
  · right; left; exact hm1
  · exfalso
    have hfin : Finite (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := Finite.of_equiv S e.toEquiv
    have : Finite (FixedPointCandidate (ReeG2LieIndex.of m hv).steinberg) := hfin
    have h1 := le_localRank_reeG2 (d := ReeG2LieIndex.of m hv) (m := m)
      (LieTypeIndex.fieldExponent_reeG2 m) hm
    have h2 := le_gla_of_carrier e Nat.prime_three h1
    subst hp3
    omega

end CFSG.LocalAnalysis.GLTheoremA
