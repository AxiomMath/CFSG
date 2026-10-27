module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Ree CFSG.TauCetiBridge TauCeti CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups
open KDRank3FieldAux

set_option linter.unusedSectionVars false

section Base


namespace KDRank3FieldAux

section Geck

variable (d : ValidLieTypeIndex) {τ : Tag} (M : GeckMatch τ d.dynkinType d.dynkinType_valid)

include M

theorem card_mul_le_localRank_geck [Finite (FixedPointCandidate d.geckFrobenius)]
    (hC : commutator ↥(adjointGroup τ d.fixedField) = ⊤) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hq : d.fieldOrder = p ^ f) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (φ : ι → (SL2 d.fixedField →* adjointGroup τ d.fixedField))
    (hφ : ∀ i, Function.Injective (φ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL2 d.fixedField, φ i A * φ j B = φ j B * φ i A) :
    Fintype.card ι * f ≤
      CFSG.Assembly.RankThreeEven.localRank p (FixedPointCandidate d.geckFrobenius) := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  have hinj := toQuot_injective (geckEmbed_injective d M) hC center_adjointGroup_eq_bot
  refine card_mul_le_localRank_of_commuting_SL2 (K := d.fixedField) hp hp2 ?_
    (fun i => (toQuot (geckEmbed d M) hC).comp (φ i)) (fun i => hinj.comp (hφ i))
    (fun i j hij A B => ?_)
  · rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
    exact hq
  · simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

end Geck

end KDRank3FieldAux

theorem kdRank3Field_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) :
    KDRank3FieldAt ⟨.E8 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  have hfin : Finite (CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.geckFrobenius) := hfin
  have hchar' : d.characteristic = p := hchar
  have hq : d.fieldOrder = p ^ q.exponent := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_E8 q
    rw [he]
  have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
    single_edge_perfect .E8 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0, 0]] (by decide +kernel)
  have h1 := card_mul_le_localRank_geck d geckMatchE8 hC hp hp2 hq ι hι hcomm
  have h2 := le_gla_of_carrier e hp h1
  have := q.exponent_pos
  simp at h2
  omega


theorem kdRank3Field_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) :
    KDRank3FieldAt ⟨.F4 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  exfalso
  set d : ValidLieTypeIndex := ⟨.F4 q, hv⟩ with hd
  have hfin : Finite (CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.geckFrobenius) := hfin
  have hchar' : d.characteristic = p := hchar
  have hq : d.fieldOrder = p ^ q.exponent := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_F4 q
    rw [he]
  have hC : commutator ↥(adjointGroup .F4 d.fixedField) = ⊤ :=
    single_edge_perfect .F4 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .F4
    ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]] (by decide +kernel)
  have h1 := card_mul_le_localRank_geck d geckMatchF4 hC hp hp2 hq ι hι hcomm
  have h2 := le_gla_of_carrier e hp h1
  have := q.exponent_pos
  simp at h2
  omega


end Base

section G2


namespace KDRank3FieldAux

theorem dvd_exponent_of_dvd_outer_G2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hqp : q.p = p) {S : Type} [Group S]
    (e0 : S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group)
    (h : p ∣ Nat.card (Outer S)) : p ∣ q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  subst hqp
  set K := GaloisField q.p q.exponent
  have hK : Nat.card K = q.p ^ q.exponent := GaloisField.card _ _ q.exponent_pos.ne'
  have hK' : Nat.card K = q.card := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q hv K hK'
  let e : S ≃* adjointGroup .G2 K :=
    e0.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot))
  have hout : q.p ∣ Nat.card (Outer (adjointGroup .G2 K)) := by
    rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact h
  by_cases h3 : q.p = 3
  · have hchar : CharP K ReeTag.G2.prime := by
      have : CharP K q.p := inferInstance
      rw [show ReeTag.G2.prime = 3 from rfl, ← h3]
      exact this
    have hK3 : Nat.card K = 3 ^ q.exponent := by rw [hK, h3]
    obtain ⟨-, -, ⟨Θ, -, hs, hker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form q.exponent_pos K hK3
    have : NeZero (2 * q.exponent) := ⟨by have := q.exponent_pos; omega⟩
    have hc := card_outer_eq_of_surj Θ hs hker
    have hout2 : q.p ∣ Nat.card (Multiplicative (ZMod (2 * q.exponent))) := by
      rw [← hc]; exact hout
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at hout2
    rcases (Nat.Prime.dvd_mul q.prime_p).1 hout2 with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h2) hp2
    · exact h2
  · obtain ⟨-, Θ, -, hs, hker, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form q.prime_p hp2
        q.exponent_pos K hK .G2 (Or.inr ⟨rfl, h3⟩)
    rw [card_outer_eq_of_surj Θ hs hker, card_ringEquiv_eq q.prime_p q.exponent_pos hK] at hout
    exact hout

end KDRank3FieldAux

theorem kdRank3Field_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) :
    KDRank3FieldAt ⟨.G2 q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hqp : q.p = p := (LieTypeIndex.characteristic_G2 q).symm.trans hchar
  have hpf : p ∣ q.exponent := dvd_exponent_of_dvd_outer_G2 q hv hp hp2 hqp e hout
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hf3 : 3 ≤ q.exponent := hp3.trans (Nat.le_of_dvd q.exponent_pos hpf)
  exfalso
  set d : ValidLieTypeIndex := ⟨.G2 q, hv⟩ with hd
  have hfin : Finite (CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  have : Finite (FixedPointCandidate d.geckFrobenius) := hfin
  have hchar' : d.characteristic = p := hchar
  have hq : d.fieldOrder = p ^ q.exponent := by
    rw [ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hchar']
    have he : d.fieldExponent = q.exponent := LieTypeIndex.fieldExponent_G2 q
    rw [he]
  have h3 : 3 ≤ Nat.card d.fixedField := by
    rw [ValidLieTypeIndex.card_fixedField, hq]
    exact le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hC : commutator ↥(adjointGroup .G2 d.fixedField) = ⊤ :=
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card d.fixedField
      h3).1.commutator_eq_top
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .G2
    ![![1, 0], ![1, 2]] (by decide +kernel)
  have h1 := card_mul_le_localRank_geck d geckMatchG2 hC hp hp2 hq ι hι hcomm
  have h2 := le_gla_of_carrier e hp h1
  simp at h2
  omega

end G2

end CFSG.LocalAnalysis.GLTheoremA
