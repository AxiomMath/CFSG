module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Field
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open KDRank3FieldAux

namespace KDRank3FieldAux

theorem le_gla_of_hasWitness {d : TauCeti.ValidLieTypeIndex} {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {p k : ℕ} (hp : p.Prime)
    (h : CFSG.RankThree.PartTwo.Census.Spin.HasWitness d.Group p k) :
    k ≤ GLATwoLocalRank p S := by
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv S e.toEquiv
  exact le_gla_of_carrier e hp
    (CFSG.RankThree.PartTwo.Census.Spin.le_localRank_of_hasWitness' hp h)

end KDRank3FieldAux

open CFSG.RankThree.PartTwo.Census.Spin CFSG.Assembly.RankThreeEven TauCeti in
theorem kdRank3Field_B_ge3 (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid)
    (hr : 3 ≤ r) : KDRank3FieldAt ⟨.B r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  have hfin : Finite (CFSGIndex.lie ⟨.B r q, hv⟩).Group := Finite.of_equiv S e.toEquiv
  obtain ⟨hchar', hord, hexp, hrk⟩ := typeB_mk_data r q hv
  have hpq : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic = p := hchar
  have hodd : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic ≠ 2 := by
    rw [hpq]; exact hp2
  have hpc : (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic.Prime := by
    rw [hpq]; exact hp
  have hw : HasWitness (TypeBLieIndex.Group ⟨⟨.B r q, hv⟩, trivial⟩)
      (⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.characteristic
      ((⟨⟨.B r q, hv⟩, trivial⟩ : TypeBLieIndex).1.fieldExponent * 4) := by
    rcases (show r = 3 ∨ 4 ≤ r by omega) with h3 | h4
    · exact CarrierB.hasWitness_bthree ⟨⟨.B r q, hv⟩, trivial⟩ hodd (by omega)
    · exact CarrierB.hasWitness_theta_four ⟨⟨.B r q, hv⟩, trivial⟩ hodd (by omega)
  have h1 := le_gla_of_hasWitness (d := ⟨.B r q, hv⟩) e hpc hw
  rw [hpq, hexp] at h1
  exact absurd ((four_le_of_mul_four q.exponent_pos h1).trans hrank) (by norm_num)

open CFSG.RankThree.PartTwo.Census.Spin CFSG.Assembly.RankThreeEven TauCeti in
theorem kdRank3Field_D (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) :
    KDRank3FieldAt ⟨.D r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  obtain ⟨hchar', hord, hexp, hrk⟩ := typeD_mk_data r q hv
  have hpq : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic = p := hchar
  have hodd : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic ≠ 2 := by
    rw [hpq]; exact hp2
  have hpc : (⟨⟨.D r q, hv⟩, by simp⟩ : TypeDLieIndex).1.characteristic.Prime := by
    rw [hpq]; exact hp
  have hw := CarrierD.hasWitness_theta_four ⟨⟨.D r q, hv⟩, by simp⟩ hodd
  have hw' : HasWitness (ValidLieTypeIndex.Group ⟨.D r q, hv⟩) _ _ := hw
  have h1 := le_gla_of_hasWitness (d := ⟨.D r q, hv⟩) e hpc hw'
  rw [hpq, hexp] at h1
  exact absurd ((four_le_of_mul_four q.exponent_pos h1).trans hrank) (by norm_num)

open CFSG.RankThree.PartTwo.Census.Spin CFSG.Assembly.RankThreeEven TauCeti in
theorem kdRank3Field_twistedD (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid) :
    KDRank3FieldAt ⟨.twistedD r q, hv⟩ := by
  intro p hp hp2 S _ _ ⟨e⟩ hchar hrank hout
  obtain ⟨hchar', hord, hexp, hrk⟩ := typeTwistedD_mk_data r q hv
  have hpq : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic = p := hchar
  have hodd : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic ≠ 2 := by
    rw [hpq]; exact hp2
  have hpc : (⟨⟨.twistedD r q, hv⟩, by simp⟩ : TypeTwistedDLieIndex).1.characteristic.Prime := by
    rw [hpq]; exact hp
  have hw := CarrierTD.hasWitness_theta ⟨⟨.twistedD r q, hv⟩, by simp⟩ hodd
  have hw' : HasWitness (ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) _ _ := hw
  have h1 := le_gla_of_hasWitness (d := ⟨.twistedD r q, hv⟩) e hpc hw'
  rw [hpq, hexp] at h1
  exact absurd ((four_le_of_mul_four q.exponent_pos h1).trans hrank) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
