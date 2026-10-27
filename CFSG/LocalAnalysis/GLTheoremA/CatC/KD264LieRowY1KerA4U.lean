module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4ULift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4SplitThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.KD264LieA4
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem KD264Y1KerU4_holds : KD264Y1KerU4 := by
  unfold KD264Y1KerU4 KD264Y1Kernel
  intro d _hfin hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, h3⟩ := hP
  by_cases h2 : q.card = 2
  · exfalso
    apply hns
    exact Or.inr ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩,
      ⟨h2, rfl⟩, ⟨MulEquiv.refl _⟩⟩
  have hp2 : 2 ≤ q.p := q.prime_p.two_le
  have hQle : q.p ≤ q.p ^ q.exponent := Nat.le_self_pow (by have := q.exponent_pos; omega) q.p
  have hQ2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def q]
    omega
  have hq5 : 5 ≤ q.card := by omega
  have hpq : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  have hfq : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 3 q
  have hPrime : (TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩).Prime :=
    TauCeti.ValidLieTypeIndex.characteristic_prime _
  have hfpos : 0 < TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩ :=
    TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  have hQ : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩ = q.card := by
    rw [hpq, hfq, TauCeti.PrimePower.card_def q]
  set p := TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩
    with hp
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 3 q, hd1⟩
    with hf
  haveI : Fact p.Prime := ⟨hPrime⟩
  have hf0 : f ≠ 0 := by omega
  have hdiv : 3 ∣ p ^ f + 1 := by rw [hQ]; exact h3
  have hUcard : Nat.card (GaloisField p (2 * f)) = p ^ (2 * f) :=
    GaloisField.card p (2 * f) (by omega)
  have hU : UnitaryFieldData p f (GaloisField p (2 * f)) :=
    ⟨hPrime, by omega, hUcard⟩
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨eSL⟩⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.kaU4S3_exists_su2_equiv hU
  have hF : 4 ≤ Nat.card F := by
    rw [hFcard, hQ]
    omega
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three_of_dvd (GaloisField p (2 * f)) (by
    rw [hUcard, two_mul, pow_add]
    have key := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
    rw [one_mul] at key
    rw [key]
    exact Dvd.dvd.mul_right hdiv _)
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hd1
  apply kerConcl_of_equiv e E
  apply kerConcl_PSU4 hU hdiv hζ eSL hF
  · exact isElemAbelian_map e hE
  · rw [Subgroup.card_map_of_injective e.injective, hc]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
