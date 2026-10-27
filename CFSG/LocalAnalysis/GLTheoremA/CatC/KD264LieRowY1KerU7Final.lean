module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4 CFSG.LocalAnalysis.ComponentInitial

theorem KD264Y1KerU7_holds : KD264Y1KerU7 := by
  unfold KD264Y1KerU7 KD264Y1Kernel
  intro d _hfin _hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, h3⟩ := hP
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 6 q hd1
  set p' := TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 6 q, hd1⟩
    with hp'
  set f' := TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 6 q, hd1⟩
    with hf'
  have hpq : p' = q.p := TauCeti.LieTypeIndex.characteristic_twistedA 6 q
  have hfq : f' = q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 6 q
  have hprime : p'.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime _
  have hfpos : 1 ≤ f' := TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  have hU : UnitaryFieldData p' f' (GaloisField p' (2 * f')) :=
    ⟨hprime, hfpos, GaloisField.card p' (2 * f') (by omega)⟩
  have hcard : p' ^ f' = q.card := by
    rw [hpq, hfq, TauCeti.PrimePower.card_def q]
  have hQ : 3 ∣ p' ^ f' - 1 := by
    rw [hcard]
    exact h3
  apply kerConcl_of_equiv e E
  apply KU7.kerConcl_PSU7 hU hQ
  · exact isElemAbelian_map e hE
  · rw [Subgroup.card_map_of_injective e.injective, hc]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
