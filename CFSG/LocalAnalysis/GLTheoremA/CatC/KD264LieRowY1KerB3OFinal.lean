module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerB3OModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3B3
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open TauCeti CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem KD264Y1KerB3Odd_holds : KD264Y1KerB3Odd := by
  unfold KD264Y1KerB3Odd KD264Y1Kernel
  intro d _hfin hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, hp⟩ := hP
  have hp3 : q.p ≠ 3 := by
    intro h
    apply hns
    refine Or.inl ⟨CFSGIndex.lie ⟨.B 3 q, hd1⟩, ?_, ⟨MulEquiv.refl _⟩⟩
    show (LieTypeIndex.B 3 q).characteristic = 3
    rw [LieTypeIndex.characteristic_B, h]
  have hq_card : Nat.card (ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show ValidLieTypeIndex.characteristic ⟨.B 3 q, hd1⟩ = q.p from
        LieTypeIndex.characteristic_B 3 q,
      show ValidLieTypeIndex.fieldExponent ⟨.B 3 q, hd1⟩ = q.exponent from
        LieTypeIndex.fieldExponent_B 3 q]
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hchar : ringChar (ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) = q.p :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p q.exponent_pos hq_card
  haveI hcp : CharP ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) q.p := by
    rw [← hchar]
    exact ringChar.charP _
  have h2K : (2 : ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩)) ≠ 0 := by
    intro h
    have h' : q.p ∣ 2 := (CharP.cast_eq_zero_iff _ q.p 2).mp (by exact_mod_cast h)
    exact hp ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp h')
  have h3K : (3 : ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩)) ≠ 0 := by
    intro h
    have h' : q.p ∣ 3 := (CharP.cast_eq_zero_iff _ q.p 3).mp (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp h')
  let φ := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd 3 q hd1 hp
    (by norm_num)
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map φ.toMonoidHom) := isElemAbelian_map φ hE
  have hc' : Nat.card (E.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
  have hK := KB3O.kerConcl_odd3 h2K h3K (E.map φ.toMonoidHom) hE' hc'
  exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv φ E hK

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
