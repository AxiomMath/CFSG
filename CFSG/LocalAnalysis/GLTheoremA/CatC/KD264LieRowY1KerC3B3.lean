module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

@[expose] def KD264Y1FamB3Odd (e : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, e = .B 3 q ∧ q.p ≠ 2

@[expose] def KD264Y1KerB3Odd : Prop := KD264Y1Kernel KD264Y1FamB3Odd

theorem KD264Y1KerB3_even (d : ValidLieTypeIndex) (q : PrimePower) (hd : d.1 = .B 3 q)
    (hp : q.p = 2) (hk2 : ¬ k2Lie 3 d.1) [Finite (CFSGIndex.lie d).Group]
    (E : Subgroup (CFSGIndex.lie d).Group) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  obtain ⟨d1, hd1⟩ := d
  simp only at hd
  subst hd
  have hq2 : q.card ≠ 2 := by
    intro h
    apply hk2
    show (3 = 3 ∧ q.card = 2)
    exact ⟨rfl, h⟩
  have hqpow : q.card = 2 ^ q.exponent := by
    rw [PrimePower.card_def, hp]
  have hexp1 : 1 ≤ q.exponent := q.exponent_pos
  have h4 : 4 ≤ q.card := by
    rcases Nat.lt_or_ge q.exponent 2 with h | h
    · have : q.exponent = 1 := by omega
      rw [hqpow, this] at hq2
      norm_num at hq2
    · rw [hqpow]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) h
  have hcardK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show ValidLieTypeIndex.characteristic ⟨.B 3 q, hd1⟩ = q.p from
        LieTypeIndex.characteristic_B 3 q,
      show ValidLieTypeIndex.fieldExponent ⟨.B 3 q, hd1⟩ = q.exponent from
        LieTypeIndex.fieldExponent_B 3 q]
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hcardK]; positivity)
  have hnd3 : ¬ 3 ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) := by
    rw [hcardK, hp]
    intro h
    have h' : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hK3 : (3 : ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩)) ≠ 0 :=
    three_ne_zero_of_not_dvd_card _ hnd3
  have hK4 : 4 ≤ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) := by
    rw [hcardK, hp]
    rw [hqpow] at h4
    exact h4
  let φ := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj 3 q hd1 hp
    (le_refl 3)
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map φ.toMonoidHom) := isElemAbelian_map φ hE
  have hc' : Nat.card (E.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
  have hK := kerConcl_sp3 ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hd1⟩) hK3 hK4
    (E.map φ.toMonoidHom) hE' hc'
  exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv φ E hK

theorem KD264Y1KerB3_of_odd (hodd : KD264Y1KerB3Odd) : KD264Y1KerB3 := by
  unfold KD264Y1KerB3 KD264Y1Kernel
  intro d hfin hns hk2 hk3 hP E hE hc
  obtain ⟨q, hq⟩ := hP
  by_cases hp : q.p = 2
  · exact KD264Y1KerB3_even d q hq hp hk2 E hE hc
  · exact hodd d hns hk2 hk3 ⟨q, hq, hp⟩ E hE hc

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
