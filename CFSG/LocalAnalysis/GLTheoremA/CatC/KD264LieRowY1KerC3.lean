module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3SpKernel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

theorem three_ne_zero_of_not_dvd_card (K : Type) [Field K] [Finite K]
    (h : ¬ 3 ∣ Nat.card K) : (3 : K) ≠ 0 := by
  intro h0
  have h0' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
  have hdvd : ringChar K ∣ 3 := (CharP.cast_eq_zero_iff K (ringChar K) 3).1 h0'
  have hp3 : ringChar K = 3 :=
    ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left CharP.ringChar_ne_one
  apply h
  haveI := Fintype.ofFinite K
  obtain ⟨n, _, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard, hp3]
  exact dvd_pow_self 3 (PNat.ne_zero n)

theorem KD264Y1KerC3_holds : KD264Y1KerC3 := by
  unfold KD264Y1KerC3 KD264Y1Kernel
  intro d _hfin hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl⟩ := hP
  have hstd := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hd1).1
  have hp2 : q.p ≠ 2 := hstd.2
  have hp3 : q.p ≠ 3 := by
    intro h
    apply hns
    refine Or.inl ⟨CFSGIndex.lie ⟨.C 3 q, hd1⟩, ?_, ⟨MulEquiv.refl _⟩⟩
    show LieTypeIndex.characteristic (.C 3 q) = 3
    rw [LieTypeIndex.characteristic_C]
    exact h
  have hqp : 5 ≤ q.p := by
    have h2 := q.prime_p.two_le
    have h4 : q.p ≠ 4 := by
      intro h
      have := q.prime_p
      rw [h] at this
      norm_num at this
    omega
  have hcardK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩) = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show ValidLieTypeIndex.characteristic ⟨.C 3 q, hd1⟩ = q.p from
        LieTypeIndex.characteristic_C 3 q,
      show ValidLieTypeIndex.fieldExponent ⟨.C 3 q, hd1⟩ = q.exponent from
        LieTypeIndex.fieldExponent_C 3 q]
  haveI : Finite ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩) :=
    Nat.finite_of_card_ne_zero (by rw [hcardK]; positivity)
  have hnd3 : ¬ 3 ∣ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩) := by
    rw [hcardK]
    intro h
    have h' : 3 ∣ q.p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1 h').symm
  have hK3 : (3 : ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩)) ≠ 0 :=
    three_ne_zero_of_not_dvd_card _ hnd3
  have h4 : 4 ≤ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩) := by
    rw [hcardK]
    have hpow : q.p ≤ q.p ^ q.exponent :=
      Nat.le_self_pow (Nat.pos_iff_ne_zero.1 q.exponent_pos) q.p
    omega
  let φ := CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj 3 q hd1
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map φ.toMonoidHom) := isElemAbelian_map φ hE
  have hc' : Nat.card (E.map φ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective φ.injective, hc]
  have hK := kerConcl_sp3 ↥(ValidLieTypeIndex.fixedField ⟨.C 3 q, hd1⟩) hK3 h4
    (E.map φ.toMonoidHom) hE' hc'
  exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv φ E hK

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
