module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UWittNorm
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem bar_eq_of_cube_dvd {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hdiv : 3 ∣ p ^ f - 1) : ∀ x : K, x ^ 3 = 1 → h.bar x = x := by
  intro x hx
  rw [UnitaryFieldData.bar_apply]
  have hpos : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  obtain ⟨k, hk⟩ := hdiv
  have hpf : p ^ f = 3 * k + 1 := by omega
  rw [hpf, pow_succ, pow_mul, hx, one_pow, one_mul]

theorem KD264Y1KerU6_of_witt
    (hW : ∀ (K : Type) [Field K] (p f : ℕ) (h : UnitaryFieldData p f K), WittEigen6 h) :
    KD264Y1KerU6 := by
  unfold KD264Y1KerU6 KD264Y1Kernel
  intro d _hfin _hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, h3⟩ := hP
  have hpq : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 5 q
  have hfq : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 5 q
  have hPrime : (TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩).Prime :=
    TauCeti.ValidLieTypeIndex.characteristic_prime _
  have hfpos : 0 < TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩ :=
    TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  set p := TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩
    with hp
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 5 q, hd1⟩
    with hf
  haveI : Fact p.Prime := ⟨hPrime⟩
  have hf0 : f ≠ 0 := by omega
  have hQ : p ^ f = q.card := by rw [hpq, hfq, TauCeti.PrimePower.card_def q]
  have hdiv : 3 ∣ p ^ f - 1 := by rw [hQ]; exact h3
  have hUcard : Nat.card (GaloisField p (2 * f)) = p ^ (2 * f) :=
    GaloisField.card p (2 * f) (by omega)
  have hU : UnitaryFieldData p f (GaloisField p (2 * f)) := ⟨hPrime, by omega, hUcard⟩
  haveI : Finite (GaloisField p (2 * f)) := hU.finite
  have hdvd : 3 ∣ Nat.card (GaloisField p (2 * f)) - 1 := by
    rw [hUcard, two_mul, pow_add]
    have key := Nat.mul_self_sub_mul_self_eq (p ^ f) 1
    rw [one_mul] at key
    rw [key]
    exact dvd_mul_of_dvd_right hdiv _
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three_of_dvd (GaloisField p (2 * f)) hdvd
  have hK4 : 4 ≤ Nat.card (GaloisField p (2 * f)) := by
    rw [hUcard]
    have hp2 : 2 ≤ p := hPrime.two_le
    have hf2 : 2 ≤ 2 * f := by omega
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right (by omega) hf2
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hd1
  apply kerConcl_of_equiv e E
  have hζu : IsPrimitiveRoot (((Units.mk0 ζ (hζ.ne_zero (by norm_num)) : (GaloisField p (2 * f))ˣ)) :
      GaloisField p (2 * f)) 3 := by
    simpa using hζ
  exact kerConcl_unitary6_of_witt hU (bar_eq_of_cube_dvd hU hdiv) hζu hK4 (hW _ p f hU)
    (isElemAbelian_map e hE) (by rw [Subgroup.card_map_of_injective e.injective, hc])

theorem KD264Y1KerU6_holds : KD264Y1KerU6 :=
  KD264Y1KerU6_of_witt (fun _ _ _ _ h => WittEigen6_holds h)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
