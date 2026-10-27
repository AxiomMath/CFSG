module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.FixPlaneSpThree
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.SpRankThree

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding

theorem fixPlaneGen_symplectic_index
    {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSymplecticIndex d.1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic) (hl : ¬ P1ThreeLieList p d)
    (hno : ¬ ∃ E : Subgroup (Cat d), CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3) :
    FixPlaneGen (Cat d) p := by
  have hp : p.Prime := Fact.out
  by_cases hp5 : 5 ≤ p
  · exact fixPlaneGen_symplectic_index_five hd hp hp5 hpd
  have hp3 : p = 3 := by
    have := hp.two_le
    interval_cases p <;> first | rfl | omega | (exfalso; revert hp; norm_num)
  subst hp3
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  ·
    have hℓ3 : q.p ≠ 3 := by simpa using hpd.symm
    have hexc : ¬ (q.p = 2 ∧ q.exponent = 3) := by
      rintro ⟨h1, h2⟩
      exact hl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, h1, h2, Or.inl rfl⟩))))))
    let e := CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have : Finite (Cat ⟨.B 2 q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
    have hrkCat : RankLE2 3 (Cat ⟨.B 2 q, hv⟩) := rankLE2_of_not_exists_cube hp hno
    exact FixPlaneGen.of_mulEquiv e hp
      (fixPlaneGen_projectiveSp_two_three q.prime_p q.exponent_pos
        (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hℓ3 hexc
        (rankLE2_of_injective e.symm.toMonoidHom e.symm.injective hrkCat))
  ·
    exfalso
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have : Finite (Cat ⟨.B r q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
    have hrkCat : RankLE2 3 (Cat ⟨.B r q, hv⟩) := rankLE2_of_not_exists_cube hp hno
    refine not_rankLE2_three_projectiveSp (r := r) hr3 ?_
      (rankLE2_of_injective e.symm.toMonoidHom e.symm.injective hrkCat)
    rw [CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv, hq2]
    intro h
    have := (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  ·
    exfalso
    have hr3 : 3 ≤ r := hrange.1
    have hℓ3 : q.p ≠ 3 := by simpa using hpd.symm
    let e := CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have : Finite (Cat ⟨.C r q, hv⟩) := Finite.of_equiv _ e.symm.toEquiv
    have hrkCat : RankLE2 3 (Cat ⟨.C r q, hv⟩) := rankLE2_of_not_exists_cube hp hno
    refine not_rankLE2_three_projectiveSp (r := r) hr3 ?_
      (rankLE2_of_injective e.symm.toMonoidHom e.symm.injective hrkCat)
    rw [card_fixedField_C r q hv]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
