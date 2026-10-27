module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactDihedralType
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KDSylow

open CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

theorem nonempty_mulEquiv_sylow {G G' : Type} [Group G] [Group G'] [Finite G] (e : G ≃* G')
    (Q : Sylow 2 G) (T : Sylow 2 G') : Nonempty (↥Q ≃* ↥T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite G' := Finite.of_equiv G e.toEquiv
  exact ⟨(Subgroup.equivMapOfInjective (Q : Subgroup G) e.toMonoidHom e.injective).trans
    (Sylow.equiv (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q) T)⟩

theorem dihedral_of_A1 {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hq2 : q.p ≠ 2) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) (Q : Sylow 2 G) :
    ∃ n : ℕ, 0 < n ∧ Nonempty (↥Q ≃* DihedralGroup n) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨φ⟩⟩ :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have e2 : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨q.p, q.exponent, q.prime_p, q.prime_p.odd_of_ne_two hq2, q.exponent_pos, hcard⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Finite.of_equiv G e2.toEquiv
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)))
  obtain ⟨m, -, ⟨eT⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd T
  obtain ⟨e3⟩ := nonempty_mulEquiv_sylow e2 Q T
  exact ⟨2 ^ m, by positivity, ⟨e3.trans eT⟩⟩

theorem semidihedral_or_wreathed_of_A2 {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hq2 : q.p ≠ 2) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩) (Q : Sylow 2 G) :
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup n)) ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.WreathedTwoGroup n) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨φ⟩⟩ :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hKL : IsLnEps 3 G 1 (q.p ^ q.exponent) := Or.inl ⟨rfl, K, hK, hKfin, hcard, ⟨φ⟩⟩
  have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.odd_of_ne_two hq2).pow
  have h1 : 1 < q.p ^ q.exponent := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  have hmod : q.p ^ q.exponent % 4 = 1 ∨ q.p ^ q.exponent % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with h | h
  · exact Or.inr (Lemma44b.sylow_L3_wr q.prime_p hq2 hKL h h1 Q)
  · exact Or.inl (Lemma44b.sylow_L3_sd q.prime_p hq2 hKL h Q)

theorem semidihedral_or_wreathed_of_twistedA2 {G : Type} [Group G] [Finite G]
    {q : TauCeti.PrimePower} (hq2 : q.p ≠ 2) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) (Q : Sylow 2 G) :
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.SemidihedralGroup n)) ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥Q ≃* CFSG.Open.WreathedTwoGroup n) := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨φ⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hKU : IsLnEps 3 G (-1) (q.p ^ q.exponent) := Or.inr ⟨rfl, K, hK, hKfin, hcard, ⟨φ⟩⟩
  have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.odd_of_ne_two hq2).pow
  have h1 : 1 < q.p ^ q.exponent := Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  have hmod : q.p ^ q.exponent % 4 = 1 ∨ q.p ^ q.exponent % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with h | h
  · exact Or.inl (Lemma44b.sylow_U3_sd q.prime_p hq2 hKU h h1 Q)
  · exact Or.inr (Lemma44b.sylow_U3_wr q.prime_p hq2 hKU h Q)

theorem isDihedralTypeIndex_cases {d : TauCeti.LieTypeIndex} (h : IsDihedralTypeIndex d) :
    (∃ q : TauCeti.PrimePower, d = .A 1 q ∧ q.p ≠ 2) ∨
      (∃ q : TauCeti.PrimePower, d = .A 2 q ∧ q.p ≠ 2) ∨
      ∃ q : TauCeti.PrimePower, d = .twistedA 2 q ∧ q.p ≠ 2 := by
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact False.elim h
    · exact Or.inl ⟨q, rfl, h⟩
    · exact Or.inr (Or.inl ⟨q, rfl, h⟩)
    · exact False.elim h
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact False.elim h
    · exact False.elim h
    · exact Or.inr (Or.inr ⟨q, rfl, h⟩)
    · exact False.elim h
  | _ => exact False.elim h

end KDSylow

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

theorem kdDihedralTypeSylow_holds : KDDihedralTypeSylow := by
  intro A _ _ L S hL hS
  obtain ⟨Q, hQ⟩ := hS
  have eQ : ↥(Q : Subgroup ↥L) ≃* ↥S :=
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hQ)
  obtain ⟨i, hi, ⟨e⟩⟩ := hL
  rcases i with ⟨p, hp⟩ | ⟨m, hm⟩ | d | s
  · exact False.elim hi
  · exact False.elim hi
  · obtain ⟨dd, hv⟩ := d
    rcases KDSylow.isDihedralTypeIndex_cases (d := dd) hi with
      ⟨q, rfl, hq2⟩ | ⟨q, rfl, hq2⟩ | ⟨q, rfl, hq2⟩
    · obtain ⟨n, hn, ⟨e'⟩⟩ := KDSylow.dihedral_of_A1 hq2 hv e Q
      exact Or.inl ⟨n, hn, ⟨eQ.symm.trans e'⟩⟩
    · rcases KDSylow.semidihedral_or_wreathed_of_A2 hq2 hv e Q with
        ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩
      · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.symm.trans e'⟩⟩)
      · exact Or.inr (Or.inr ⟨n, hn, ⟨eQ.symm.trans e'⟩⟩)
    · rcases KDSylow.semidihedral_or_wreathed_of_twistedA2 hq2 hv e Q with
        ⟨n, hn, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩
      · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.symm.trans e'⟩⟩)
      · exact Or.inr (Or.inr ⟨n, hn, ⟨eQ.symm.trans e'⟩⟩)
  · exact False.elim hi

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
