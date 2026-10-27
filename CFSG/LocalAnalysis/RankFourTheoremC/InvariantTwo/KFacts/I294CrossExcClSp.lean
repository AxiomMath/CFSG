module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClGen
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcE

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank Subgroup

section Symplectic

variable {K : Type} [Field K] [Finite K] {r p : ℕ}

theorem crossExcCl_sylow_statedSp_split (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    (hr : r < p) (S : Sylow p (StatedSp r K)) : IsMulCommutative (S : Subgroup (StatedSp r K)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : 1 ≤ Nat.card K := Finite.card_pos
  have hpK : ¬ p ∣ Nat.card K := fun h => by
    have h1 : p ∣ 1 := by
      have := Nat.dvd_sub h hpq
      rwa [Nat.sub_sub_self hq] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  refine crossExcCl_sylow_abelian_of_torus
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom (r := r) (k := K))
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.torusHom_injective
    (M := Nat.card K ^ (r ^ 2) * ∏ i ∈ Finset.Icc 1 r, crossExcClGeom (Nat.card K) (2 * i)) ?_ ?_ S
  · rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      crossExcCl_prod_pow_two hq]
    ring
  · intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpK (hp.dvd_of_dvd_pow h)
    · exact crossExcCl_not_dvd_prod_geom hp hp2 hq hpq hr h

theorem crossExcCl_sylow_statedSp (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hr : r < p) (R : Sylow p (StatedProj (StatedSp r K))) :
    IsMulCommutative (R : Subgroup (StatedProj (StatedSp r K))) :=
  crossExcCl_sylow_statedProj hp hp2 hpK (by simpa using (by omega : (r + r) / 2 < p))
    (StatedSp r K) (fun hpq S => crossExcCl_sylow_statedSp_split hp hp2 hpq hr S) R

end Symplectic

section Families

theorem crossAtPrime_C_of_lt {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) {p : ℕ} (hrp : r < p) :
    CrossAtPrime ⟨.C r q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedSp hp (by omega) hpK hrp R) P

theorem crossAtPrime_B2 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    {p : ℕ} : CrossAtPrime ⟨.B 2 q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedSp hp (by omega) hpK (by omega) R) P

theorem crossAtPrime_B_even_of_lt {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.p = 2) (hr : 3 ≤ r) {p : ℕ} (hrp : r < p) :
    CrossAtPrime ⟨.B r q, hv⟩ p := by
  refine crossAtPrime_of_sylowAbelian fun hp hp5 hdp L _ _ hs ⟨e⟩ P => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq hr e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact crossExc_not_dvd_pow_of_ne hp q.prime_p hdp'
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => crossExcCl_sylow_statedSp hp (by omega) hpK hrp R) P

end Families

end CFSG.LocalAnalysis.RankFourTheoremC
