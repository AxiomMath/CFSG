module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

open CFSG.RankThree.PartOne.OutStructure CFSG.Assembly.LowTwoRank

theorem noKlein_PSL_two {X : Type} [Group X] {m : ℕ} (h : StatedClassicalModel X .PSL 2 2 m) :
    NoKlein X :=
  noKlein_of_outPNice_two (outPNice_PSL_two Nat.prime_two h)

theorem noKlein_PSp_two {X : Type} [Group X] {m : ℕ} (h : StatedClassicalModel X .PSp 2 2 m) :
    NoKlein X :=
  noKlein_of_outPNice_two (outPNice_PSp_two Nat.prime_two h)

theorem noKlein_PSp_ge_three {X : Type} [Group X] {r m : ℕ} (hr : 3 ≤ r)
    (h : StatedClassicalModel X .PSp r 2 m) : NoKlein X :=
  noKlein_of_outPNice_two (outPNice_PSp_ge_three Nat.prime_two hr h)

theorem noKlein_PSU {X : Type} [Group X] {n m : ℕ} (h : StatedClassicalModel X .PSU n 2 m) :
    NoKlein X := by
  have hm : 1 ≤ m := h.1.2.1
  refine noKlein_of_outPNice_two (outPNice_PSU Nat.prime_two h ?_)
  intro hd
  have h1 : 2 ∣ 2 ^ m + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  omega

theorem noKlein_alternatingGroup {n : ℕ} (hn : n = 5 ∨ 7 ≤ n) :
    NoKlein (alternatingGroup (Fin n)) := by
  refine noKlein_of_index_le_two ?_
  exact Nat.le_of_dvd (by norm_num) (CFSG.Quasithin.SteinbergCB.index_inner_dvd_two hn)

section Small

open CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial

private theorem noKlein_PSL_two_prime {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    (hK : Nat.card K = r) (hodd : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    NoKlein (PSL2 K) := by
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : Inn (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have : Finite (PSL2 K) := inferInstance
  refine noKlein_of_index_le_two ?_
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  rw [hInn, h2, pgl2_psl2Range_index_eq_two K hodd]

theorem noKlein_PSL_two_seven {X : Type} [Group X] (h : StatedClassicalModel X .PSL 2 7 1) :
    NoKlein X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact NoKlein.of_mulEquiv e'.symm (noKlein_PSL_two_prime hK7 hodd hcard)

end Small

section SmallUnitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem noKlein_PSU_three_three {X : Type} [Group X] (h : StatedClassicalModel X .PSU 3 3 1) :
    NoKlein X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 3 1 K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ 3 ^ 1 = 2) := by decide
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := 3)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact NoKlein.of_mulEquiv e'.symm (noKlein_of_outPNice_two (outPNice_primeFormP hU hn3 hq Nat.prime_two (by norm_num)))

end SmallUnitary

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
