
module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertBase

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveCertInputs
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveKer
public import Certificates.Certificate17381

public section

namespace CFSG.HardMathSupport.Dickson.I271.HNFive

open CFSG.Sporadic.He.Native CFSG.Sporadic.F5 CFSG.Sporadic.F5.Native CFSG.Sporadic.HNSchreier
  CFSG.Sporadic.HNSchreier.Native
  CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix
open CFSG.HardMathSupport.Dickson.I271.HNFive.Native

section Facts

theorem hn5_spec_J : Hn5Spec (matJ g3J) (matJ hn5C) := by
  have h := Certificates.certificate17381
  unfold hn5CheckO at h
  dsimp only at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← g3Arr_eq] at h
  have h' := hn5Core_spec h
  rw [toMat_tabMat g3J_rep, toMat_tabMat (prep_seedWordArr cWord cWord_letters)] at h'
  exact h'

theorem hn5_facts :
    g3J ^ 30 = 1 ∧ g3J ^ 6 ≠ 1 ∧ g3J ^ 10 ≠ 1 ∧
    hn5Q * g3J ^ 6 = g3J ^ 6 * hn5Q ∧ g3J ^ 10 * hn5Q ≠ hn5Q * g3J ^ 10 ∧
    ActsTrivM2 (g3J ^ 6) hn5Q ∧ ¬ ActsTrivM2 (g3J ^ 6) (g3J ^ 10) := by
  obtain ⟨h30, h6, h10, hcomm, hncomm, A, Lam, R, W, Phi, hTA, hAL, hqA, hPT, hPs⟩ := hn5_spec_J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact matJ_injective (by rw [matJ_pow, matJ_one]; exact h30)
  · exact fun h => h6 (by rw [← matJ_pow, h, matJ_one])
  · exact fun h => h10 (by rw [← matJ_pow, h, matJ_one])
  · apply matJ_injective
    rw [matJ_mul, matJ_mul, matJ_hn5Q, matJ_pow]
    exact hcomm
  · intro h
    apply hncomm
    have := congrArg matJ h
    rw [matJ_mul, matJ_mul, matJ_hn5Q, matJ_pow] at this
    exact this
  · unfold ActsTrivM2
    rw [matJ_hn5Q, matJ_pow]
    exact vec_fact_q hAL hqA
  · intro hall
    unfold ActsTrivM2 at hall
    rw [matJ_pow, matJ_pow] at hall
    obtain ⟨v, hv, hn⟩ := vec_fact_s hTA hPT hPs
    obtain ⟨w, hw⟩ := hall v hv
    exact hn w hw

theorem hnMovedIn_g3J6 [Finite JH]
    (hord : Nat.card ↥(Subgroup.centralizer ({g3J ^ 6} : Set JH)) ∣ 2 ^ 14 * 3 * 5 ^ 6) :
    HNMovedIn (Subgroup.centralizer ({g3J ^ 6} : Set JH)) := by
  obtain ⟨h30, h6, h10, hcomm, hncomm, hqA, hsA⟩ := hn5_facts
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf (g3J ^ 10) = 3 := orderOf_eq_prime (by rw [← pow_mul]; exact h30) h10
  have hsC : g3J ^ 10 ∈ Subgroup.centralizer ({g3J ^ 6} : Set JH) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← pow_add, ← pow_add, add_comm]
  have hqC : hn5Q ∈ Subgroup.centralizer ({g3J ^ 6} : Set JH) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcomm
  exact hnMovedIn_of_data hord hsC hso hsA hqC hqA hncomm

end Facts

end CFSG.HardMathSupport.Dickson.I271.HNFive
