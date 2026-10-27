module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge sporOrd)

private theorem not_chev_odd_of_card (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    {N : ℕ} (hT : Nat.card T = N) (hN0 : 0 < N)
    (hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ^ (3 * N.primeFactorsList.count q) ≤ N)
    (h3 : N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (h5 : N ≠ 60) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : ¬ IsChevSimple q T := by
  set a := N.factorization q
  have hm : q ^ a * (N / q ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N q
  refine I1416QRows.not_isChevSimple_of_card hb hq hq2 (hT.trans hm.symm)
    (Nat.not_dvd_ordCompl hq hN0.ne') ?_ (fun _ => by rw [hm]; exact h3)
    (fun _ => by rw [hm]; exact h5)
  by_cases hqN : q ∣ N
  · have hk := hN q ((Nat.mem_primeFactorsList hN0.ne').2 ⟨hq, hqN⟩) hq2
    rw [Nat.primeFactorsList_count_eq] at hk
    have : q ^ a * q ^ (2 * a) ≤ q ^ a * (N / q ^ a) := by
      rw [hm, ← pow_add]
      calc q ^ (a + 2 * a) = q ^ (3 * a) := by ring_nf
        _ ≤ N := hk
    exact Nat.le_of_mul_le_mul_left this (pow_pos hq.pos a)
  · have ha : a = 0 := Nat.factorization_eq_zero_of_not_dvd hqN
    simp only [ha, mul_zero, pow_zero, Nat.div_one]
    exact hN0

private theorem fi24p_not_chev_of_prime (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 1255205709190661721292800) {q : ℕ} (hq : q.Prime) :
    ¬ IsChevSimple q T := by
  by_cases h2 : q = 2
  · subst h2
    exact I1416Rows.not_isChevSimple_two_of_card hb (a := 21)
      (m := 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29) (by rw [hT]; norm_num) (by decide)
      (by norm_num) (by norm_num)
  · exact not_chev_odd_of_card hb hT (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)
      hq h2

private theorem hn_not_chev_of_prime (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 273030912000000) {q : ℕ} (hq : q.Prime) : ¬ IsChevSimple q T := by
  by_cases h2 : q = 2
  · subst h2
    exact I1416Rows.not_isChevSimple_two_of_card hb (a := 14)
      (m := 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19) (by rw [hT]; norm_num) (by decide)
      (by norm_num) (by norm_num)
  · exact not_chev_odd_of_card hb hT (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)
      hq h2

theorem i1420Lie_holds
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hD3 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 q)
    (hD5 : ∀ q : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 5 q) : I1420Lie := by
  intro p z s ht S _ _ idx e β J hcore
  obtain ⟨hS, hnab, hβp, -, -, hJ, ⟨eT⟩, -⟩ := hcore
  have hq : idx.1.characteristic.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime idx
  have hchev : IsChevSimple idx.1.characteristic S :=
    Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨e⟩⟩
  have hcard := (Nat.card_congr eT.toEquiv).trans (hOrd s)
  rcases ht with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
  · exact fi24p_not_chev_of_prime hb (hcard.trans (by norm_num [sporOrd, orderFi24Prime])) hq
      (hD3 idx.1.characteristic S hS hnab hchev β hβp J hJ)
  · exact hn_not_chev_of_prime hb (hcard.trans (by norm_num [sporOrd, orderHN])) hq
      (hD5 idx.1.characteristic S hS hnab hchev β hβp J hJ)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
