module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowU43
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem not_isChevSimple_odd_of_card_pt (hb : LieOrderBridge) {T : Type} [Group T]
    [Finite T] {N : ℕ} (hT : Nat.card T = N) (hN0 : 0 < N)
    (h3 : N ≠ 360 ∧ N ≠ 504 ∧ N ≠ 25920) (h5 : N ≠ 60) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hk : q ∈ N.primeFactorsList → q ^ (3 * N.primeFactorsList.count q) ≤ N) :
    ¬ IsChevSimple q T := by
  set a := N.factorization q
  have hm : q ^ a * (N / q ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N q
  refine I1416QRows.not_isChevSimple_of_card hb hq hq2 (hT.trans hm.symm)
    (Nat.not_dvd_ordCompl hq hN0.ne') ?_ (fun _ => by rw [hm]; exact h3)
    (fun _ => by rw [hm]; exact h5)
  by_cases hqN : q ∣ N
  · have hk' := hk ((Nat.mem_primeFactorsList hN0.ne').2 ⟨hq, hqN⟩)
    rw [Nat.primeFactorsList_count_eq] at hk'
    have : q ^ a * q ^ (2 * a) ≤ q ^ a * (N / q ^ a) := by
      rw [hm, ← pow_add]
      calc q ^ (a + 2 * a) = q ^ (3 * a) := by ring_nf
        _ ≤ N := hk'
    exact Nat.le_of_mul_le_mul_left this (pow_pos hq.pos a)
  · have ha : a = 0 := Nat.factorization_eq_zero_of_not_dvd hqN
    simp only [ha, mul_zero, pow_zero, Nat.div_one]
    exact hN0

theorem not_isChevSimple_u43_of_ne_three (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 3265920) {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) : ¬ IsChevSimple q T := by
  by_cases h2 : q = 2
  · subst h2
    exact I1416Rows.not_isChevSimple_two_of_card hb (a := 7) (m := 3 ^ 6 * 5 * 7)
      (by rw [hT]; norm_num) (by decide) (by norm_num) (by norm_num)
  · refine not_isChevSimple_odd_of_card_pt hb hT (by norm_num) (by norm_num) (by norm_num) hq h2 ?_
    simp only [Nat.primeFactorsList_ofNat]
    intro hmem
    have : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by simpa using hmem
    rcases this with rfl | rfl | rfl | rfl
    · exact absurd rfl h2
    · exact absurd rfl hq3
    · decide +kernel
    · decide +kernel

theorem suzRow_lie_of_facts {z : ℕ} (hz : z ≠ 1) (hb : LieOrderBridge)
    (hD : ∀ q : ℕ, KDChevDownQ 3 q) (hInn : KDChevInner 3) (h65 : KD65 3)
    (hL2 : KDOutChevCentre) {S : Type} [Group S] [Finite S] (idx : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) {β : MulAut S} {J : Subgroup S}
    (hcore : I1420CoreP 3 (S8.isU4of 3) z β J) {E : Type} [Group E] [Finite E]
    (hE : CFSG.Open.IsQuasisimple E) (hEp : IsPGroup 3 (Subgroup.center E))
    (eE : (E ⧸ Subgroup.center E) ≃* S)
    (hineq : z ∣ Nat.card (Subgroup.center (PQuot 3 J)) * Nat.card (Subgroup.center E)) :
    False := by
  obtain ⟨hS, hnab, hβp, hβ1, -, hJ, hT, -⟩ := hcore
  have hq : idx.1.characteristic.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime idx
  have hchev : IsChevSimple idx.1.characteristic S := Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨e⟩⟩
  by_cases hq3 : idx.1.characteristic = 3
  · rw [hq3] at hchev
    by_cases hin : β ∈ inner S
    · have hbot := hInn S hS hnab hchev β hβp hβ1 hin
      exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ le_sSup hJ))
    · have hZJ := hL2 S idx hq3 e β hβp hin J hJ
      have hZE := h65 S hS hnab hchev ⟨β, hβp, hin⟩ E hE hEp ⟨eE⟩
      rw [hZJ, hZE, Subgroup.card_bot] at hineq
      exact hz (Nat.dvd_one.1 (by simpa using hineq))
  · exact not_isChevSimple_u43_of_ne_three hb (card_eq_of_isU4of_three hT) hq hq3
      (hD idx.1.characteristic S hS hnab hchev β hβp J hJ)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
