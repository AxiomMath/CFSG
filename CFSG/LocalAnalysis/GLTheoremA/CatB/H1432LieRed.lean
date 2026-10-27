module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432LieDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open ClsRed

private theorem not_chev_of_card_ne_three (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    {N : ℕ} (hT : Nat.card T = N) (hN0 : 0 < N)
    (hN : ∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ 3 → q ^ (3 * N.primeFactorsList.count q) ≤ N)
    (h5 : N ≠ 60) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) : ¬ IsChevSimple r T := by
  set a := N.factorization r
  have hm : r ^ a * (N / r ^ a) = N := Nat.ordProj_mul_ordCompl_eq_self N r
  refine I1416QRows.not_isChevSimple_of_card hb hr hr2 (hT.trans hm.symm)
    (Nat.not_dvd_ordCompl hr hN0.ne') ?_ (fun h => absurd h hr3) (fun _ => by rw [hm]; exact h5)
  by_cases hrN : r ∣ N
  · have hk := hN r ((Nat.mem_primeFactorsList hN0.ne').2 ⟨hr, hrN⟩) hr2 hr3
    rw [Nat.primeFactorsList_count_eq] at hk
    have : r ^ a * r ^ (2 * a) ≤ r ^ a * (N / r ^ a) := by
      rw [hm, ← pow_add]
      calc r ^ (a + 2 * a) = r ^ (3 * a) := by ring_nf
        _ ≤ N := hk
    exact Nat.le_of_mul_le_mul_left this (pow_pos hr.pos a)
  · have ha : a = 0 := Nat.factorization_eq_zero_of_not_dvd hrN
    simp only [ha, mul_zero, pow_zero, Nat.div_one]
    exact hN0

theorem not_isChevSimple_d4three (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : catalogIs T (S8.isD4of 3)) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ¬ IsChevSimple r T := by
  have hc := card_d4three hb hT
  by_cases hr2 : r = 2
  · subst hr2
    exact I1416Rows.not_isChevSimple_two_of_card hb (a := 12)
      (m := 3 ^ 12 * 5 ^ 2 * 7 * 13) (by rw [hc]; norm_num) (by decide) (by norm_num)
      (by norm_num)
  · exact not_chev_of_card_ne_three hb hc (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) hr hr2 hr3

theorem not_isChevSimple_g2three (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : catalogIs T (S8.isG2of 3)) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    ¬ IsChevSimple r T := by
  have hc := card_g2three hb hT
  by_cases hr2 : r = 2
  · subst hr2
    exact I1416Rows.not_isChevSimple_two_of_card hb (a := 6) (m := 3 ^ 6 * 7 * 13)
      (by rw [hc]; norm_num) (by decide) (by norm_num) (by norm_num)
  · exact not_chev_of_card_ne_three hb hc (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) hr hr2 hr3

variable {Q : Type} [Group Q] [Finite Q]

private theorem lie_out_of_model {K I : Subgroup Q} {y : Q} (hM : I1432Model K I y)
    {d : TauCeti.ValidLieTypeIndex} (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hDQ : ∀ r : ℕ, KDChevDownQ 3 r) (hInn : KDChevInner 3) {P : TauCeti.CFSGIndex → Prop}
    (hT : catalogIs (PSimple 3 I) P)
    (hP : ∀ (T : Type) [Group T] [Finite T], catalogIs T P →
      ∀ r : ℕ, r.Prime → r ≠ 3 → ¬ IsChevSimple r T) :
    d.1.characteristic = 3 ∧ ∃ α : MulAut (PSimple 3 K), α ^ 3 = 1 ∧ α ∉ inner (PSimple 3 K) ∧
      ∃ J : Subgroup (PSimple 3 K), GLAPComponent 3 (fixSubgroup α) J ∧
        catalogIs (PSimple 3 J) P := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hq, -, hyN, hy3, hIc, -⟩ := id hM
  have hS : IsSimpleGroup (PSimple 3 K) := hq.2
  have hnab : ∃ a b : PSimple 3 K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hβ3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  have hβ1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := model_chevAut_ne_one hM
  have hyp := isPGroup_zpowers_three hy3
  have hJ := glaPComponent_chevTransfer hp hyN hyp hIc
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hIc
  have hJT : catalogIs (PSimple 3 (chevTransfer 3 K I)) P := by
    obtain ⟨i, hi, ⟨f⟩⟩ := hT
    exact ⟨i, hi, ⟨g.symm.trans f⟩⟩
  have hchev : IsChevSimple d.1.characteristic (PSimple 3 K) :=
    Or.inl ⟨TauCeti.CFSGIndex.lie d, rfl, ⟨e⟩⟩
  by_cases hr : d.1.characteristic = 3
  · refine ⟨hr, chevAut 3 K ⟨y, hyN⟩, hβ3, fun hin => ?_, chevTransfer 3 K I, hJ, hJT⟩
    have hbot := hInn (PSimple 3 K) hS hnab (hr ▸ hchev) _ hβ3 hβ1 hin
    exact glaPComponent_ne_bot' hJ (le_bot_iff.1 (hbot ▸ le_sSup hJ))
  · exact absurd (hDQ _ (PSimple 3 K) hS hnab hchev _ hβ3 _ hJ)
      (hP _ hJT _ (TauCeti.ValidLieTypeIndex.characteristic_prime d) hr)

theorem i1432ClsD4Lie_of_out (hb : LieOrderBridge) (hDQ : ∀ r : ℕ, KDChevDownQ 3 r)
    (hInn : KDChevInner 3) (hOut : I1432LieOut) : I1432ClsD4Lie := by
  intro Q _ _ K I y hM hI d ⟨e⟩
  obtain ⟨hr, α, hα3, hαin, J, hJ, hJT⟩ := lie_out_of_model hM e hDQ hInn hI.1
    fun T _ _ hT r hr hr3 => not_isChevSimple_d4three hb hT hr hr3
  exact Or.inr ((hOut _ d hr ⟨e⟩ α hα3 hαin J hJ).1 hJT)

theorem i1432ClsG2Lie_of_out (hb : LieOrderBridge) (hDQ : ∀ r : ℕ, KDChevDownQ 3 r)
    (hInn : KDChevInner 3) (hOut : I1432LieOut) : I1432ClsG2Lie := by
  intro Q _ _ K I y hM hI d ⟨e⟩
  obtain ⟨hr, α, hα3, hαin, J, hJ, hJT⟩ := lie_out_of_model hM e hDQ hInn hI.1
    fun T _ _ hT r hr hr3 => not_isChevSimple_g2three hb hT hr hr3
  exact Or.inr (Or.inr ((hOut _ d hr ⟨e⟩ α hα3 hαin J hJ).2 hJT))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
