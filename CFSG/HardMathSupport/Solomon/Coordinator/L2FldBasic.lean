module

public import CFSG.HardMathSupport.Solomon.Coordinator.L514CL2
import CFSG.Quasithin.EmptyFaithful.SzPS8S6Class
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem l2fld_isTypeL2_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : IsTypeL2 r A) : IsTypeL2 r B :=
  p6_isTypeL2_of_equiv e h

theorem l2fld_isQuasisimple_psl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    CFSG.Open.IsQuasisimple (StatedProj (StatedSL 2 F)) ∧
      Subgroup.center (StatedProj (StatedSL 2 F)) = ⊥ := by
  have hc : ∃ s : Finset F, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four h4
  obtain ⟨hnt, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr hc)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) (n := 2) le_rfl (Or.inr hc)
  have hna : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx⟩ := exists_ne (1 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    have : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = ⊥ := by
      change (⁅(⊤ : Subgroup _), (⊤ : Subgroup _)⁆ : Subgroup _) = ⊥
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a _ b _
      exact (commutatorElement_eq_one_iff_mul_comm.2 (hcon a b)) ▸ Subgroup.one_mem _
    rw [hperf.commutator_eq_top] at this
    exact hx (by
      have : x ∈ (⊥ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
        this ▸ Subgroup.mem_top x
      exact Subgroup.mem_bot.1 this)
  obtain ⟨hq, hz⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
  let e := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  exact ⟨isQuasisimple_open_of_mulEquiv e.symm (isQuasisimple_open hq),
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.center_eq_bot_of_mulEquiv' e.symm hz⟩

theorem l2fld_three_dvd_card_psl2 {F : Type} [Field F] [Finite F] :
    3 ∣ Nat.card (StatedProj (StatedSL 2 F)) := by
  have h := l514c_card_psl2 (F := F)
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have h3 : 3 ∣ q * (q ^ 2 - 1) := by
    have hm : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases hm with hm | hm | hm
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hm) _
    · refine Dvd.dvd.mul_left ?_ _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hm]
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      omega
    · refine Dvd.dvd.mul_left ?_ _
      have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hm]
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      omega
  rw [← h] at h3
  have hc : Nat.Coprime 3 (Nat.gcd 2 (q - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 2 _) (by norm_num)
  exact hc.dvd_of_dvd_mul_right h3

theorem l2fld_isSolvable_psl2_of_card_le_three {F : Type} [Field F] [Finite F] (h : Nat.card F ≤ 3) :
    Group.IsSolvable (StatedProj (StatedSL 2 F)) := by
  have h1 := l514c_card_psl2 (F := F)
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  apply CFSG.Quasithin.SzPS8.S6Class.isSolvable_of_card_le_twelve
  generalize Nat.card F = n at h h1 h2
  interval_cases n <;> norm_num at h1 <;> omega

end CFSG.HardMathSupport.Solomon.Coordinator
