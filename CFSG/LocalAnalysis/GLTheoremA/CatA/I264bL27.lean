module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAut168
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

theorem card_fL27 {S : Type} [Group S] (h : catalogIs S fL27) : Nat.card S = 168 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · exact hi.elim
      · have hq : q.card = 7 := hi
        have h7 : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def, hq]
        obtain ⟨hp, he⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 h7
        have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [hp, he] at hm
        exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hm
      · exact hi.elim
    | _ => exact hi.elim

theorem card_mulAut_dvd_40320 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hT : Nat.card T = 168) : Nat.card (MulAut T) ∣ 40320 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨h8, hP⟩ := I1416Rows.sylow7_facts_168 hT
  obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
  have hdvd := I1416Rows.card_mulAut_dvd_factorial (hP P).2
  rw [h8] at hdvd
  exact hdvd

theorem kDescFam_l27 (p : ℕ) : KDescFam p fL27 := by
  intro hp hp2 Y _ _ K B h hc hcB
  have hS : Nat.card (↥K ⧸ Subgroup.center ↥K) = 168 := card_fL27 hc
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_noncomm_of_simple_card hS (by norm_num)
  refine (false_of_not_sq_dvd hp h hcB (MulEquiv.refl _) ?_).elim
  by_cases hp3 : p = 3
  · subst hp3
    exact I1416Rows.not_sq_three_dvd_card_mulAut_of_card_168 hnab hS
  · exact not_sq_dvd_of_dvd_smooth_mul (a := 7) (b := 2) (M := 5 * 7) hp hp2 hp3
      (squarefree_prime_mul (by norm_num) (by norm_num) (by norm_num)) ((card_mulAut_dvd_40320 hS).trans (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA
