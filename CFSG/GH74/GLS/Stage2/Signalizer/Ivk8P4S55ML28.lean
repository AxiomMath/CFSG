module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MNoP
public import Certificates.Certificate5253
public import CFSG.GH74.KGroups.L28
public import CFSG.GH74.KGroups.CoverEven

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.GH74.Uniqueness.Bender CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.GH74.KGroups.L28 (pa pb sg QA QP QP_closure QP_ok QP_valid)

theorem noN1_L28
    {Y : Type} [Group Y] (hY : LieModel Y .PSL 2 2 3) {p : ℕ} {b : MulAut Y}
    {R₀ : Subgroup Y} : ¬ N1Config Y p b R₀ := by
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.L28.autModel hY
  have : Finite Y := Finite.of_equiv M.P M.e.symm.toEquiv
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (S := Y) (f := 3) (by norm_num) hY
  have hZ : center Y = ⊥ := (BenderType.linear 3 (by norm_num) e).center_eq_bot
  have hQA : QA.originalSubgroup = closure {pa, pb, sg} := by
    rw [CFSG.GH74.KGroups.L28.QA, certificate_originalSubgroup]
    congr 1
    ext g
    simp
  have hPA : M.P ≤ M.A := by
    rw [hP, hA, QP_closure, hQA]
    refine Subgroup.closure_mono ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hcP : Nat.card M.P = 504 := by
    rw [hP, ← QP.orderCertificate_eq_card QP_ok, QP_valid.2]
  refine noN1_of_noP_autModel M hPA hZ (k := 3) (by rw [hcP]; norm_num) (by rw [hcP]; norm_num) ?_
  intro p hp hp2
  rw [hP, hA]
  exact Certificates.certificate5253.2.2.2.2.2.1 p hp hp2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
