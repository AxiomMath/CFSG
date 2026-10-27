module

public import CFSG.GH74.GLS.Stage1.Main.Closed
public import CFSG.GH74.KGroups.CoverL34

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.GH74.GLS.Stage1.Thm3.Sec5

theorem l34_cover_any
    (K : Type) [Group K] [Finite K] (hK : CFSG.IsQuasisimple K)
    (hZ2 : IsPGroup 2 ↥(Subgroup.center K)) (h : LieModel (K ⧸ Subgroup.center K) .PSL 3 2 2)
    (hZ : Subgroup.center K ≠ ⊥) : ¬ CFSG.GH74.Gen4 K := by
  intro hgen
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨e⟩ := equiv_of_lieModel h
  have hcard : Nat.card QE.originalSubgroup = 16 := by rw [card_group QE QE_ok, QE_valid.2]
  have hind := indepCheck_sound indep_ok
  exact (not_genLE4_of_double_cover hperf hZ2 hZ hJ (fun C _ _ hC ⟨eC⟩ =>
    not_genLE4_double_cover hC QP.originalSubgroup (eC.trans e) QE.originalSubgroup QE_le hcard
      (sqOneCheck_sound QE QE_ok QE_sq) eg0 (conj_of_words _ _ gens_mem QE QE_ok conj_ok) eg0 eg1 eg2
      mem0 mem1 mem2 hind.1 hind.2.1 hind.2.2.1 hind.2.2.2.1 hind.2.2.2.2.1 hind.2.2.2.2.2.1
      hind.2.2.2.2.2.2)) hgen

theorem gen4NoL34_thm :
    Gen4NoL34 := by
  intro G _ _ hG K ⟨hq, hL, hexp⟩
  have hK : Gen4 (HatT K) := Gen4.quotient _ (Gen4.subgroup K hG)
  have hZ2 : IsPGroup 2 ↥(Subgroup.center (HatT K)) := by
    intro z
    refine ⟨2, ?_⟩
    have h4 := Monoid.pow_exponent_eq_one z
    rw [hexp] at h4
    simpa using h4
  have hZ : Subgroup.center (HatT K) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hexp
    simp at hexp
  exact l34_cover_any (HatT K) hq hZ2 hL hZ hK

end CFSG.GH74.GLS.Stage1.Main
