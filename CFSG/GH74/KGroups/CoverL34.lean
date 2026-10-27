
module

public import CFSG.GH74.KGroups.CoverL34Base

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.Checks2
public import CFSG.GH74.KGroups.Checks3
public import CFSG.GH74.KGroups.CoverRank
public import CFSG.GH74.KGroups.L34
public import CFSG.GH74.Generic.Shapes
public meta import CFSG.GH74.KGroups.Checks2
public meta import CFSG.GH74.KGroups.Checks3
public meta import CFSG.GH74.KGroups.L34
public import CFSG.GH74.KGroups.CoverL34Inputs
public meta import CFSG.GH74.KGroups.CoverL34Inputs
public import Certificates.Certificate5112
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.GH74.KGroups.L34Inputs

public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint

theorem QE_valid :
    QE.check = true ∧ QE.orderCertificate = 16 :=
  Certificates.certificate5112.1

theorem QE_ok : ValidSchreier QE := QE_valid.1

theorem QE_le_check : leCheck QE QP = true :=
  Certificates.certificate5112.2.2.2.2.1

theorem QE_le :
    QE.originalSubgroup ≤ QP.originalSubgroup :=
  leCheck_sound QE QP QP_ok QE_le_check

theorem QE_sq : sqOneCheck (elemsT QE) = true :=
  Certificates.certificate5112.2.1

theorem conj_ok :
    conjWordsCheck [PA, PB] eg0 cws (elemsT QE) = true :=
  Certificates.certificate5112.2.2.1

theorem indep_ok : indepCheck eg0 eg1 eg2 = true :=
  Certificates.certificate5112.2.2.2.1

theorem mem0_check : QE.sift eg0 0 = true :=
  Certificates.certificate5112.2.2.2.2.2.1

theorem mem0 :
    eg0 ∈ QE.originalSubgroup := (mem_iff_sift QE QE_ok _).2 mem0_check

theorem mem1_check : QE.sift eg1 0 = true :=
  Certificates.certificate5112.2.2.2.2.2.2.1

theorem mem1 :
    eg1 ∈ QE.originalSubgroup := (mem_iff_sift QE QE_ok _).2 mem1_check

theorem mem2_check : QE.sift eg2 0 = true :=
  Certificates.certificate5112.2.2.2.2.2.2.2

theorem mem2 :
    eg2 ∈ QE.originalSubgroup := (mem_iff_sift QE QE_ok _).2 mem2_check

theorem l34_cover :
    ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    IsPGroup 2 ↥(Subgroup.center K) → LieModel (K ⧸ Subgroup.center K) .PSL 3 2 2 →
      Subgroup.center K ≠ ⊥ → Monoid.exponent ↥(Subgroup.center K) ≠ 4 → ¬ CFSG.GH74.Gen4 K := by
  intro K _ _ hK hZ2 h hZ _
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨e⟩ := equiv_of_lieModel h
  have hcard : Nat.card QE.originalSubgroup = 16 := by rw [card_group QE QE_ok, QE_valid.2]
  have hind := indepCheck_sound indep_ok
  exact not_genLE4_of_double_cover hperf hZ2 hZ hJ (fun C _ _ hC ⟨eC⟩ =>
    not_genLE4_double_cover hC QP.originalSubgroup (eC.trans e) QE.originalSubgroup QE_le hcard
      (sqOneCheck_sound QE QE_ok QE_sq) eg0 (conj_of_words _ _ gens_mem QE QE_ok conj_ok) eg0 eg1 eg2
      mem0 mem1 mem2 hind.1 hind.2.1 hind.2.2.1 hind.2.2.2.1 hind.2.2.2.2.1 hind.2.2.2.2.2.1
      hind.2.2.2.2.2.2)

end CFSG.GH74.KGroups.L34
