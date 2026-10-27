module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Spec
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate27811
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Class

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

theorem s16F1_j3P :
    S16F1 ↥j3P := by
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, -, -, -, -, hrows, hcov, -⟩ := j3_centData
  obtain ⟨a, b, ha, hb, haτ, hbτ, ha8, hb2, hba, hcard⟩ :=
    S16.f1_dihedral_of_check j3_groupData Certificates.certificate27811.2
  have hall := S16.hall_of_rows (fun r hr => (hrows r hr).2.2.1) hcov
    (τ0 := tp 6156 (j3CentTbl 21)) (by
      intro r hr hout
      simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h
      · rw [h] at hout
        exact absurd hout (by simp)
      · rw [h])
  have hcent : Nat.card ↥(j3P ⊓ centralizer ({tp 6156 (j3CentTbl 21)} :
      Set (Equiv.Perm (Fin 6156)))) = 16 * 153 := by
    have := (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.2.1
    simpa using this
  exact s16F1_of_data le_sup_left e he (m := 153) (by decide) hcent hall ha hb haτ hbτ ha8 hb2 hba
    hcard

end CFSG.EvenSporadicStandard.Fin76b.J3
