module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Spec
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Certificate27811
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1Class

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.Fin76b

theorem s16F1_j2P :
    S16F1 ↥j2P := by
  obtain ⟨e, he, -⟩ := ctuc_j2_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, -, -, -, -, hrows, hcov, -⟩ :=
    centData_spec j2_groupData card_j2P j2_primes j2_sylowOrder j2_centDataOK
  obtain ⟨a, b, ha, hb, haτ, hbτ, ha8, hb2, hba, hcard⟩ :=
    S16.f1_dihedral_of_check j2_groupData Certificates.certificate27811.1
  have hall := S16.hall_of_rows (fun r hr => (hrows r hr).2.2.1) hcov
    (τ0 := tp 315 (j2CentTbl 9)) (by
      intro r hr hout
      simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h
      · rw [h]
      · rw [h] at hout
        exact absurd hout (by simp)
      · rw [h] at hout
        exact absurd hout (by simp))
  have hcent : Nat.card ↥(j2P ⊓ centralizer ({tp 315 (j2CentTbl 9)} :
      Set (Equiv.Perm (Fin 315)))) = 16 * 21 := by
    have := (hrows _ List.mem_cons_self).2.2.2.2.1
    simpa using this
  exact s16F1_of_data le_sup_left e he (m := 21) (by decide) hcent hall ha hb haτ hbτ ha8 hb2 hba
    hcard

end CFSG.EvenSporadicStandard.Fin76b.J2
