module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinFour
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate55105

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier FinGlue FinFour

namespace FinJ3

theorem noFourPerfIn_j3R : NoFourPerfIn j3R := by
  obtain ⟨hU2, -, -, hmap, -, hRmem, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hcc : j3u * j3u = 1 := by rw [← pow_two, hU2]
  have hcP : ∀ x ∈ j3P, j3u * x * j3u⁻¹ ∈ j3P := fun x hx => by
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  refine noFourPerfIn_of_reps (c := j3u) (fun x hx => (hRmem x).1 hx) hcc hcP
    (j3Rows.map fun r => tp 6156 r.rep) Nat.prime_two Nat.prime_three (by norm_num)
    (a := 30) (b := 30) ?_ ?_
  · intro t ht htt ht1
    obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht (orderOf_eq_prime (by rw [pow_two]; exact htt) ht1)
    exact ⟨_, List.mem_map_of_mem hr, g, hg, rfl⟩
  · intro t ht
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ht
    obtain ⟨-, -, -, hC, hcard, -⟩ := hrows r hr
    rw [← hC] at hcard ⊢
    exact Certificates.certificate55105 r hr hcard

end FinJ3

theorem finCellB_j3
    {Y : Type} [Group Y]
    (hY : NativeSporadic.IsSporadic Y .J3) : FinCellB Y := by
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥j3P := (e : Y ≃* NativeSporadic.J3).trans j3PermEquiv
  obtain ⟨Θ, -⟩ := ctuc_j3_full_automorphism_permutation_model
  exact finCellB_of (NoFourPerf.of_equiv ((MulAut.congr e').trans Θ.symm)
    (NoFourPerf.of_in FinJ3.noFourPerfIn_j3R))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
