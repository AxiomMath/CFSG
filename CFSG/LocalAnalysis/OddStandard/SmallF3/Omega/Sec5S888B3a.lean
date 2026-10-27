module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH1

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private theorem s888b3a_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem s888b3a_isPGroup_twoCoreIn (X : Subgroup G) : IsPGroup 2 (twoCoreIn X) := by
  unfold twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype

private theorem s888b3a_le_twoCoreIn_of_normal {X P : Subgroup G} (hPX : P ≤ X)
    (hP2 : IsPGroup 2 P) (hn : (P.subgroupOf X).Normal) : P ≤ twoCoreIn X := by
  have hP2' : IsPGroup 2 (P.subgroupOf X) := hP2.comap_subtype
  have hle : P.subgroupOf X ≤ CFSG.pCore 2 ↥X := le_sSup ⟨hn, hP2'⟩
  calc
    P = (P.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hPX).symm
    _ ≤ (CFSG.pCore 2 ↥X).map X.subtype := Subgroup.map_mono hle
    _ = twoCoreIn X := rfl

private theorem s888b3a_mem_all_of_mem {i : Fin 4} {x : G} (hx : x ∈ K i) :
    x ∈ Sec5B517All K := by
  fin_cases i
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hx))
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
  · exact Subgroup.mem_sup_right hx

theorem twoCoreIn_eq_inf [Finite G] (hq : Sec5B517Quad K z) (i : Fin 4) :
    twoCoreIn (K i) = Sec5B517Q8 hq ⊓ K i := by
  refine le_antisymm ?_ ?_
  · intro u hu
    have huK : u ∈ K i := s888b3a_twoCoreIn_le_self (K i) hu
    have huAll : u ∈ Sec5B517All K := s888b3a_mem_all_of_mem huK
    have hpow : ∃ m : ℕ, u ^ (2 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := s888b3a_isPGroup_twoCoreIn (K i) ⟨u, hu⟩
      exact ⟨m, by
        simpa using congrArg (fun y : ↥(twoCoreIn (K i)) => (y : G)) hm⟩
    have huQ : u ∈ Sec5B517Q8 hq := by
      have h := (Sec5B517Quad.mem_core_iff hq).mpr ⟨huAll, hpow⟩
      rwa [hq.core_eq] at h
    exact (mem_inf_K_iff hq i).mpr ⟨huK, Sec5B517Q8.pow_four hq huQ⟩
  · intro u hu
    refine s888b3a_le_twoCoreIn_of_normal inf_le_right ?_ ?_ hu
    · intro x
      refine ⟨2, Subtype.ext ?_⟩
      have hx4 : (x : G) ^ 4 = 1 := ((mem_inf_K_iff hq i).mp x.2).2
      simpa using hx4
    · rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      exact ⟨Sec5B517Q8.conj_mem hq (s888b3a_mem_all_of_mem hk) hh.1,
        (K i).mul_mem ((K i).mul_mem hk hh.2) ((K i).inv_mem hk)⟩

end CFSG.OddStandard.SmallF3.Omega
