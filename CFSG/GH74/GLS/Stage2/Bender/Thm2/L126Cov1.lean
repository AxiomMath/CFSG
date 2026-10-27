module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L126Alt
public import CFSG.GH74.Uniqueness.SU.SU13TA0

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L126

open Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA (TwoCover)

section Cov

variable {H : Type} [Group H] [Finite H] (π : H →* alternatingGroup (Fin 11))

@[expose] def Nh (F : Set (Fin 11)) : Subgroup H := (StabF F).comap π

@[expose] def Eh (F : Set (Fin 11)) : Subgroup H := (FixF F).comap π

omit [Finite H] in
theorem Eh_normal_in_Nh (F : Set (Fin 11)) : ((Eh π F).subgroupOf (Nh π F)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  show π ((g : H) * (n : H) * (g : H)⁻¹) ∈ FixF F
  rw [map_mul, map_mul, map_inv]
  exact StabF_conj_FixF F g.2 hn

instance (F : Set (Fin 11)) : ((Eh π F).subgroupOf (Nh π F)).Normal := Eh_normal_in_Nh π F

end Cov

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L126
