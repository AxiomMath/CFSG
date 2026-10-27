module

public import CFSG.GH74.GLS.C3.Layer1.P34RealL2C

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34Real

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

@[expose] def AutLevelPA7 (Kb : Type) [Group Kb] : Prop :=
  Nonempty (Kb ≃* alternatingGroup (Fin 7)) →
    (∀ α : MulAut Kb, orderOf α = 2 → α ∉ innAut Kb →
      (Nat.card ↥(fixedSubgroup Kb α)).factorization 2 = (Nat.card Kb).factorization 2) ∧
    ∀ B : Subgroup (MulAut Kb), IsPGroup 2 ↥B → IsSylowOf 2 (B ⊓ innAut Kb) (innAut Kb) →
      ∀ α ∈ B, orderOf α = 2 → α ∉ innAut Kb → (∀ q ∈ B ⊓ innAut Kb, α * q = q * α) →
        ∃ z : MulAut Kb, AutP34 B α z

@[expose] def B_prop34_autlevel_A7 : Prop :=
  ∀ (Kb : Type) [Group Kb] [Finite Kb], AutLevelPA7 Kb

theorem b_prop34_autlevel_of_A7
    (hA7 : B_prop34_autlevel_A7) : B_prop34_autlevel := by
  intro Kb _ _ _
  refine ⟨?_, ?_⟩
  · intro α hα2 hfa
    rcases hfa with ⟨hne, ⟨F, _, _, e, hodd, hα⟩ | ⟨h7, hout⟩⟩
    · exact fix_two_part_L2 (L2Field_of_fieldAut hodd e hα hne) e hα hα2
    · exact (hA7 Kb h7).1 α hα2 hout
  · intro B hB2 hSyl α hαB hα2 hfa hαc
    rcases hfa with ⟨hne, ⟨F, _, _, e, hodd, hα⟩ | ⟨h7, hout⟩⟩
    · exact autP34_of_L2 (L2Field_of_fieldAut hodd e hα hne) e hB2 hSyl hαB hα2 hα hαc
    · exact (hA7 Kb h7).2 B hB2 hSyl α hαB hα2 hout hαc

end CFSG.GH74.GLS.C3.Layer1.P34Real
