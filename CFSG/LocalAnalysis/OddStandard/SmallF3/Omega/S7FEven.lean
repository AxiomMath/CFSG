module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FFrameLem

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def s7fEven (φ : (Fin 5 → ZMod 2) → G) (H : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ H ∧ ∃ σ ∈ alternatingGroup (Fin 5), s7fActs φ h σ}
  one_mem' := ⟨H.one_mem, 1, (alternatingGroup (Fin 5)).one_mem, s7fActs_one φ⟩
  mul_mem' := by
    rintro a b ⟨ha, σ, hσ, haσ⟩ ⟨hb, τ, hτ, hbτ⟩
    exact ⟨H.mul_mem ha hb, σ * τ, (alternatingGroup (Fin 5)).mul_mem hσ hτ,
      s7fActs_mul haσ hbτ⟩
  inv_mem' := by
    rintro a ⟨ha, σ, hσ, haσ⟩
    exact ⟨H.inv_mem ha, σ⁻¹, (alternatingGroup (Fin 5)).inv_mem hσ, s7fActs_inv haσ⟩

theorem s7fEven_le (φ : (Fin 5 → ZMod 2) → G) (H : Subgroup G) : s7fEven φ H ≤ H :=
  fun _ hh => hh.1

theorem S7FFrame.even_perm {t : G} {B E H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (F : S7FFrame t B E H φ) :
    IsPermModuleVia IsEvenVec φ B (s7fEven φ H) (alternatingGroup (Fin 5)) := by
  refine ⟨F.perm.1, F.perm.2.1, F.perm.2.2.1, fun h hh => hh.2, fun σ hσ => ?_⟩
  obtain ⟨h, hh, hhσ⟩ := F.realize σ
  exact ⟨h, ⟨hh, σ, hσ, hhσ⟩, hhσ⟩

end CFSG.OddStandard.SmallF3.Omega
