module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem Agrp_le_centralizer_x₂ (hC : CentData z ι) :
    Agrp ι ≤ centralizer ({z * ι τ₀} : Set G) := by
  intro a ha
  obtain ⟨ρ, -, rfl⟩ := (mem_Agrp_iff (ι := ι)).mp ha
  rw [mem_centralizer_singleton_iff]
  have hz : ι (liftS8 ρ) * z = z * ι (liftS8 ρ) := (hC.comm (liftS8 ρ)).symm
  have ht : ι (liftS8 ρ) * ι τ₀ = ι τ₀ * ι (liftS8 ρ) := by
    rw [← map_mul, ← map_mul, liftS8_mul_τ₀]
  calc ι (liftS8 ρ) * (z * ι τ₀) = (ι (liftS8 ρ) * z) * ι τ₀ := by group
    _ = (z * ι (liftS8 ρ)) * ι τ₀ := by rw [hz]
    _ = z * (ι (liftS8 ρ) * ι τ₀) := by group
    _ = z * (ι τ₀ * ι (liftS8 ρ)) := by rw [ht]
    _ = (z * ι τ₀) * ι (liftS8 ρ) := by group

theorem commutator_Agrp (ι : Perm (Fin 10) →* G) : ⁅Agrp ι, Agrp ι⁆ = Agrp ι := by
  have hperf : ⁅alternatingGroup (Fin 8), alternatingGroup (Fin 8)⁆ = alternatingGroup (Fin 8) :=
    commutator_alternatingGroup_eq_self (α := Fin 8) (by norm_num)
  rw [Agrp, ← Subgroup.map_commutator (f := ι.comp liftS8)
    (H₁ := alternatingGroup (Fin 8)) (H₂ := alternatingGroup (Fin 8)), hperf]

theorem nonempty_mulEquiv_Agrp (hC : CentData z ι) :
    Nonempty (alternatingGroup (Fin 8) ≃* ↥(Agrp ι)) := by
  exact ⟨Subgroup.equivMapOfInjective (alternatingGroup (Fin 8)) (ι.comp liftS8)
    (hC.inj.comp liftS8_injective)⟩

end CFSG.OddStandard.AltStdSec.SwapPartner
