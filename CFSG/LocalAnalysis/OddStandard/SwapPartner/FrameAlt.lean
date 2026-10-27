module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarMain

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

private theorem sign_conj_eq (d σ : Perm (Fin 10)) :
    sign (d * σ * d⁻¹) = sign σ := by
  simp only [map_mul, map_inv]
  exact mul_inv_cancel_comm _ _

theorem map_alternatingGroup_eq_of_even {ι ι₀ : Perm (Fin 10) →* G} {d : Perm (Fin 10)}
    (h : ∀ σ, sign σ = 1 → ι σ = ι₀ (d * σ * d⁻¹)) :
    (alternatingGroup (Fin 10)).map ι = (alternatingGroup (Fin 10)).map ι₀ := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' : sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 hσ
    exact ⟨d * σ * d⁻¹, Equiv.Perm.mem_alternatingGroup.2 (by rw [sign_conj_eq, hσ']),
      (h σ hσ').symm⟩
  · rintro ⟨τ, hτ, rfl⟩
    have hτ' : sign τ = 1 := Equiv.Perm.mem_alternatingGroup.1 hτ
    have hdτ : sign (d⁻¹ * τ * d) = 1 := by
      rw [show sign (d⁻¹ * τ * d) = sign τ by
        simpa only [inv_inv] using sign_conj_eq d⁻¹ τ, hτ']
    refine ⟨d⁻¹ * τ * d, Equiv.Perm.mem_alternatingGroup.2 hdτ, ?_⟩
    rw [h (d⁻¹ * τ * d) hdτ,
      show d * (d⁻¹ * τ * d) * d⁻¹ = τ by group]

theorem map_alternatingGroup_swapIotaHom (h : Setting G L 10) (d : Cyc L Q z)
    (T : ShapeTwo L Q z u) (e : L ≃* alternatingGroup (Fin 10)) :
    (alternatingGroup (Fin 10)).map (swapIotaHom h d T e) = L := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hw, -⟩ := swapIota_mem_of_even h d T e hσ
    simpa only [swapIotaHom_apply] using hw
  · intro hg
    obtain ⟨hw, hew⟩ := swapIota_mem_of_even h d T e (e ⟨g, hg⟩).2
    refine ⟨((e ⟨g, hg⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)), (e ⟨g, hg⟩).2, ?_⟩
    have hwit : (⟨swapIota h d T e
        ((e ⟨g, hg⟩ : alternatingGroup (Fin 10)) : Perm (Fin 10)), hw⟩ : L) = ⟨g, hg⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [hew]
    rw [swapIotaHom_apply]
    exact congrArg Subtype.val hwit

end CFSG.OddStandard.AltStdSec.SwapPartner
