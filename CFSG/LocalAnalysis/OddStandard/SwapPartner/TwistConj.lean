module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapData

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι : Perm (Fin 10) →* G}

theorem centData_conj (hC : CentData z ι) (g : G) :
    CentData (g * z * g⁻¹) ((MulAut.conj g).toMonoidHom.comp ι) := by
  have hφ : ∀ h : G, (MulAut.conj g).toMonoidHom h = g * h * g⁻¹ :=
    fun h => MulAut.conj_apply g h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hφ z, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z,
      hC.order]
  · exact (MulAut.conj g).injective.comp hC.inj
  · intro σ
    calc (g * z * g⁻¹) * (g * ι σ * g⁻¹)
        = g * (z * ι σ) * g⁻¹ := by group
      _ = g * (ι σ * z) * g⁻¹ := by rw [hC.comm σ]
      _ = (g * ι σ * g⁻¹) * (g * z * g⁻¹) := by group
  · intro σ h
    exact hC.ne_z σ ((MulAut.conj g).injective (h.trans (hφ z).symm))
  · intro c hc
    have hc' : g⁻¹ * c * g ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc (g⁻¹ * c * g) * z
          = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [hc]
        _ = z * (g⁻¹ * c * g) := by group
    obtain ⟨σ, hσ | hσ⟩ := hC.cases (g⁻¹ * c * g) hc'
    · refine ⟨σ, Or.inl ?_⟩
      calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
        _ = g * ι σ * g⁻¹ := by rw [hσ]
        _ = (MulAut.conj g).toMonoidHom (ι σ) := (hφ (ι σ)).symm
    · refine ⟨σ, Or.inr ?_⟩
      calc c = g * (g⁻¹ * c * g) * g⁻¹ := by group
        _ = g * (z * ι σ) * g⁻¹ := by rw [hσ]
        _ = (g * z * g⁻¹) * (MulAut.conj g).toMonoidHom (ι σ) := by
              rw [hφ (ι σ)]; group

theorem centData_comp_conj (hC : CentData z ι) (d : Perm (Fin 10)) :
    CentData z (ι.comp (MulAut.conj d).toMonoidHom) := by
  have hψ : ∀ σ : Perm (Fin 10), (MulAut.conj d).toMonoidHom σ = d * σ * d⁻¹ :=
    fun σ => MulAut.conj_apply d σ
  refine ⟨hC.order, ?_, ?_, ?_, ?_⟩
  · exact hC.inj.comp (MulAut.conj d).injective
  · intro σ
    exact hC.comm ((MulAut.conj d).toMonoidHom σ)
  · intro σ
    exact hC.ne_z ((MulAut.conj d).toMonoidHom σ)
  · intro c hc
    obtain ⟨σ', hσ' | hσ'⟩ := hC.cases c hc
    · refine ⟨d⁻¹ * σ' * d, Or.inl ?_⟩
      have hd : d * (d⁻¹ * σ' * d) * d⁻¹ = σ' := by group
      calc c = ι σ' := hσ'
        _ = ι (d * (d⁻¹ * σ' * d) * d⁻¹) := congrArg ι hd.symm
        _ = (ι.comp (MulAut.conj d).toMonoidHom) (d⁻¹ * σ' * d) := by
              rw [MonoidHom.comp_apply, hψ]
    · refine ⟨d⁻¹ * σ' * d, Or.inr ?_⟩
      have hd : d * (d⁻¹ * σ' * d) * d⁻¹ = σ' := by group
      calc c = z * ι σ' := hσ'
        _ = z * ι (d * (d⁻¹ * σ' * d) * d⁻¹) := congrArg (fun x => z * ι x) hd.symm
        _ = z * (ι.comp (MulAut.conj d).toMonoidHom) (d⁻¹ * σ' * d) := by
              rw [MonoidHom.comp_apply, hψ]

end CFSG.OddStandard.AltStdSec.SwapPartner
