module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Open
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ei2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34El1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ej
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ek
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Em2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Em3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34En

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

theorem l34SigmaFourInput_holds : L34SigmaFourInput := by
  intro G _ _ t L S x₁ x₂ lam rho tau W v _ _ ha hv
  have hl := ha.toCtx4L
  have hc := hl.toCtx4Q
  obtain ⟨E, _, _, _, ψ, hdim, hker⟩ := exists_rep_LO ha
  let π : ↥(ctxLO t tau x₁ x₂) →* ↥ψ.range := ψ.rangeRestrict
  have hπ : Function.Surjective π := ψ.rangeRestrict_surjective
  haveI : Finite ↥ψ.range := Finite.of_surjective π hπ
  have hπker : π.ker = (ctxO t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hι : Function.Injective (ψ.range.subtype : ↥ψ.range →* (E ≃ₗ[ZMod 2] E)) :=
    Subtype.val_injective
  have hσL : t * lam ∈ ctxLO t tau x₁ x₂ := by
    rw [t_comm_lam hc]
    exact lamt_mem_LO ha
  have htT : t ∈ closure ({t, tau} : Set G) := subset_closure (by simp)
  have hσρ : (t * lam) * rho * (t * lam)⁻¹ = rho⁻¹ := by
    have hct : Commute t rho := (rho_comm_T hc t htT).symm
    calc (t * lam) * rho * (t * lam)⁻¹ = t * (lam * rho * lam⁻¹) * t⁻¹ := by group
      _ = t * rho⁻¹ * t⁻¹ := by rw [hc.lam_rho]
      _ = rho⁻¹ := by rw [hct.inv_right.eq]; group
  have hcrit := crit_of_surj (ctxLO t tau x₁ x₂) (ctxO t tau x₁ x₂) (ctxPL t tau x₁ x₂) W
    (O_le_ctxPL ha) ((O_le_U hl).trans hv.U_le) (normal_ctxPL ha).1 hv.sylow.1 π hπ hπker
    ψ.range.subtype hι hdim (rho_mem_LO ha) hσL (rho_cubed hc) (rho_not_mem_ctxPL ha)
    (q_mul_self hc) hσρ (normal_ctxPL ha).2 (card_LO_eq_six_mul_card_PL ha)
    (fun _ hp hcomm => fpf_core ha hp hcomm) hv.sylow.2.1 hv.sylow.2.2
    (hv.U_le (q_mem_U hl)) (card_CW_eq ha hv) (card_CO_eq hl)
    (fun w hw hcomm => exists_cent_of_comm_mem ha hv hw hcomm)
  obtain ⟨e⟩ := nonempty_perm_four_of_crit hcrit
  refine ⟨e.toMonoidHom.comp π, e.surjective.comp hπ, ?_⟩
  have hker' : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  rw [hker', hπker]

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
