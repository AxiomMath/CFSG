module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eh
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eo
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2d2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2s
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem exists_rep_LO (ha : Ctx4A t L S x₁ x₂ lam rho tau) :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module (ZMod 2) E) (_ : Module.Finite (ZMod 2) E)
      (ψ : ↥(ctxLO t tau x₁ x₂) →* (E ≃ₗ[ZMod 2] E)),
      Module.finrank (ZMod 2) E = 6 ∧
        ψ.ker = (ctxO t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂) := by
  have hl : Ctx4L t L S x₁ x₂ lam rho tau := ha.toCtx4L
  have hc : Ctx4Q t L S x₁ x₂ lam rho tau := hl.toCtx4Q
  have hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho) := isSylSL34_of_Ctx4L hl
  obtain ⟨E, i1, i2, i3, ψ, hdim, hker⟩ :=
    exists_rep (ctxLO t tau x₁ x₂) (ctxO t tau x₁ x₂) (fourGrp x₁ x₂) (k := 6)
      (fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn)
      (V_le_O hc)
      (fun g hg v hv => conj_V_of_mem_LO hc hs hg hv)
      (fun a hao b hbo => O_comm_le hc hao hbo)
      (sq_mem_V hl)
      (by rw [hc.card_O, card_fourGrp hc]; norm_num)
  exact ⟨E, i1, i2, i3, ψ, hdim, by
    ext g
    rw [MonoidHom.mem_ker, hker g, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ha.CL_Obar g g.2 h
    · intro hgo a hao
      have hmem : ⁅(g : G), a⁆ ∈ ⁅ctxO t tau x₁ x₂, ctxO t tau x₁ x₂⁆ :=
        Subgroup.commutator_mem_commutator hgo hao
      rw [hl.O_comm] at hmem
      simpa [commutatorElement_def] using hmem⟩

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
