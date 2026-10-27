module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28

public section

namespace CFSG.AGLEmbedding

open KFactProofs.L28Local

private theorem l28TorusData {L : Type} [Group L] [Finite L] (hL : IsCaseTwoGroup 3 L)
    (T : Sylow 3 L) : L28Data L (T : Subgroup L) := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hL
  exact l28Data_of_equiv ε₀ T

private theorem l28TorusExistsOrderNine {L : Type} [Group L] [Finite L]
    (hL : IsCaseTwoGroup 3 L) (T : Sylow 3 L) : ∃ a ∈ (T : Subgroup L), orderOf a = 9 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hL
  have hd := l28TorusData hL T
  have hc9 : orderOf (ε₀.symm CFSG.Quasithin.F6.L28Res.g9) = 9 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_g9
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine hd.card_group hd.card_eq
    (E' := Subgroup.zpowers (ε₀.symm CFSG.Quasithin.F6.L28Res.g9))
    (by rw [Nat.card_zpowers, hc9])
  refine ⟨g⁻¹ * ε₀.symm CFSG.Quasithin.F6.L28Res.g9 * g, (hg _).2 ?_, ?_⟩
  · rw [show g * (g⁻¹ * ε₀.symm CFSG.Quasithin.F6.L28Res.g9 * g) * g⁻¹ =
        ε₀.symm CFSG.Quasithin.F6.L28Res.g9 by group]
    exact Subgroup.mem_zpowers _
  · have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (ε₀.symm CFSG.Quasithin.F6.L28Res.g9)
    simpa [MulAut.conj_apply, hc9] using this

section Intrinsic

variable {L : Type} [Group L] [Finite L]

theorem l28_card_sylow_three (hL : IsCaseTwoGroup 3 L) (T : Sylow 3 L) :
    Nat.card (T : Subgroup L) = 9 :=
  (l28TorusData hL T).card_eq

theorem l28_isCyclic_sylow_three (hL : IsCaseTwoGroup 3 L) (T : Sylow 3 L) :
    IsCyclic (T : Subgroup L) := by
  obtain ⟨a, haT, ha⟩ := l28TorusExistsOrderNine hL T
  refine isCyclic_of_orderOf_eq_card (⟨a, haT⟩ : (T : Subgroup L)) ?_
  rw [Subgroup.orderOf_mk, ha, l28_card_sylow_three hL T]

end Intrinsic

end CFSG.AGLEmbedding
