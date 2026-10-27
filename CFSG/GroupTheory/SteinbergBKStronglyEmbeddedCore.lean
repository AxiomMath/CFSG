module

public import CFSG.Assembly.OrderReductions.StrongEmbedding
public import CFSG.Foundations.Basic

public section

namespace CFSG.GroupTheory.SteinbergBK

variable {G : Type*} [Group G]

theorem isStronglyEmbedded_iff (H : Subgroup G) :
    IsStronglyEmbedded H ↔ CFSG.OrderReductions.InvolutionGraph.StronglyEmbedded H := by
  rw [CFSG.OrderReductions.InvolutionGraph.stronglyEmbedded_right_conjugate_iff]
  rfl

theorem core_odd [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) :
    Odd (Nat.card ↥(⨅ g : G, conjugate H g)) ∧ (⨅ g : G, conjugate H g) ≤ pPrimeCore 2 G := by
  have hcore : (⨅ g : G, conjugate H g) = H.normalCore := by
    rw [Subgroup.normalCore_eq_iInf_map_conj]
    exact Equiv.iInf_comp (Equiv.inv G) (g := fun g => H.map (MulAut.conj g).toMonoidHom)
  have hodd : Odd (Nat.card H.normalCore) :=
    CFSG.OrderReductions.StrongEmbedding.normalCore_odd H ((isStronglyEmbedded_iff H).mp hH)
  rw [hcore]
  exact ⟨hodd, le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩⟩

end CFSG.GroupTheory.SteinbergBK
