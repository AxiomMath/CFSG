module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Sylow
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Endgame

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

namespace P6

variable {G : Type*} [Group G]

theorem relIndex_eq_two_or_six {K H : Subgroup G} [(K.subgroupOf H).Normal]
    (h : Nonempty (↥H ⧸ K.subgroupOf H ≃* Equiv.Perm (Fin 2)) ∨
      Nonempty (↥H ⧸ K.subgroupOf H ≃* Equiv.Perm (Fin 3))) :
    K.relIndex H = 2 ∨ K.relIndex H = 6 := by
  have e : K.relIndex H = Nat.card (↥H ⧸ K.subgroupOf H) := Subgroup.index_eq_card (K.subgroupOf H)
  rw [e]
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · left
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  · right
    rw [Nat.card_congr f.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl

theorem firstTransferData_of_sylow_quotient [Finite G] {S H H₀ : Subgroup G} {t : G}
    (ht2 : orderOf t = 2) (hSH : fusionIsSylowIn 2 S H) (hH₀H : H₀ ≤ H)
    (hnorm : H ≤ normalizer (H₀ : Set G)) (hidx : H₀.relIndex H = 2 ∨ H₀.relIndex H = 6)
    (htH₀ : t ∉ H₀) (htS : t ∈ S)
    (hfus : ∀ g : G, g⁻¹ * t * g ∈ S → ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    (hsyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) :
    FirstTransferData S (S ⊓ H₀) t := by
  have hS₀ : S ⊓ H₀ ≤ S := inf_le_left
  have hidx' : (S ⊓ H₀).relIndex S = 2 := P6.relIndex_inf_eq_two hSH hH₀H hnorm hidx
  have htS₀ : t ∉ S ⊓ H₀ := fun h => htH₀ h.2
  exact CFSG.LocalAnalysis.EvenBN.Common.firstTransferData_of_relIndex_eq_two hsyl hS₀ hidx' htS
    htS₀ ht2 (CFSG.LocalAnalysis.EvenBN.Tits.S56.s56_forall_conj_notMem S (S ⊓ H₀) t hfus hS₀ hidx'
      htS₀)

end P6

end CFSG.LocalAnalysis.EvenBN.Tits.N
