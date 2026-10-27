module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G]

@[expose] def thetaZero {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) : L →* alternatingGroup (Fin 5) :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))

@[expose] def Transports {L : Subgroup G} (θ₀ : L →* alternatingGroup (Fin 5)) (m : G)
    (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ l l' : L, m * (l : G) * m⁻¹ = (l' : G) →
    ((θ₀ l' : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      σ * ((θ₀ l : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * σ⁻¹

structure QData (P S : Subgroup G) (s x : G) (a : ℕ) : Prop where
  two_le : 2 ≤ a
  S_eq : S = zpowers s
  orderOf_s : orderOf s = 2 ^ a
  P_klein : Nonempty (P ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  P_comm_s : ∀ p ∈ P, p * s = s * p
  P_inf_S : P ⊓ S = ⊥
  x_mul_x : x * x = 1
  x_not_mem : x ∉ P ⊔ S
  x_normalizes_P : ∀ p ∈ P, x * p * x⁻¹ ∈ P
  x_normalizes_S : x * s * x⁻¹ ∈ S
  x_acts_nontrivially : ∃ p ∈ P, x * p * x⁻¹ ≠ p

@[expose] def QData.group (P S : Subgroup G) (x : G) : Subgroup G := P ⊔ S ⊔ zpowers x

end CFSG.OddStandard
