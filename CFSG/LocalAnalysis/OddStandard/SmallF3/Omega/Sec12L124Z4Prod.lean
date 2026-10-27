module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec124_commute_subtype {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    ∀ (a : H) (b : K), Commute (H.subtype a) (K.subtype b) := fun a b => hc a a.2 b b.2

theorem sec124_noncomm_injective {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    (hd : H ⊓ K = ⊥) :
    Function.Injective (H.subtype.noncommCoprod K.subtype (sec124_commute_subtype hc)) := by
  rw [MonoidHom.noncommCoprod_injective]
  refine ⟨H.subtype_injective, K.subtype_injective, ?_⟩
  rw [range_subtype, range_subtype]
  exact disjoint_iff.2 hd

theorem sec124_noncomm_range {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    (H.subtype.noncommCoprod K.subtype (sec124_commute_subtype hc)).range = H ⊔ K := by
  rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]

@[expose] noncomputable def sec124SupEquiv {H K : Subgroup G}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hd : H ⊓ K = ⊥) : ↥(H ⊔ K) ≃* ↥H × ↥K :=
  ((MonoidHom.ofInjective (sec124_noncomm_injective hc hd)).trans
    (MulEquiv.subgroupCongr (sec124_noncomm_range hc))).symm

theorem sec124SupEquiv_symm_coe {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    (hd : H ⊓ K = ⊥) (p : ↥H × ↥K) :
    (((sec124SupEquiv hc hd).symm p : ↥(H ⊔ K)) : G) = p.1 * p.2 := rfl

theorem sec124_card_sup {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    (hd : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (sec124SupEquiv hc hd).toEquiv, Nat.card_prod]

end CFSG.OddStandard.SmallF3.Omega
