module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltSub

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

universe u

namespace IsSubnormalQuotient

open Equiv.Perm.OnCycleFactors

theorem card_support_cycle {α : Type u} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσ : σ ^ 3 = 1) (c : σ.cycleFactorsFinset) : c.val.support.card = 3 := by
  have hmem : c.val.support.card ∈ σ.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map_of_mem _ c.2
  have h1 := (Equiv.Perm.dvd_of_mem_cycleType hmem).trans (orderOf_dvd_of_pow_eq_one hσ)
  have h2 := Equiv.Perm.two_le_of_mem_cycleType hmem
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · omega
  · exact h

theorem range_toPermHom_eq_top {α : Type u} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσ : σ ^ 3 = 1) : (toPermHom σ).range = ⊤ := by
  rw [range_toPermHom_eq_range_toPermHom', eq_top_iff]
  intro τ _
  rw [Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff]
  intro c
  rw [card_support_cycle hσ, card_support_cycle hσ]

theorem alt_of_centralizer {α : Type u} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (hσ : σ ^ 3 = 1) {L : Type*} [Group L] [IsSimpleGroup L] (hL : ¬ Group.IsSolvable L)
    (h : IsSubnormalQuotient (Subgroup.centralizer ({σ} : Set (Equiv.Perm α))) L) :
    ∃ (β : Type u) (_ : Fintype β) (_ : DecidableEq β),
      5 ≤ Nat.card β ∧ Nonempty (L ≃* alternatingGroup β) := by
  classical
  have hrange := range_toPermHom_eq_top hσ
  rcases split (toPermHom σ).rangeRestrict (MonoidHom.rangeRestrict_surjective _) h with h1 | h1
  · have h2 := of_mulEquiv (MulEquiv.subgroupCongr (MonoidHom.ker_rangeRestrict (toPermHom σ))) h1
    let e1 := MonoidHom.ofInjective (kerParam_injective σ)
    let e2 : (kerParam σ).range ≃* (toPermHom σ).ker :=
      (MulEquiv.subgroupCongr kerParam_range_eq).trans
        (Subgroup.equivMapOfInjective (toPermHom σ).ker
          (Subgroup.centralizer ({σ} : Set (Equiv.Perm α))).subtype
          (Subgroup.centralizer ({σ} : Set (Equiv.Perm α))).subtype_injective).symm
    have h3 := of_mulEquiv (e1.trans e2).symm h2
    rcases split (MonoidHom.fst (Equiv.Perm (Function.fixedPoints σ))
        ((c : σ.cycleFactorsFinset) → Subgroup.zpowers c.val))
        (fun u => ⟨(u, 1), rfl⟩) h3 with h4 | h4
    · exfalso
      have : Group.IsSolvable ↥(MonoidHom.fst (Equiv.Perm (Function.fixedPoints σ))
          ((c : σ.cycleFactorsFinset) → Subgroup.zpowers c.val)).ker := by
        refine Group.isSolvable_of_isSolvable_injective
          (f := (MonoidHom.snd (Equiv.Perm (Function.fixedPoints σ))
            ((c : σ.cycleFactorsFinset) → Subgroup.zpowers c.val)).comp (MonoidHom.ker _).subtype)
          ?_
        intro a b hab
        refine Subtype.ext (Prod.ext ?_ hab)
        exact ((MonoidHom.mem_ker).1 a.2).trans ((MonoidHom.mem_ker).1 b.2).symm
      exact h4.false_of_isSolvable hL
    · have : Fintype (Function.fixedPoints σ) := Fintype.ofFinite _
      obtain ⟨h5, h6⟩ := alt_of_perm hL h4
      exact ⟨_, inferInstance, inferInstance, h5, h6⟩
  · have h2 := of_mulEquiv ((MulEquiv.subgroupCongr hrange).trans Subgroup.topEquiv) h1
    obtain ⟨h5, h6⟩ := alt_of_perm hL h2
    exact ⟨_, inferInstance, inferInstance, h5, h6⟩

end IsSubnormalQuotient

end CFSG.HardMathSupport.Solomon.Coordinator
