module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.GLS.C3.Prop121

theorem normalCore_eq_bot_of_isSimpleGroup {X : Type*} [Group X] (H : Subgroup X)
    [IsSimpleGroup H] (hnorm : ¬ H.Normal) : H.normalCore = ⊥ := by
  have hN : (H.normalCore.subgroupOf H).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.normalCore.subgroupOf H) with h | h
  · rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le (Subgroup.normalCore_le H)
  · exfalso
    apply hnorm
    rw [Subgroup.subgroupOf_eq_top] at h
    rw [← le_antisymm (Subgroup.normalCore_le H) h]
    exact Subgroup.normalCore_normal H

theorem exists_injective_perm_fin_of_not_normal {X : Type*} [Group X] [Finite X] (H : Subgroup X)
    [IsSimpleGroup H] (hnorm : ¬ H.Normal) {n : ℕ} (hn : H.index = n) :
    ∃ ρ : X →* Equiv.Perm (Fin n), Function.Injective ρ := by
  have hcosets : Nat.card (X ⧸ H) = n := by rw [← Subgroup.index_eq_card, hn]
  let e : (X ⧸ H) ≃ Fin n := Finite.equivFinOfCardEq hcosets
  refine ⟨e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom X (X ⧸ H)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  change e.permCongrHom (MulAction.toPermHom X (X ⧸ H) g) = 1 at hg
  rw [MulEquiv.map_eq_one_iff] at hg
  have hcore : g ∈ H.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
    exact hg
  rw [normalCore_eq_bot_of_isSimpleGroup H hnorm] at hcore
  exact hcore

theorem nonempty_mulEquiv_alt8_of_card_of_alt7 {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = 20160) (H : Subgroup X) (hH : Nonempty (H ≃* alternatingGroup (Fin 7)))
    (hnorm : ¬ H.Normal) : Nonempty (X ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨eH⟩ := hH
  have hHcard : Nat.card H = 2520 := by
    rw [Nat.card_congr eH.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hidx : H.index = 8 := by
    have := H.card_mul_index
    rw [hHcard, hcard] at this
    omega
  have hsimple7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup H := eH.isSimpleGroup
  obtain ⟨ρ, hinj⟩ := exists_injective_perm_fin_of_not_normal H hnorm hidx
  have hrange : Nat.card ρ.range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
  have hperm : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    rw [Nat.card_perm]
    simp [Nat.factorial]
  have hidx2 : ρ.range.index = 2 := by
    have := ρ.range.card_mul_index
    rw [hrange, hperm] at this
    omega
  have hR : ρ.range = alternatingGroup (Fin 8) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hidx2
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hR)⟩

end CFSG.GH74.GLS.C3.Prop121
