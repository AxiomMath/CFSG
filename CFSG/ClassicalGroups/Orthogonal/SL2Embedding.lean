module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed
public import CFSG.ClassicalGroups.F2Fixed.SL2Fixed

public section

namespace CFSG.ClassicalGroups.F2Fixed

open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem fixedSub_compHom {H G : Type*} [Group H] [Group G] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] (π : H →* G) (S : Set H) :
    @fixedSub H _ M _ (DistribMulAction.compHom M π) S = fixedSub M (π '' S) := by
  ext m
  simp only [mem_fixedSub, Set.forall_mem_image]
  rfl

theorem injective_sl2Upper {E : Type*} [Field E] : Function.Injective (sl2Upper E) := by
  intro s t h
  have := congrArg (fun g : SL(2, E) => (g : Matrix (Fin 2) (Fin 2) E) 0 1) h
  simpa using this

theorem injective_sl2Lower {E : Type*} [Field E] : Function.Injective (sl2Lower E) := by
  intro s t h
  have := congrArg (fun g : SL(2, E) => (g : Matrix (Fin 2) (Fin 2) E) 1 0) h
  simpa using this

theorem card_sl2UpperSub {E : Type*} [Field E] : Nat.card (sl2UpperSub E) = Nat.card E :=
  Nat.card_range_of_injective injective_sl2Upper

theorem card_sl2LowerSub {E : Type*} [Field E] : Nat.card (sl2LowerSub E) = Nat.card E :=
  Nat.card_range_of_injective injective_sl2Lower

end CFSG.ClassicalGroups.F2Fixed

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem card_Lom (u : V) : Nat.card (Lom Q u) = Nat.card (rootGroup Q u) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootGroup_le_elementaryGroup Q u)).toEquiv

theorem card_eq_pow_of_sl2_embedding {E : Type*} [Field E] [Finite E] [CharP E 2]
    (φ : SL(2, E) →* (V ≃ₗ[K] V)) (hφ : Function.Injective φ)
    (hφE : ∀ g, φ g ∈ elementaryGroup Q) {u u' : V}
    (hU : ∀ s, φ (sl2Upper E s) ∈ rootGroup Q u) (hL : ∀ t, φ (sl2Lower E t) ∈ rootGroup Q u')
    (hcU : Nat.card (rootGroup Q u) = Nat.card E) (hcL : Nat.card (rootGroup Q u') = Nat.card E)
    {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M]
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card E ^ (2 * n) := by
  let π : SL(2, E) →* Gom Q := φ.codRestrict (elementaryGroup Q) hφE
  have hπ : Function.Injective π := fun a b h => hφ (congrArg Subtype.val h)
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hmapU : (sl2UpperSub E).map π = Lom Q u := by
    have hfin : Finite (Lom Q u) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [card_Lom, hcU]
      exact hEpos.ne'
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨s, rfl⟩, rfl⟩
      exact hU s
    · rw [Subgroup.card_map_of_injective hπ, card_sl2UpperSub, card_Lom, hcU]
  have hmapL : (sl2LowerSub E).map π = Lom Q u' := by
    have hfin : Finite (Lom Q u') := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [card_Lom, hcL]
      exact hEpos.ne'
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨s, rfl⟩, rfl⟩
      exact hL s
    · rw [Subgroup.card_map_of_injective hπ, card_sl2LowerSub, card_Lom, hcL]
  letI : DistribMulAction SL(2, E) M := DistribMulAction.compHom M π
  have hdec' : IsCompl (fixedSub M (sl2UpperSub E : Set SL(2, E)))
      (fixedSub M (sl2LowerSub E : Set SL(2, E))) := by
    rw [fixedSub_compHom, fixedSub_compHom, ← Subgroup.coe_map, ← Subgroup.coe_map, hmapU, hmapL]
    exact hdec
  exact sl2_card_eq_pow h2 hdec'

end CFSG.ClassicalGroups.Orthogonal
