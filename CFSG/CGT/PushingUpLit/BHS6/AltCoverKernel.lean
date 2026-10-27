module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.LocalAnalysis.ComponentInitial Equiv Equiv.Perm

variable {P : Type*} [Group P]

theorem ker_eq_zpowers_sq_of_alternating [Finite P] [Group.IsPerfect P] {m : ℕ}
    (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : IsPGroup 2 η.ker) {x : Fin m → P}
    (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1) {i j : Fin m} (hij : i ≠ j) :
    η.ker = Subgroup.zpowers ((x i * x j) ^ 2) := by
  classical
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  set z := (x i * x j) ^ 2 with hzdef
  have hzc : z ∈ Subgroup.center P := hK (by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq hij])
  have hzK : z ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq hij]
  have hz2 : z ^ 2 = 1 := sq_sq_lift_eq_one η hK hK2 hij (hxη i) (hxη j) (hx3 i) (hx3 j)
  have hzij : ∀ i' j', i' ≠ j' → (x i' * x j') ^ 2 = z := fun i' j' hij' =>
    lift_sq_eq η hη hK hK2 hxη hx3 hij' hij
  set K₀ := Subgroup.zpowers z with hK₀
  have : K₀.Normal := ⟨fun k hk g => by
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hc := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hzc e) g
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) e⟩
  have hcardQ : Nat.card (P ⧸ K₀) ≤ (m + 2).factorial / 2 := by
    have h := card_closure_le_of_carmichael m (QuotientGroup.mk' K₀ ∘ x)
      (fun i => by rw [Function.comp_apply, ← map_pow, hx3, map_one])
      (fun i j hij => by
        rw [Function.comp_apply, Function.comp_apply, ← map_mul, ← map_pow, hzij i j hij]
        exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z))
    have hgen : Subgroup.closure (Set.range (QuotientGroup.mk' K₀ ∘ x)) = ⊤ := by
      rw [Set.range_comp, ← MonoidHom.map_closure, hL,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [hgen, Subgroup.card_top] at h
    exact h
  have hP1 : Nat.card P = Nat.card (P ⧸ K₀) * Nat.card K₀ :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K₀
  have hP2 : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  have hle : (m + 2).factorial / 2 * Nat.card η.ker ≤ (m + 2).factorial / 2 * Nat.card K₀ := by
    calc (m + 2).factorial / 2 * Nat.card η.ker = Nat.card P := by rw [hP2, hA]
      _ = Nat.card (P ⧸ K₀) * Nat.card K₀ := hP1
      _ ≤ (m + 2).factorial / 2 * Nat.card K₀ := Nat.mul_le_mul_right _ hcardQ
  have hcard : Nat.card η.ker ≤ Nat.card K₀ := Nat.le_of_mul_le_mul_left hle hApos
  have hK₀le : K₀ ≤ η.ker := (Subgroup.zpowers_le).2 hzK
  exact (Subgroup.eq_of_le_of_card_ge hK₀le hcard).symm

end CFSG.CGT.PushingUpLit.BHS6
