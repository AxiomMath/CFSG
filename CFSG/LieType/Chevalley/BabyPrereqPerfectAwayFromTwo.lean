module

public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem generated_group_perfect_away_from_two
    (τ : Tag) (K : Type*) [Field K]
    (hK : (3 : ℕ∞) ≤ ENat.card K) : commutator (adjointGroup τ K) = ⊤ := by
  by_cases h2 : ringChar K = 2
  swap
  · exact odd_characteristic_perfect τ K h2
  have h2K : (2 : K) = 0 := by
    have h := ringChar.Nat.cast_ringChar (R := K)
    rwa [h2, Nat.cast_ofNat] at h
  obtain ⟨t, ht0, ht1⟩ : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
    by_contra! h
    have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (h x hx)
    have hcard : ENat.card K ≤ 2 := by
      rw [← Set.encard_univ]
      refine (Set.encard_le_encard hsub).trans ?_
      refine (Set.encard_insert_le _ _).trans ?_
      rw [Set.encard_singleton]
      norm_num
    exact absurd (hK.trans hcard) (by norm_num)
  have ht2 : ((Units.mk0 t ht0 : Kˣ) : K) ^ 2 ≠ 1 := by
    rw [Units.val_mk0]
    intro h
    have h0 : (t - 1) ^ 2 = 0 := by linear_combination h - (t - 1) * h2K
    exact ht1 (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))
  rw [eq_top_iff, ← iSup_simplePosSubgroup_sup_simpleNegSubgroup]
  refine iSup_le fun i => ?_
  have htop := (rank_one_scalar_perfect τ K i).1 (Units.mk0 t ht0) ht2
  calc simplePosSubgroup τ K i ⊔ simpleNegSubgroup τ K i
      = (commutator (rankOneSubgroup (τ := τ) (K := K) i)).map
          (rankOneSubgroup (τ := τ) (K := K) i).subtype := by
        rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rfl
    _ = ⁅rankOneSubgroup (τ := τ) (K := K) i, rankOneSubgroup i⁆ :=
        Subgroup.map_subtype_commutator _
    _ ≤ commutator (adjointGroup τ K) := by
        rw [commutator_def]
        exact Subgroup.commutator_mono le_top le_top

end CFSG.LieType.Chevalley
