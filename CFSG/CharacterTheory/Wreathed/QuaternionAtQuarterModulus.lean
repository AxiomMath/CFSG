module

public import CFSG.CharacterTheory.Wreathed.QuaternionNormalQuotient

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def modulusEquiv {m k : ℕ} (h : m = k) : Wreath m ≃* Wreath k := by
  subst k
  exact MulEquiv.refl _

@[simp] theorem modulusEquiv_element {m k : ℕ} (h : m = k)
    (a b : ZMod m) (e : ZMod 2) :
    modulusEquiv h (element m a b e) =
      element k (ZMod.ringEquivCongr h a) (ZMod.ringEquivCongr h b) e := by
  subst k
  simp [modulusEquiv]

theorem twice_half_quarter (l : ℕ) : 2 * (2 * l) = 4 * l := by omega

@[expose] def quaternionAtQuarterSubgroup (l : ℕ) : Subgroup (Wreath (4 * l)) :=
  (quaternionSubgroup (2 * l)).map (modulusEquiv (twice_half_quarter l)).toMonoidHom

theorem quaternionAtQuarter_eq_generated (l : ℕ) :
    quaternionAtQuarterSubgroup l = Subgroup.closure
      {element (4 * l) 1 (-1) 0, element (4 * l) (2 * l : ℕ) 0 1} := by
  rw [quaternionAtQuarterSubgroup, quaternion_range_eq_generated, MonoidHom.map_closure]
  congr 1
  simp only [Set.image_insert_eq, Set.image_singleton]
  have h := twice_half_quarter l
  have h1 : modulusEquiv h (element (2 * (2 * l)) 1 (-1) 0) =
      element (4 * l) 1 (-1) 0 := by
    rw [modulusEquiv_element]
    simp
  have hd : modulusEquiv h (element (2 * (2 * l)) (2 * l : ℕ) 0 1) =
      element (4 * l) (2 * l : ℕ) 0 1 := by
    rw [modulusEquiv_element]
    simp only [map_natCast, map_zero]
  change {modulusEquiv h (element (2 * (2 * l)) 1 (-1) 0),
      modulusEquiv h (element (2 * (2 * l)) (2 * l : ℕ) 0 1)} = _
  rw [h1, hd]

instance quaternionAtQuarter_normal (l : ℕ) : (quaternionAtQuarterSubgroup l).Normal := by
  unfold quaternionAtQuarterSubgroup
  exact Subgroup.Normal.map inferInstance _ (modulusEquiv (twice_half_quarter l)).surjective

@[expose] def quaternionAtQuarterEquiv (l : ℕ) :
    QuaternionGroup (2 * l) ≃* quaternionAtQuarterSubgroup l :=
  (quaternionRangeEquiv (2 * l)).trans
    ((modulusEquiv (twice_half_quarter l)).subgroupMap (quaternionSubgroup (2 * l)))

theorem card_quaternionAtQuarter (l : ℕ) (hl : 0 < l) :
    Nat.card (quaternionAtQuarterSubgroup l) = 2 * (4 * l) := by
  rw [← Nat.card_congr (quaternionAtQuarterEquiv l).toEquiv]
  let : NeZero (2 * l) := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  omega

@[expose] def quaternionAtQuarterQuotientEquiv (l : ℕ) :
    Wreath (4 * l) ⧸ quaternionAtQuarterSubgroup l ≃* Multiplicative (ZMod (4 * l)) :=
  (QuotientGroup.congr (quaternionSubgroup (2 * l)) (quaternionAtQuarterSubgroup l)
    (modulusEquiv (twice_half_quarter l)) rfl).symm.trans
    ((quaternionQuotientEquivCyclic (2 * l)).trans
      ((ZMod.ringEquivCongr (twice_half_quarter l)).toAddEquiv.toMultiplicative))

theorem card_quaternionAtQuarter_quotient (l : ℕ) :
    Nat.card (Wreath (4 * l) ⧸ quaternionAtQuarterSubgroup l) = 4 * l := by
  rw [Nat.card_congr (quaternionAtQuarterQuotientEquiv l).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem quaternionAtQuarter_quotient_isCyclic (l : ℕ) :
    IsCyclic (Wreath (4 * l) ⧸ quaternionAtQuarterSubgroup l) :=
  (quaternionAtQuarterQuotientEquiv l).isCyclic.mpr inferInstance

theorem normalClosure_d_atQuarter (l : ℕ) :
    Subgroup.normalClosure {element (4 * l) (2 * l : ℕ) 0 1} =
      quaternionAtQuarterSubgroup l := by
  have hm := twice_half_quarter l
  have hsource := normalClosure_d_eq_quaternionSubgroup (2 * l)
  have hmap := congrArg (Subgroup.map (modulusEquiv hm).toMonoidHom) hsource
  rw [Subgroup.map_normalClosure _ _ (modulusEquiv hm).surjective] at hmap
  simp only [Set.image_singleton] at hmap
  have hd : modulusEquiv hm (element (2 * (2 * l)) (2 * l : ℕ) 0 1) =
      element (4 * l) (2 * l : ℕ) 0 1 := by
    rw [modulusEquiv_element]
    simp only [map_natCast, map_zero]
  change Subgroup.normalClosure
    {(modulusEquiv hm) (element (2 * (2 * l)) (2 * l : ℕ) 0 1)} =
      quaternionAtQuarterSubgroup l at hmap
  simpa only [hd] using hmap

end CFSG.Wreathed
