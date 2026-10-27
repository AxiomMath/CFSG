module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem generatedPairGrowth_involutions_normalize_product {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2) :
    z ∈ Subgroup.normalizer (Subgroup.zpowers (z * t) : Set G) ∧
      t ∈ Subgroup.normalizer (Subgroup.zpowers (z * t) : Set G) := by
  have hzinv := inv_eq_self_of_orderOf_eq_two hz
  have htinv := inv_eq_self_of_orderOf_eq_two ht
  have hzz : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have hzconj : z * (z * t) * z⁻¹ = (z * t)⁻¹ := by
    calc
      z * (z * t) * z⁻¹ = t * z := by rw [← mul_assoc z z t, hzz, one_mul, hzinv]
      _ = (z * t)⁻¹ := by rw [mul_inv_rev, hzinv, htinv]
  have htconj : t * (z * t) * t⁻¹ = (z * t)⁻¹ := by
    calc
      t * (z * t) * t⁻¹ = t * z := by group
      _ = (z * t)⁻¹ := by rw [mul_inv_rev, hzinv, htinv]
  constructor
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (z * (z * t) * z⁻¹) = _
    rw [hzconj, Subgroup.zpowers_inv]
  · apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * (z * t) * t⁻¹) = _
    rw [htconj, Subgroup.zpowers_inv]

theorem generatedPairGrowth_two_involutions_product_normal {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t = ⊤) :
    (Subgroup.zpowers (z * t)).Normal := by
  have hn := generatedPairGrowth_involutions_normalize_product hz ht
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le (Subgroup.zpowers_le.mpr hn.1) (Subgroup.zpowers_le.mpr hn.2)

theorem generatedPairGrowth_two_involutions_cosets {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t = ⊤) (b : G) :
    b ∈ Subgroup.zpowers (z * t) ∨ z * b ∈ Subgroup.zpowers (z * t) := by
  let C := Subgroup.zpowers (z * t)
  have hzinv := inv_eq_self_of_orderOf_eq_two hz
  have htinv := inv_eq_self_of_orderOf_eq_two ht
  have hzz : z * z = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
  have hzt : z * t ∈ C := Subgroup.mem_zpowers _
  have htz : t * z ∈ C := by
    have hi := C.inv_mem hzt
    simpa only [mul_inv_rev, hzinv, htinv] using hi
  have hclosure : Subgroup.closure ({z, t} : Set G) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hstep : ∀ a ∈ ({z, t} : Set G), ∀ y : G,
      y ∈ C ∨ z * y ∈ C → a * y ∈ C ∨ z * (a * y) ∈ C := by
    intro a ha y hy
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rcases hy with hy | hy
      · right
        simpa only [← mul_assoc, hzz, one_mul] using hy
      · exact Or.inl hy
    · have hat : a = t := Set.mem_singleton_iff.mp ha
      subst a
      rcases hy with hy | hy
      · right
        simpa only [mul_assoc] using C.mul_mem hzt hy
      · left
        have hmem := C.mul_mem htz hy
        have he : (t * z) * (z * y) = t * y := by
          calc
            (t * z) * (z * y) = t * (z * z) * y := by group
            _ = t * y := by rw [hzz, mul_one]
        rwa [he] at hmem
  have hb : b ∈ Subgroup.closure ({z, t} : Set G) := hclosure.symm ▸ Subgroup.mem_top b
  exact Subgroup.closure_induction_left
    (p := fun y _ => y ∈ C ∨ z * y ∈ C) (Or.inl C.one_mem)
    (fun a ha y _ hy => hstep a ha y hy)
    (fun a ha y _ hy => by
      rcases Set.mem_insert_iff.mp ha with ha | ha
      · rw [ha, hzinv]
        exact hstep z (by simp) y hy
      · have hat : a = t := Set.mem_singleton_iff.mp ha
        subst a
        rw [htinv]
        exact hstep t (by simp) y hy) hb

theorem generatedPairGrowth_two_involutions_product_index {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t = ⊤) :
    (Subgroup.zpowers (z * t)).index ∣ 2 :=
  Subgroup.index_dvd_two_iff'.mpr ⟨z, fun b =>
    (generatedPairGrowth_two_involutions_cosets hz ht hgen b).symm⟩

theorem generatedPairGrowth_not_two_involutions_generate [IsSimpleGroup G]
    {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hnonabelian : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.zpowers z ⊔ Subgroup.zpowers t ≠ ⊤ := by
  intro hgen
  have hn := generatedPairGrowth_two_involutions_product_normal hz ht hgen
  let : (Subgroup.zpowers (z * t)).Normal := hn
  have hcyclic : IsCyclic G := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (z * t)) with hc | hc
    · have hzt : z * t = 1 := Subgroup.mem_bot.mp (hc ▸ Subgroup.mem_zpowers (z * t))
      have htz : t = z := by
        calc
          t = z⁻¹ * (z * t) := by group
          _ = z⁻¹ := by rw [hzt, mul_one]
          _ = z := inv_eq_self_of_orderOf_eq_two hz
      have hzgen : Subgroup.zpowers z = ⊤ := by simpa only [htz, sup_idem] using hgen
      exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z, hzgen⟩
    · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z * t, hc⟩
  let : IsCyclic G := hcyclic
  let : CommGroup G := IsCyclic.commGroup
  obtain ⟨a, b, hab⟩ := hnonabelian
  exact hab (mul_comm a b)

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
