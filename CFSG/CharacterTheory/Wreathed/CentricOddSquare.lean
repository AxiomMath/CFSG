module

public import CFSG.CharacterTheory.Wreathed.CyclicTwoAutomorphism
public import CFSG.GroupTheory.AutomorphismRestrictionKernel
public import CFSG.CharacterTheory.Wreathed.OriginalCoordinates

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

@[expose] def halfCoordinate (l : ℕ) : ZMod 2 →+ ZMod (4 * l) where
  toFun e := if e = 0 then 0 else (2 * l : ℕ)
  map_zero' := by simp
  map_add' e f := by
    rcases swap_exponent_cases e with rfl | rfl <;>
      rcases swap_exponent_cases f with rfl | rfl
    · simp
    · simp
    · simp
    · rw [show (1 + 1 : ZMod 2) = 0 by decide]
      simpa only [↓reduceIte, one_ne_zero, Nat.cast_mul, Nat.cast_ofNat] using
        (twice_quarter_add_self l).symm

theorem halfCoordinate_cases (l : ℕ) (e : ZMod 2) :
    halfCoordinate l e = 0 ∨ halfCoordinate l e = (2 * l : ℕ) := by
  rcases swap_exponent_cases e with rfl | rfl <;> simp [halfCoordinate]

theorem halfCoordinate_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (halfCoordinate l) := by
  intro e f h
  rcases swap_exponent_cases e with rfl | rfl <;>
    rcases swap_exponent_cases f with rfl | rfl
  · rfl
  · exact False.elim (half_quarter_ne_zero l hl (by simpa [halfCoordinate] using h.symm))
  · exact False.elim (half_quarter_ne_zero l hl (by simpa [halfCoordinate] using h))
  · rfl

@[expose] def smallBaseHom (l : ℕ) :
    Multiplicative (ZMod (4 * l)) × Multiplicative (ZMod 2) →* Wreath (4 * l) where
  toFun c := element (4 * l) (c.1.toAdd + halfCoordinate l c.2.toAdd) c.1.toAdd 0
  map_one' := by simp
  map_mul' c d := by
    change element (4 * l)
      (c.1.toAdd + d.1.toAdd + halfCoordinate l (c.2.toAdd + d.2.toAdd))
      (c.1.toAdd + d.1.toAdd) 0 = _
    rw [map_add, element_base_mul]
    congr 1
    abel

@[expose] def smallBase (l : ℕ) : Subgroup (Wreath (4 * l)) := (smallBaseHom l).range

theorem smallBaseHom_injective (l : ℕ) (hl : 0 < l) :
    Function.Injective (smallBaseHom l) := by
  intro c d h
  have hc := (element_eq_iff _ _ _ _ _ _ _).mp h
  apply Prod.ext
  · exact Multiplicative.toAdd.injective hc.2.1
  · apply Multiplicative.toAdd.injective
    apply halfCoordinate_injective l hl
    rw [hc.2.1] at hc
    exact add_left_cancel hc.1

theorem element_mem_smallBase (l : ℕ) (a b : ZMod (4 * l)) (e : ZMod 2) :
    element (4 * l) a b e ∈ smallBase l ↔
      e = 0 ∧ (a - b = 0 ∨ a - b = (2 * l : ℕ)) := by
  constructor
  · rintro ⟨c, hc⟩
    have hcoord := (element_eq_iff _ _ _ _ _ _ _).mp hc
    refine ⟨hcoord.2.2.symm, ?_⟩
    rw [← hcoord.1, ← hcoord.2.1]
    simpa only [add_sub_cancel_left] using halfCoordinate_cases l c.2.toAdd
  · rintro ⟨rfl, h | h⟩
    · refine ⟨(Multiplicative.ofAdd b, Multiplicative.ofAdd 0), ?_⟩
      change element (4 * l) (b + halfCoordinate l 0) b 0 = element (4 * l) a b 0
      simp only [map_zero, add_zero, sub_eq_zero.mp h]
    · refine ⟨(Multiplicative.ofAdd b, Multiplicative.ofAdd 1), ?_⟩
      change element (4 * l) (b + halfCoordinate l 1) b 0 = element (4 * l) a b 0
      change element (4 * l) (b + (2 * l : ℕ)) b 0 = element (4 * l) a b 0
      congr 1
      linear_combination -h

theorem smallBase_le_base (l : ℕ) : smallBase l ≤ baseSubgroup (4 * l) := by
  intro g hg
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
  exact (element_mem_base _ _ _ _).mpr ((element_mem_smallBase _ _ _ _).mp hg).1

theorem smallBase_eq_generated (l : ℕ) :
    smallBase l = Subgroup.closure {Original.a (4 * l), Original.x2 (4 * l)} := by
  let D := Subgroup.closure {Original.a (4 * l), Original.x2 (4 * l)}
  have ha : Original.a (4 * l) ∈ D := Subgroup.subset_closure (by simp)
  have hx : Original.x2 (4 * l) ∈ D := Subgroup.subset_closure (by simp)
  have hdiag (c : ZMod (4 * l)) : element (4 * l) c c 0 ∈ D := by
    have h : element (4 * l) c c 0 ∈ (diagonalHom (4 * l)).range :=
      ⟨Multiplicative.ofAdd c, rfl⟩
    rw [diagonal_range_eq_zpowers, ← Original.a_eq] at h
    exact Subgroup.zpowers_le_of_mem ha h
  change smallBase l = D
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
    change element (4 * l) a b e ∈ D
    change element (4 * l) a b e ∈ smallBase l at hg
    rcases (element_mem_smallBase _ _ _ _).mp hg with ⟨rfl, h | h⟩
    · rw [sub_eq_zero.mp h]
      exact hdiag b
    · have hp := D.mul_mem (hdiag b) hx
      rw [Original.x2_eq, show 4 * l / 2 = 2 * l by omega, element_base_mul] at hp
      have heq : b + (2 * l : ℕ) = a := by linear_combination -h
      simpa only [heq, add_zero] using hp
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | h
    · simp [Original.a_eq, element_mem_smallBase]
    · rw [Set.mem_singleton_iff.mp h, Original.x2_eq,
        show 4 * l / 2 = 2 * l by omega]
      simp [element_mem_smallBase]

@[expose] def smallBaseEquiv (l : ℕ) (hl : 0 < l) :
    Multiplicative (ZMod (4 * l)) × Multiplicative (ZMod 2) ≃* smallBase l :=
  MonoidHom.ofInjective (smallBaseHom_injective l hl)

theorem card_smallBase (l : ℕ) (hl : 0 < l) : Nat.card (smallBase l) = 2 * (4 * l) := by
  rw [← Nat.card_congr (smallBaseEquiv l hl).toEquiv, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  omega

@[expose] def smallOutside (l : ℕ) (i j : ZMod (4 * l)) : Subgroup (Wreath (4 * l)) :=
  Subgroup.closure {Original.a (4 * l), Original.x2 (4 * l), element (4 * l) i j 1}

instance smallBase_normal (l : ℕ) : (smallBase l).Normal := by
  refine ⟨?_⟩
  intro g hg c
  obtain ⟨⟨a, b, e⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective g
  change element (4 * l) a b e ∈ smallBase l at hg
  rcases (element_mem_smallBase _ _ _ _).mp hg with ⟨rfl, hd⟩
  obtain ⟨⟨u, v, f⟩, rfl⟩ := (coordinateEquiv (4 * l)).symm.surjective c
  rcases swap_exponent_cases f with rfl | rfl
  · change element (4 * l) u v 0 * element (4 * l) a b 0 *
      (element (4 * l) u v 0)⁻¹ ∈ smallBase l
    rw [conjugate_base_by_base]
    exact hg
  · change element (4 * l) u v 1 * element (4 * l) a b 0 *
      (element (4 * l) u v 1)⁻¹ ∈ smallBase l
    rw [conjugate_base_by_swap, element_mem_smallBase]
    refine ⟨rfl, ?_⟩
    have hneg := half_difference_neg l (a - b) hd
    simpa only [neg_sub] using hneg

private def twoCosetSubgroup {G : Type*} [Group G] (D : Subgroup G) [D.Normal]
    (w : G) (hsquare : w ^ 2 ∈ D) : Subgroup G where
  carrier := {g | g ∈ D ∨ ∃ b ∈ D, g = b * w}
  one_mem' := Or.inl D.one_mem
  mul_mem' {g h} hg hh := by
    rcases hg with hg | ⟨a, ha, rfl⟩ <;> rcases hh with hh | ⟨b, hb, rfl⟩
    · exact Or.inl (D.mul_mem hg hh)
    · exact Or.inr ⟨g * b, D.mul_mem hg hb, (mul_assoc _ _ _).symm⟩
    · refine Or.inr ⟨a * (w * h * w⁻¹),
        D.mul_mem ha ((inferInstance : D.Normal).conj_mem h hh w), ?_⟩
      group
    · refine Or.inl ?_
      have hmem := D.mul_mem
        (D.mul_mem ha ((inferInstance : D.Normal).conj_mem b hb w)) hsquare
      convert hmem using 1
      group
  inv_mem' {g} hg := by
    rcases hg with hg | ⟨b, hb, rfl⟩
    · exact Or.inl (D.inv_mem hg)
    · refine Or.inr ⟨(w ^ 2)⁻¹ * (w * b⁻¹ * w⁻¹),
        D.mul_mem (D.inv_mem hsquare)
          ((inferInstance : D.Normal).conj_mem b⁻¹ (D.inv_mem hb) w), ?_⟩
      group

theorem smallBase_le_smallOutside (l : ℕ) (i j : ZMod (4 * l)) :
    smallBase l ≤ smallOutside l i j := by
  rw [smallBase_eq_generated, Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  rcases Set.mem_insert_iff.mp hg with rfl | h
  · simp
  · rw [Set.mem_singleton_iff.mp h]
    simp

theorem smallOutside_cosets (l : ℕ) (i j : ZMod (4 * l)) (g : Wreath (4 * l)) :
    g ∈ smallOutside l i j ↔ g ∈ smallBase l ∨
      ∃ b ∈ smallBase l, g = b * element (4 * l) i j 1 := by
  let D := smallBase l
  let w := element (4 * l) i j 1
  have hsquare : w ^ 2 ∈ D := by
    rw [element_swap_sq, element_mem_smallBase]
    simp
  let T := twoCosetSubgroup D w hsquare
  have hT : smallOutside l i j ≤ T := by
    rw [smallOutside, Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · apply Or.inl
      simp [D, Original.a_eq, element_mem_smallBase]
    · rcases Set.mem_insert_iff.mp hx with rfl | hx
      · apply Or.inl
        simp [D, Original.x2_eq, element_mem_smallBase,
          show 4 * l / 2 = 2 * l by omega]
      · rw [Set.mem_singleton_iff.mp hx]
        exact Or.inr ⟨1, D.one_mem, (one_mul w).symm⟩
  constructor
  · intro hg
    exact hT hg
  · rintro (hg | ⟨b, hb, rfl⟩)
    · exact smallBase_le_smallOutside l i j hg
    · exact (smallOutside l i j).mul_mem (smallBase_le_smallOutside l i j hb)
        (Subgroup.subset_closure (by simp))

theorem smallOutside_base_intersection (l : ℕ) (i j : ZMod (4 * l)) :
    smallOutside l i j ⊓ baseSubgroup (4 * l) = smallBase l := by
  apply le_antisymm
  · intro g hg
    rcases (smallOutside_cosets l i j g).mp hg.1 with h | ⟨b, hb, hgb⟩
    · exact h
    · obtain ⟨⟨a, c, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective b
      change element (4 * l) a c e = b at heq
      have he : e = 0 := ((element_mem_smallBase l a c e).mp (heq ▸ hb)).1
      subst e
      have hbase := hg.2
      change g ∈ baseSubgroup (4 * l) at hbase
      rw [hgb, ← heq, element_base_mul, element_mem_base] at hbase
      exact False.elim (one_ne_zero hbase)
  · exact le_inf (smallBase_le_smallOutside l i j) (smallBase_le_base l)

@[expose] def residueParity (l : ℕ) : ZMod (4 * l) →+* ZMod 2 :=
  ZMod.castHom (by omega) (ZMod 2)

theorem residueParity_odd_iff (l : ℕ) (hl : 0 < l) (c : ZMod (4 * l)) :
    residueParity l c = 1 ↔ Odd c.val := by
  let : NeZero (4 * l) := ⟨by omega⟩
  have hcast : residueParity l c = (c.val : ZMod 2) := by
    calc
      residueParity l c = residueParity l (c.val : ZMod (4 * l)) := by
        rw [ZMod.natCast_zmod_val]
      _ = (c.val : ZMod 2) := map_natCast _ _
  rw [hcast]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    apply Nat.odd_iff.mpr
    simpa only [ZMod.val_natCast, ZMod.val_one] using hv
  · intro h
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast, ZMod.val_one] using Nat.odd_iff.mp h

theorem smallBase_sum_parity (l : ℕ) (a b : ZMod (4 * l))
    (hg : element (4 * l) a b 0 ∈ smallBase l) : residueParity l (a + b) = 0 := by
  rcases ((element_mem_smallBase _ _ _ _).mp hg).2 with h | h
  · rw [sub_eq_zero.mp h, map_add]
    exact CharTwo.add_self_eq_zero _
  · have heq : a = b + (2 * l : ℕ) := by linear_combination h
    have hhalf : residueParity l (2 * l : ℕ) = 0 := by
      rw [map_natCast, Nat.cast_mul, Nat.cast_ofNat]
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
    rw [heq, map_add, map_add, hhalf, add_zero]
    exact CharTwo.add_self_eq_zero _

theorem smallOutside_odd_coset_sum (l : ℕ) (hl : 0 < l)
    (i j a b : ZMod (4 * l)) (hodd : Odd (i + j).val)
    (hb : element (4 * l) a b 0 ∈ smallBase l) :
    Odd ((a + i) + (b + j)).val := by
  apply (residueParity_odd_iff l hl _).mp
  have hbase := smallBase_sum_parity l a b hb
  have hsum := (residueParity_odd_iff l hl _).mpr hodd
  have heq : (a + i) + (b + j) = (a + b) + (i + j) := by abel
  rw [heq, map_add, hbase, zero_add, hsum]

theorem half_quarter_smul_eq_zero_iff (l : ℕ) (hl : 0 < l) (c : ZMod (4 * l)) :
    (2 * l) • c = 0 ↔ Even c.val := by
  let : NeZero (4 * l) := ⟨by omega⟩
  have heq : (2 * l) • c = ((2 * l * c.val : ℕ) : ZMod (4 * l)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  have hdiv (r : ℕ) : 4 * l ∣ (2 * l) * r ↔ 2 ∣ r := by
    rw [show 4 * l = (2 * l) * 2 by omega,
      Nat.mul_dvd_mul_iff_left (by omega : 0 < 2 * l)]
  rw [heq, ZMod.natCast_eq_zero_iff, hdiv, even_iff_two_dvd]

theorem element_swap_pow_atQuarter (l : ℕ) (a b : ZMod (4 * l)) :
    element (4 * l) a b 1 ^ (4 * l) =
      element (4 * l) ((2 * l) • (a + b)) ((2 * l) • (a + b)) 0 := by
  conv_lhs => arg 2; rw [show 4 * l = 2 * (2 * l) by omega]
  rw [pow_mul, element_swap_sq, element_base_pow]

theorem smallOutside_odd_base_iff_pow (l : ℕ) (hl : 0 < l)
    (i j : ZMod (4 * l)) (hodd : Odd (i + j).val) (g : smallOutside l i j) :
    g ∈ (smallBase l).subgroupOf (smallOutside l i j) ↔ g ^ (4 * l) = 1 := by
  constructor
  · intro hg
    apply Subtype.ext
    have hb : g.val ∈ baseSubgroup (4 * l) := smallBase_le_base l hg
    obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective g.val
    change element (4 * l) a b e = g.val at heq
    have he : e = 0 := (element_mem_base _ _ _ _).mp (heq ▸ hb)
    change g.val ^ (4 * l) = 1
    rw [← heq, he]
    exact element_base_pow_modulus _ _ _
  · intro hpow
    rcases (smallOutside_cosets l i j g.val).mp g.property with hg | ⟨b, hb, hgb⟩
    · exact hg
    · obtain ⟨⟨a, c, e⟩, heq⟩ := (coordinateEquiv (4 * l)).symm.surjective b
      change element (4 * l) a c e = b at heq
      have he : e = 0 := ((element_mem_smallBase l a c e).mp (heq ▸ hb)).1
      subst e
      have hsum := smallOutside_odd_coset_sum l hl i j a c hodd (heq ▸ hb)
      have hambient := congrArg Subtype.val hpow
      change g.val ^ (4 * l) = 1 at hambient
      rw [hgb, ← heq, element_base_mul, element_swap_pow_atQuarter,
        element_base_eq_one_iff, half_quarter_smul_eq_zero_iff l hl] at hambient
      exact False.elim (Nat.not_even_iff_odd.mpr hsum hambient.1)

theorem smallOutside_odd_base_characteristic (l : ℕ) (hl : 0 < l)
    (i j : ZMod (4 * l)) (hodd : Odd (i + j).val) :
    ((smallBase l).subgroupOf (smallOutside l i j)).Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro α g hg
  apply (smallOutside_odd_base_iff_pow l hl i j hodd (α g)).mpr
  rw [← map_pow, (smallOutside_odd_base_iff_pow l hl i j hodd g).mp hg, map_one]

@[expose] def smallOutsideSwap (l : ℕ) (i j : ZMod (4 * l)) :
    smallOutside l i j →* Multiplicative (ZMod 2) :=
  (RegularWreathProduct.rightHom : Wreath (4 * l) →* Multiplicative (ZMod 2)).comp
    (smallOutside l i j).subtype

theorem smallOutsideSwap_surjective (l : ℕ) (i j : ZMod (4 * l)) :
    Function.Surjective (smallOutsideSwap l i j) := by
  intro c
  rcases swap_coordinate_cases c with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨⟨element (4 * l) i j 1, Subgroup.subset_closure (by simp)⟩, rfl⟩

theorem smallOutsideSwap_ker (l : ℕ) (i j : ZMod (4 * l)) :
    (smallOutsideSwap l i j).ker = (smallBase l).subgroupOf (smallOutside l i j) := by
  ext g
  change g.val ∈ baseSubgroup (4 * l) ↔ g.val ∈ smallBase l
  constructor
  · intro hg
    exact (smallOutside_base_intersection l i j) ▸ ⟨g.property, hg⟩
  · intro hg
    exact smallBase_le_base l hg

instance smallOutsideBase_normal (l : ℕ) (i j : ZMod (4 * l)) :
    ((smallBase l).subgroupOf (smallOutside l i j)).Normal := by
  rw [← smallOutsideSwap_ker]
  infer_instance

@[expose] def smallOutsideBaseQuotientEquiv (l : ℕ) (i j : ZMod (4 * l)) :
    smallOutside l i j ⧸ (smallBase l).subgroupOf (smallOutside l i j) ≃*
      Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq (smallOutsideSwap_ker l i j).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (smallOutsideSwap l i j)
      (smallOutsideSwap_surjective l i j))

theorem smallOutside_odd_automorphism_atQuarter (n l : ℕ) (hn : 2 ≤ n)
    (hl : 0 < l) (hm : 4 * l = 2 ^ n)
    (i j : ZMod (4 * l)) (hodd : Odd (i + j).val) :
    IsPGroup 2 (MulAut (smallOutside l i j)) := by
  let : NeZero (4 * l) := ⟨by omega⟩
  let D := (smallBase l).subgroupOf (smallOutside l i j)
  let : D.Characteristic := smallOutside_odd_base_characteristic l hl i j hodd
  have ebase : D ≃* Multiplicative (ZMod (4 * l)) × Multiplicative (ZMod 2) :=
    (Subgroup.subgroupOfEquivOfLe (smallBase_le_smallOutside l i j)).trans
      (smallBaseEquiv l hl).symm
  have eheight : Multiplicative (ZMod (4 * l)) × Multiplicative (ZMod 2) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2) :=
    MulEquiv.prodCongr (ZMod.ringEquivCongr hm).toAddEquiv.toMultiplicative (MulEquiv.refl _)
  have hD : IsPGroup 2 D := by
    apply IsPGroup.of_card (n := n + 1)
    rw [Nat.card_congr ebase.toEquiv, Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hm, pow_succ, Nat.mul_comm]
  have hAutD : IsPGroup 2 (MulAut D) :=
    cyclicTimesTwoAut_isPGroup_of_equiv n hn (ebase.trans eheight)
  have equot : smallOutside l i j ⧸ D ≃* Multiplicative (ZMod 2) :=
    smallOutsideBaseQuotientEquiv l i j
  have hquot : Nat.card (smallOutside l i j ⧸ D) = 2 := by
    rw [Nat.card_congr equot.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  let : IsCyclic (smallOutside l i j ⧸ D) := equot.isCyclic.mpr inferInstance
  have hAutQuot : IsPGroup 2 (MulAut (smallOutside l i j ⧸ D)) := by
    apply IsPGroup.of_card (n := 0)
    rw [IsCyclic.card_mulAut, hquot, Nat.totient_two, pow_zero]
  exact CFSG.characteristic_automorphism_isPGroup 2 Nat.prime_two D hD hAutD hAutQuot

theorem smallOutside_even_conjugate_atQuarter (l : ℕ) (hl : 0 < l)
    (i j : ZMod (4 * l)) (heven : Even (i + j).val) :
    ∃ g : Wreath (4 * l), (smallOutside l i j).map (MulAut.conj g).toMonoidHom =
      Original.V (4 * l) := by
  let : NeZero (4 * l) := ⟨by omega⟩
  obtain ⟨q, hq⟩ := heven
  have hsum : i + j = (q : ZMod (4 * l)) + q := by
    rw [← ZMod.natCast_zmod_val (i + j), hq, Nat.cast_add]
  let c : ZMod (4 * l) := (q : ZMod (4 * l)) - i
  let g : Wreath (4 * l) := element (4 * l) c 0 0
  let f := (MulAut.conj g).toMonoidHom
  have ha : f (Original.a (4 * l)) = Original.a (4 * l) := by
    rw [Original.a_eq]
    change g * element (4 * l) 1 1 0 * g⁻¹ = element (4 * l) 1 1 0
    exact conjugate_base_by_base _ _ _ _ _
  have hx : f (Original.x2 (4 * l)) = Original.x2 (4 * l) := by
    rw [Original.x2_eq]
    change g * element (4 * l) _ 0 0 * g⁻¹ = element (4 * l) _ 0 0
    exact conjugate_base_by_base _ _ _ _ _
  have hw : f (element (4 * l) i j 1) = element (4 * l) q q 1 := by
    change g * element (4 * l) i j 1 * g⁻¹ = element (4 * l) q q 1
    rw [conjugate_swap_by_base]
    rw [element_eq_iff]
    refine ⟨?_, ?_, rfl⟩
    · dsimp [c]
      abel
    · dsimp [c]
      linear_combination hsum
  have himage : f '' {Original.a (4 * l), Original.x2 (4 * l), element (4 * l) i j 1} =
      {Original.a (4 * l), Original.x2 (4 * l), element (4 * l) q q 1} := by
    simp only [Set.image_insert_eq, Set.image_singleton, ha, hx, hw]
  refine ⟨g, ?_⟩
  change (smallOutside l i j).map f = Original.V (4 * l)
  rw [smallOutside, MonoidHom.map_closure, himage]
  let T := Subgroup.closure
    {Original.a (4 * l), Original.x2 (4 * l), element (4 * l) q q 1}
  change T = Original.V (4 * l)
  have hdiagT (b : ZMod (4 * l)) : element (4 * l) b b 0 ∈ T := by
    have hdiag : element (4 * l) b b 0 ∈ (diagonalHom (4 * l)).range :=
      ⟨Multiplicative.ofAdd b, rfl⟩
    rw [diagonal_range_eq_zpowers, ← Original.a_eq] at hdiag
    exact Subgroup.zpowers_le_of_mem (Subgroup.subset_closure (by simp)) hdiag
  have hdiagV (b : ZMod (4 * l)) : element (4 * l) b b 0 ∈ Original.V (4 * l) := by
    rw [Original.V_atQuarter]
    simp
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hxmem
    rcases Set.mem_insert_iff.mp hxmem with rfl | hxmem
    · exact Subgroup.subset_closure (by simp)
    · rcases Set.mem_insert_iff.mp hxmem with rfl | hxmem
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff.mp hxmem]
        have hz : Original.z (4 * l) ∈ Original.V (4 * l) :=
          Subgroup.subset_closure (by simp)
        have hp := (Original.V (4 * l)).mul_mem (hdiagV q) hz
        change element (4 * l) q q 1 ∈ Original.V (4 * l)
        simpa only [Original.z, element_base_mul, add_zero] using hp
  · rw [Original.V, Subgroup.closure_le]
    intro x hxmem
    rcases Set.mem_insert_iff.mp hxmem with rfl | hxmem
    · exact Subgroup.subset_closure (by simp)
    · rcases Set.mem_insert_iff.mp hxmem with rfl | hxmem
      · exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff.mp hxmem]
        have hwT : element (4 * l) q q 1 ∈ T := Subgroup.subset_closure (by simp)
        have hp := T.mul_mem (hdiagT (-q)) hwT
        change Original.z (4 * l) ∈ T
        simpa only [element_base_mul, neg_add_cancel, Original.z] using hp

theorem smallOutside_odd_automorphism (n : ℕ) (hn : 2 ≤ n)
    (i j : ZMod (2 ^ n)) (hodd : Odd (i + j).val) :
    IsPGroup 2 (MulAut
      (Subgroup.closure {Original.a (2 ^ n), Original.x2 (2 ^ n), element (2 ^ n) i j 1})) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    rw [hheight, pow_add]
    norm_num
    ring
  revert i j
  rw [hm]
  intro i j hodd
  exact smallOutside_odd_automorphism_atQuarter n (2 ^ (n - 2)) hn
    (pow_pos (by decide) _) hm.symm i j hodd

theorem smallOutside_even_conjugate (n : ℕ) (hn : 2 ≤ n)
    (i j : ZMod (2 ^ n)) (heven : Even (i + j).val) :
    ∃ g : Wreath (2 ^ n),
      (Subgroup.closure {Original.a (2 ^ n), Original.x2 (2 ^ n), element (2 ^ n) i j 1}).map
        (MulAut.conj g).toMonoidHom = Original.V (2 ^ n) := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    rw [hheight, pow_add]
    norm_num
    ring
  revert i j
  rw [hm]
  intro i j heven
  exact smallOutside_even_conjugate_atQuarter (2 ^ (n - 2)) (pow_pos (by decide) _) i j heven

end CFSG.Wreathed
