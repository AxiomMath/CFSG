module

public import CFSG.CharacterTheory.Wreathed.CentricSubgroups
public import CFSG.CharacterTheory.Wreathed.CyclicTwoAutomorphism
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalizerComplement

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem abelian_centric_card (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (i j : ZMod m) (hw : element m i j 1 ∈ P) : Nat.card P = 2 * m := by
  let f : P →* Multiplicative (ZMod 2) := RegularWreathProduct.rightHom.comp P.subtype
  have hsurj : Function.Surjective f := by
    intro e
    rcases swap_coordinate_cases e with rfl | rfl
    · exact ⟨1, by simp [f]⟩
    · exact ⟨⟨element m i j 1, hw⟩, rfl⟩
  have hbase := abelian_centric_base_intersection m hm P hP habelian _ hw (by simp)
  have hker : f.ker = (Subgroup.center (Wreath m)).subgroupOf P := by
    ext g
    change g.val ∈ baseSubgroup m ↔ g.val ∈ Subgroup.center (Wreath m)
    constructor
    · intro hg
      rw [← hbase]
      exact ⟨g.property, hg⟩
    · intro hg
      have hi : g.val ∈ P ⊓ baseSubgroup m := by rw [hbase]; exact hg
      exact hi.2
  have hcardker : Nat.card f.ker = m := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (center_le_of_centric P hP)).toEquiv, card_center m hm]
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hcardker, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hcard
  simpa only [Nat.mul_comm] using hcard.symm

theorem abelian_centric_cyclic_of_odd (n : ℕ) (hn : 1 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (i j : ZMod (2 ^ n)) (hw : element (2 ^ n) i j 1 ∈ P)
    (hodd : Odd (i + j).val) : IsCyclic P ∧ Nat.card P = 2 * 2 ^ n := by
  have hm : 1 < 2 ^ n := by
    exact one_lt_pow₀ (by decide) (by omega)
  have hcard := abelian_centric_card (2 ^ n) hm P hP habelian i j hw
  have horder : orderOf (element (2 ^ n) i j 1) = 2 * 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact (element_swap_maximal_order_iff k i j).mpr hodd
  have heq : Subgroup.zpowers (element (2 ^ n) i j 1) = P := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hw)
    rw [Nat.card_zpowers, horder, hcard]
  refine ⟨?_, hcard⟩
  rw [← heq]
  infer_instance

@[expose] def diagonalInvolutionProductHom (m : ℕ) (b : ZMod m) :
    Multiplicative (ZMod m) × Multiplicative (ZMod 2) →* Wreath m where
  toFun c := if Multiplicative.toAdd c.2 = 0 then
    element m (Multiplicative.toAdd c.1) (Multiplicative.toAdd c.1) 0 else
    element m (Multiplicative.toAdd c.1 + b) (Multiplicative.toAdd c.1 - b) 1
  map_one' := by simp
  map_mul' c d := by
    rcases c with ⟨c, e⟩
    rcases d with ⟨d, f⟩
    rcases swap_coordinate_cases e with rfl | rfl <;>
      rcases swap_coordinate_cases f with rfl | rfl <;>
      simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul,
        toAdd_ofAdd, add_zero, zero_add,
        show (1 + 1 : ZMod 2) = 0 by decide, ite_true,
        one_ne_zero, ite_false, element_base_mul, element_swap_mul]
    all_goals
      apply (element_eq_iff _ _ _ _ _ _ _).mpr
      refine ⟨?_, ?_, ?_⟩ <;> abel

theorem diagonalInvolutionProductHom_injective (m : ℕ) (b : ZMod m) :
    Function.Injective (diagonalInvolutionProductHom m b) := by
  rintro ⟨c, e⟩ ⟨d, f⟩ h
  rcases swap_coordinate_cases e with rfl | rfl <;>
    rcases swap_coordinate_cases f with rfl | rfl <;>
    simp only [diagonalInvolutionProductHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, ite_true, one_ne_zero, ite_false,
      element_eq_iff] at h
  · exact Prod.ext (Multiplicative.toAdd.injective h.1) rfl
  · exact False.elim (zero_ne_one h.2.2)
  · exact False.elim h.2.2
  · exact Prod.ext (Multiplicative.toAdd.injective (add_right_cancel h.1)) rfl

theorem abelian_centric_involution_product (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (b : ZMod m) (hw : element m b (-b) 1 ∈ P) :
    Nonempty (P ≃* Multiplicative (ZMod m) × Multiplicative (ZMod 2)) := by
  have hbase := abelian_centric_base_intersection m hm P hP habelian _ hw (by simp)
  have hdiag (c : ZMod m) : element m c c 0 ∈ P :=
    center_le_of_centric P hP ((element_mem_center_iff m hm _ _ _).mpr ⟨rfl, rfl⟩)
  have hmaps (c : Multiplicative (ZMod m) × Multiplicative (ZMod 2)) :
      diagonalInvolutionProductHom m b c ∈ P := by
    rcases c with ⟨c, e⟩
    rcases swap_coordinate_cases e with rfl | rfl
    · exact hdiag _
    · have h := P.mul_mem (hdiag (Multiplicative.toAdd c)) hw
      change element m (Multiplicative.toAdd c + b) (Multiplicative.toAdd c - b) 1 ∈ P
      simpa only [element_base_mul, sub_eq_add_neg] using h
  let f : Multiplicative (ZMod m) × Multiplicative (ZMod 2) →* P :=
    (diagonalInvolutionProductHom m b).codRestrict P hmaps
  have hinj : Function.Injective f := by
    intro c d h
    exact diagonalInvolutionProductHom_injective m b (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro g
    rcases (subgroup_base_cosets m P b (-b) hw g.val).mp g.property with hg | ⟨c, hc, hcg⟩
    · have hz : g.val ∈ Subgroup.center (Wreath m) := hbase ▸ hg
      rw [center_eq_diagonal_range m hm] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨(a, Multiplicative.ofAdd 0), Subtype.ext ha⟩
    · have hz : c ∈ Subgroup.center (Wreath m) := hbase ▸ hc
      rw [center_eq_diagonal_range m hm] at hz
      obtain ⟨a, rfl⟩ := hz
      refine ⟨(a, Multiplicative.ofAdd 1), ?_⟩
      apply Subtype.ext
      rw [hcg]
      change element m (Multiplicative.toAdd a + b) (Multiplicative.toAdd a - b) 1 =
        element m (Multiplicative.toAdd a) (Multiplicative.toAdd a) 0 * element m b (-b) 1
      rw [element_base_mul, sub_eq_add_neg]
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm⟩

theorem abelian_centric_product_of_even (m : ℕ) (hm : 1 < m)
    (P : Subgroup (Wreath m)) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (i j : ZMod m) (hw : element m i j 1 ∈ P) (heven : Even (i + j).val) :
    Nonempty (P ≃* Multiplicative (ZMod m) × Multiplicative (ZMod 2)) := by
  let : NeZero m := ⟨by omega⟩
  obtain ⟨q, hq⟩ := heven
  have hsum : i + j = (q : ZMod m) + q := by
    rw [← ZMod.natCast_zmod_val (i + j), hq, Nat.cast_add]
  have hdiag : element m (-(q : ZMod m)) (-q) 0 ∈ P :=
    center_le_of_centric P hP ((element_mem_center_iff m hm _ _ _).mpr ⟨rfl, rfl⟩)
  have hnew := P.mul_mem hdiag hw
  rw [element_base_mul] at hnew
  have heq : -(q : ZMod m) + j = -(-(q : ZMod m) + i) := by
    linear_combination hsum
  rw [heq] at hnew
  exact abelian_centric_involution_product m hm P hP habelian _ hnew

theorem abelian_centric_outside_structure (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (hout : ¬ P ≤ baseSubgroup (2 ^ n)) :
    (IsCyclic P ∧ Nat.card P = 2 * 2 ^ n) ∨
      Nonempty (P ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)) := by
  obtain ⟨i, j, hw⟩ := subgroup_outside_exists (2 ^ n) P hout
  rcases Nat.even_or_odd (i + j).val with heven | hodd
  · exact Or.inr (abelian_centric_product_of_even _
      (one_lt_pow₀ (by decide) (by omega)) P hP habelian i j hw heven)
  · exact Or.inl (abelian_centric_cyclic_of_odd n (by omega) P hP habelian i j hw hodd)

theorem abelian_centric_outside_automorphism_isPGroup (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : IsCentric P) (habelian : IsMulCommutative P)
    (hout : ¬ P ≤ baseSubgroup (2 ^ n)) : IsPGroup 2 (MulAut P) := by
  rcases abelian_centric_outside_structure n hn P hP habelian hout with hcyclic | hproduct
  · obtain ⟨hcyclic, hcard⟩ := hcyclic
    let : IsCyclic P := hcyclic
    apply CFSG.TwoRankLowerBound.Helpers.cyclic_two_group_automorphisms_isPGroup P
    apply IsPGroup.of_card (n := n + 1)
    rw [hcard, pow_succ, Nat.mul_comm]
  · obtain ⟨e⟩ := hproduct
    exact cyclicTimesTwoAut_isPGroup_of_equiv n hn e

end CFSG.Wreathed
