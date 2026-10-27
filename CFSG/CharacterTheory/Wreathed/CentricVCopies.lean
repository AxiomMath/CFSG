module

public import CFSG.CharacterTheory.Wreathed.CentricSubgroups
public import CFSG.CharacterTheory.Wreathed.OriginalStructure

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem wreath_isPGroup (n : ℕ) : IsPGroup 2 (Wreath (2 ^ n)) := by
  apply IsPGroup.of_card (n := 2 * n + 1)
  rw [card_wreath, pow_add, pow_one,
    show 2 * n = n * 2 by omega, pow_mul]
  ring

theorem original_v_is_nonabelian (n : ℕ) (hn : 2 ≤ n) :
    ∃ u v : Original.V (2 ^ n), u * v ≠ v * u := by
  have hm : 2 ^ n = 4 * 2 ^ (n - 2) := by
    have hheight : n = (n - 2) + 2 := by omega
    calc
      2 ^ n = 2 ^ ((n - 2) + 2) := congrArg (fun j : ℕ => 2 ^ j) hheight
      _ = 4 * 2 ^ (n - 2) := by rw [pow_add]; norm_num; ring
  rw [hm, Original.V_atQuarter]
  exact v_is_nonabelian _ (pow_pos (by decide) _)

theorem original_v_isCentric (n : ℕ) (hn : 2 ≤ n) : IsCentric (Original.V (2 ^ n)) := by
  have h := wreath_center_involution_and_quaternion_coordinates n hn
  unfold IsCentric
  exact h.central_product_centralizer.trans h.central_product_center.symm

theorem original_v_center_card (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (Subgroup.center (Original.V (2 ^ n))) = 2 ^ n := by
  have h := wreath_center_involution_and_quaternion_coordinates n hn
  have hm : 1 < 2 ^ n := by
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at he
    omega
  rw [← Subgroup.card_map_of_injective (Original.V (2 ^ n)).subtype_injective,
    h.central_product_center, ← h.center, card_center _ hm]

theorem original_v_automorphism_not_isPGroup (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsPGroup 2 (MulAut (Original.V (2 ^ n))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨automorphism, horder, _⟩ :=
    (wreath_center_involution_and_quaternion_coordinates n hn).cycle
  intro htwo
  have hne : automorphism ≠ 1 := by
    intro h
    rw [h, orderOf_one] at horder
    omega
  have hdiv := htwo.dvd_orderOf hne
  rw [horder] at hdiv
  norm_num at hdiv

theorem original_v_copy_nonabelian (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) :
    ∃ u v : P, u * v ≠ v * u := by
  obtain ⟨u, v, hne⟩ := original_v_is_nonabelian n hn
  refine ⟨equiv.symm u, equiv.symm v, ?_⟩
  intro h
  apply hne
  have heq := congrArg equiv h
  simpa only [map_mul, equiv.apply_symm_apply] using heq

theorem original_v_copy_center (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) :
    (Subgroup.center P).map P.subtype = Subgroup.center (Wreath (2 ^ n)) := by
  have hm : 1 < 2 ^ n := by
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at he
    omega
  have hcard : Nat.card (Subgroup.center P) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.centerCongr equiv).toEquiv, original_v_center_card n hn]
  have hle : (Subgroup.center P).map P.subtype ≤ Subgroup.center (Wreath (2 ^ n)) := by
    rw [nonabelian_subgroup_center _ hm P (original_v_copy_nonabelian n hn P equiv)]
    exact inf_le_right
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective P.subtype_injective, hcard, card_center _ hm]

theorem original_v_copy_isCentric (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) : IsCentric P := by
  have hm : 1 < 2 ^ n := by
    have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at he
    omega
  unfold IsCentric
  rw [nonabelian_subgroup_centralizer_eq_center _ hm P
    (original_v_copy_nonabelian n hn P equiv), original_v_copy_center n hn P equiv]

theorem original_v_copy_automorphism_not_isPGroup (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) :
    ¬ IsPGroup 2 (MulAut P) := by
  intro htwo
  exact original_v_automorphism_not_isPGroup n hn (htwo.of_equiv (MulAut.congr equiv))

theorem original_v_copy_ne_base (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) :
    P ≠ baseSubgroup (2 ^ n) := by
  intro heq
  obtain ⟨u, v, hne⟩ := original_v_copy_nonabelian n hn P equiv
  apply hne
  exact isMulCommutative_iff.mp (heq ▸ base_is_abelian (2 ^ n)) u v

theorem normalizer_card_of_original_v_conjugate (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (g : Wreath (2 ^ n))
    (hconjugate : P.map (MulAut.conj g).toMonoidHom = Original.V (2 ^ n)) :
    Nat.card (Subgroup.normalizer (P : Set (Wreath (2 ^ n)))) = 8 * 2 ^ n := by
  have hmap := P.map_normalizer_eq_of_bijective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective
  rw [hconjugate] at hmap
  rw [← Subgroup.card_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective, hmap]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).normalizer_card

end CFSG.Wreathed
