module

public import CFSG.CharacterTheory.Wreathed.CentricDihedralAutomorphism
public import CFSG.CharacterTheory.Wreathed.CentricAbelian
public import CFSG.CharacterTheory.Wreathed.CentricOddSquare
public import CFSG.CharacterTheory.Wreathed.CentricSmallQuotient

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem centric_odd_automorphism_classification (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (hP : IsCentric P)
    (hautomorphism : ¬ IsPGroup 2 (MulAut P)) :
    P = Original.U (2 ^ n) ∨
      ∃ g : Wreath (2 ^ n), P.map (MulAut.conj g).toMonoidHom = Original.V (2 ^ n) := by
  by_cases hbase : P ≤ baseSubgroup (2 ^ n)
  · exact Or.inl ((centric_eq_base_of_le P hP hbase).trans (Original.U_eq _).symm)
  · by_cases hab : IsMulCommutative P
    · exact False.elim (hautomorphism
        (abelian_centric_outside_automorphism_isPGroup n hn P hP hab hbase))
    · have hnonabelian : ∃ u v : P, u * v ≠ v * u := by
        by_contra h
        apply hab
        rw [isMulCommutative_iff]
        intro u v
        by_contra hne
        exact h ⟨u, v, hne⟩
      have hcenter := center_le_of_centric P hP
      obtain ⟨equiv⟩ := nonabelian_odd_automorphism_center_quotient_dihedral_two
        n hn P hnonabelian hcenter hautomorphism
      obtain ⟨i, j, hgenerated⟩ := nonabelian_small_center_quotient_generators
        n (by omega) P hnonabelian hcenter equiv
      rcases Nat.even_or_odd (i + j).val with heven | hodd
      · apply Or.inr
        rw [hgenerated]
        exact smallOutside_even_conjugate n hn i j heven
      · exact False.elim (hautomorphism
          (hgenerated ▸ smallOutside_odd_automorphism n hn i j hodd))

theorem original_v_copy_conjugate (n : ℕ) (hn : 2 ≤ n)
    (P : Subgroup (Wreath (2 ^ n))) (equiv : P ≃* Original.V (2 ^ n)) :
    ∃ g : Wreath (2 ^ n), P.map (MulAut.conj g).toMonoidHom = Original.V (2 ^ n) := by
  rcases centric_odd_automorphism_classification n hn P
    (original_v_copy_isCentric n hn P equiv)
    (original_v_copy_automorphism_not_isPGroup n hn P equiv) with hbase | hconjugate
  · exact False.elim (original_v_copy_ne_base n hn P equiv
      (hbase.trans (Original.U_eq _)))
  · exact hconjugate

structure CentricClassification (n : ℕ) : Prop where
  classification : ∀ P : Subgroup (Wreath (2 ^ n)), IsCentric P →
    ¬ IsPGroup 2 (MulAut P) →
    P = Original.U (2 ^ n) ∨
      ∃ g : Wreath (2 ^ n), P.map (MulAut.conj g).toMonoidHom = Original.V (2 ^ n)
  centric : IsCentric (Original.V (2 ^ n))
  order_three : ∃ α : MulAut (Original.V (2 ^ n)), orderOf α = 3
  copies_conjugate : ∀ P : Subgroup (Wreath (2 ^ n)),
    Nonempty (P ≃* Original.V (2 ^ n)) →
      ∃ g : Wreath (2 ^ n), P.map (MulAut.conj g).toMonoidHom = Original.V (2 ^ n)
  copies_center : ∀ P : Subgroup (Wreath (2 ^ n)),
    Nonempty (P ≃* Original.V (2 ^ n)) →
      (Subgroup.center P).map P.subtype = Original.Z (2 ^ n)
  copies_normalizer : ∀ P : Subgroup (Wreath (2 ^ n)),
    Nonempty (P ≃* Original.V (2 ^ n)) →
      Nat.card (Subgroup.normalizer (P : Set (Wreath (2 ^ n)))) = 8 * 2 ^ n

theorem wreath_centric_odd_automorphism_subgroups (n : ℕ) (hn : 2 ≤ n) :
    CentricClassification n := by
  refine ⟨centric_odd_automorphism_classification n hn,
    original_v_isCentric n hn, ?_, ?_, ?_, ?_⟩
  · obtain ⟨α, hα, _⟩ := (wreath_center_involution_and_quaternion_coordinates n hn).cycle
    exact ⟨α, hα⟩
  · intro P ⟨equiv⟩
    exact original_v_copy_conjugate n hn P equiv
  · intro P ⟨equiv⟩
    exact (original_v_copy_center n hn P equiv).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).center
  · intro P ⟨equiv⟩
    obtain ⟨g, hg⟩ := original_v_copy_conjugate n hn P equiv
    exact normalizer_card_of_original_v_conjugate n hn P g hg

end CFSG.Wreathed
