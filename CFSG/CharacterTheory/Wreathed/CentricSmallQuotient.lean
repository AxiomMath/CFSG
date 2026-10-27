module

public import CFSG.CharacterTheory.Wreathed.CentricSubgroups

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem nonabelian_not_le_base (m : ℕ) (P : Subgroup (Wreath m))
    (hP : ∃ u v : P, u * v ≠ v * u) : ¬ P ≤ baseSubgroup m := by
  intro hle
  obtain ⟨u, v, huv⟩ := hP
  apply huv
  apply Subtype.ext
  exact congrArg (fun x : baseSubgroup m => (x : Wreath m))
    (isMulCommutative_iff.mp (base_is_abelian m)
      (⟨u.val, hle u.property⟩ : baseSubgroup m) ⟨v.val, hle v.property⟩)

theorem noncentral_base_exists (m : ℕ)
    (P : Subgroup (Wreath m)) (hP : ∃ u v : P, u * v ≠ v * u)
    (i j : ZMod m) (hw : element m i j 1 ∈ P) :
    ∃ b ∈ P ⊓ baseSubgroup m, b ∉ Subgroup.center (Wreath m) := by
  by_contra! hnone
  have hcommute (p : P) : Commute p.val (element m i j 1) := by
    rcases (subgroup_base_cosets m P i j hw p.val).mp p.property with hb | ⟨b, hb, heq⟩
    · exact (Subgroup.mem_center_iff.mp (hnone _ hb) _).symm
    · rw [heq]
      change b * element m i j 1 * element m i j 1 =
        element m i j 1 * (b * element m i j 1)
      calc
        b * element m i j 1 * element m i j 1 =
            (element m i j 1 * b) * element m i j 1 := by
              rw [Subgroup.mem_center_iff.mp (hnone _ hb)]
        _ = element m i j 1 * (b * element m i j 1) := mul_assoc _ _ _
  obtain ⟨u, v, huv⟩ := hP
  apply huv
  apply Subtype.ext
  exact (outside_centralizer_is_abelian m i j u.val v.val (hcommute u) (hcommute v)).eq

theorem center_quotient_dihedral_two_square (m : ℕ) (P : Subgroup (Wreath m))
    (equiv : P ⧸ Subgroup.center P ≃* DihedralGroup 2) (p : P) :
    p ^ 2 ∈ Subgroup.center P := by
  apply (QuotientGroup.eq_one_iff _).mp
  apply equiv.injective
  rw [map_one]
  change equiv ((QuotientGroup.mk' (Subgroup.center P)) (p ^ 2)) = 1
  rw [map_pow, map_pow, pow_two]
  exact IsKleinFour.mul_self _

theorem base_difference_of_center_quotient_dihedral_two (k : ℕ)
    (P : Subgroup (Wreath (2 ^ (k + 1))))
    (hP : ∃ u v : P, u * v ≠ v * u)
    (equiv : P ⧸ Subgroup.center P ≃* DihedralGroup 2)
    (c d : ZMod (2 ^ (k + 1))) (hcd : element (2 ^ (k + 1)) c d 0 ∈ P) :
    c - d = 0 ∨ c - d = (2 ^ k : ℕ) := by
  have hm : 1 < 2 ^ (k + 1) := by
    rw [pow_succ]
    have hp := pow_pos (by decide : 0 < (2 : ℕ)) k
    omega
  have hsquare := center_quotient_dihedral_two_square _ P equiv ⟨_, hcd⟩
  have hmap : element (2 ^ (k + 1)) c d 0 ^ 2 ∈
      (Subgroup.center P).map P.subtype := ⟨⟨_, hcd⟩ ^ 2, hsquare, rfl⟩
  rw [nonabelian_subgroup_center _ hm P hP] at hmap
  have hz := hmap.2
  change element (2 ^ (k + 1)) c d 0 ^ 2 ∈ Subgroup.center _ at hz
  rw [element_base_pow, element_mem_center_iff _ hm] at hz
  apply (two_smul_eq_zero_iff k (c - d)).mp
  simpa only [smul_sub, sub_eq_zero] using hz.2

theorem nonabelian_center_quotient_dihedral_two_generated (k : ℕ)
    (P : Subgroup (Wreath (2 ^ (k + 1))))
    (hP : ∃ u v : P, u * v ≠ v * u)
    (hcenter : Subgroup.center (Wreath (2 ^ (k + 1))) ≤ P)
    (equiv : P ⧸ Subgroup.center P ≃* DihedralGroup 2)
    (i j : ZMod (2 ^ (k + 1))) (hw : element (2 ^ (k + 1)) i j 1 ∈ P) :
    P = Subgroup.closure {Original.a (2 ^ (k + 1)), Original.x2 (2 ^ (k + 1)),
      element (2 ^ (k + 1)) i j 1} := by
  let m := 2 ^ (k + 1)
  have hm : 1 < m := by
    dsimp [m]
    rw [pow_succ]
    have hp := pow_pos (by decide : 0 < (2 : ℕ)) k
    omega
  have hhalf : m / 2 = 2 ^ k := by
    dsimp [m]
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < (2 : ℕ))]
  have hdiagonal (d : ZMod m) : element m d d 0 ∈ P :=
    hcenter ((element_mem_center_iff m hm d d 0).mpr ⟨rfl, rfl⟩)
  have ha : Original.a m ∈ P := by simpa only [Original.a_eq] using hdiagonal 1
  have hx2 : Original.x2 m ∈ P := by
    obtain ⟨b, hb, hnoncentral⟩ := noncentral_base_exists m P hP i j hw
    obtain ⟨⟨c, d, e⟩, hcoord⟩ := (coordinateEquiv m).symm.surjective b
    change element m c d e = b at hcoord
    have he : e = 0 := by
      have hbase := hb.2
      change b ∈ baseSubgroup m at hbase
      rwa [← hcoord, element_mem_base] at hbase
    subst e
    have hcd : element m c d 0 ∈ P := hcoord ▸ hb.1
    have hdiff := base_difference_of_center_quotient_dihedral_two k P hP equiv c d hcd
    have hne : c - d ≠ 0 := by
      intro h
      apply hnoncentral
      rw [← hcoord, element_mem_center_iff m hm]
      exact ⟨rfl, sub_eq_zero.mp h⟩
    have hhalfDiff := hdiff.resolve_left hne
    have hmul := P.mul_mem hcd (hdiagonal (-d))
    rw [element_base_mul, add_neg_cancel] at hmul
    rw [Original.x2_eq, hhalf]
    simpa only [← sub_eq_add_neg, hhalfDiff] using hmul
  let H : Subgroup (Wreath m) :=
    Subgroup.closure {Original.a m, Original.x2 m, element m i j 1}
  have haH : Original.a m ∈ H := Subgroup.subset_closure (by simp)
  have hx2H : Original.x2 m ∈ H := Subgroup.subset_closure (by simp)
  have hwH : element m i j 1 ∈ H := Subgroup.subset_closure (by simp)
  have hcenterH : Subgroup.center (Wreath m) ≤ H := by
    rw [center_eq_zpowers m hm, ← Original.a_eq]
    exact Subgroup.zpowers_le_of_mem haH
  have hbaseH (b : Wreath m) (hb : b ∈ P ⊓ baseSubgroup m) : b ∈ H := by
    obtain ⟨⟨c, d, e⟩, hcoord⟩ := (coordinateEquiv m).symm.surjective b
    change element m c d e = b at hcoord
    have he : e = 0 := by
      have hbase := hb.2
      change b ∈ baseSubgroup m at hbase
      rwa [← hcoord, element_mem_base] at hbase
    subst e
    have hcd : element m c d 0 ∈ P := hcoord ▸ hb.1
    rcases base_difference_of_center_quotient_dihedral_two k P hP equiv c d hcd with
      hdiag | hdiff
    · apply hcenterH
      rw [← hcoord, element_mem_center_iff m hm]
      exact ⟨rfl, sub_eq_zero.mp hdiag⟩
    · have hdiagmem : element m d d 0 ∈ H :=
        hcenterH ((element_mem_center_iff m hm d d 0).mpr ⟨rfl, rfl⟩)
      have hmul := H.mul_mem hx2H hdiagmem
      rw [Original.x2_eq, hhalf, element_base_mul, zero_add] at hmul
      rw [← hcoord]
      convert hmul using 1
      congr 1
      linear_combination hdiff
  apply le_antisymm
  · intro b hb
    rcases (subgroup_base_cosets m P i j hw b).mp hb with hbase | ⟨c, hc, rfl⟩
    · exact hbaseH b hbase
    · exact H.mul_mem (hbaseH c hc) hwH
  · rw [Subgroup.closure_le]
    intro b hb
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact ha
    · rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact hx2
      · exact Set.mem_singleton_iff.mp hb ▸ hw

theorem nonabelian_small_center_quotient_generators (n : ℕ) (hn : 1 ≤ n)
    (P : Subgroup (Wreath (2 ^ n)))
    (hP : ∃ u v : P, u * v ≠ v * u)
    (hcenter : Subgroup.center (Wreath (2 ^ n)) ≤ P)
    (equiv : P ⧸ Subgroup.center P ≃* DihedralGroup 2) :
    ∃ i j : ZMod (2 ^ n),
      P = Subgroup.closure {Original.a (2 ^ n), Original.x2 (2 ^ n),
        element (2 ^ n) i j 1} := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨i, j, hw⟩ := subgroup_outside_exists _ P (nonabelian_not_le_base _ P hP)
  exact ⟨i, j, nonabelian_center_quotient_dihedral_two_generated k P hP hcenter equiv i j hw⟩

end CFSG.Wreathed
