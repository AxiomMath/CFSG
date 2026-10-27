module

public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8.GapDS

open CFSG.Open CFSG.Semidihedral Subgroup

theorem dihedral_rot_of_comm {n : ℕ} {x g : DihedralGroup n} (hx : orderOf x = 4)
    (hg : g * x = x * g) : ∃ j, g = DihedralGroup.r j := by
  rcases x with i | i
  · rcases g with j | j
    · exact ⟨j, rfl⟩
    · exfalso
      rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at hg
      have h2 : i + i = 0 := by
        have := DihedralGroup.sr.inj hg
        linear_combination this
      have : DihedralGroup.r i ^ 2 = 1 := by
        rw [pow_two, DihedralGroup.r_mul_r, h2]; rfl
      have h4 := orderOf_dvd_of_pow_eq_one this
      rw [hx] at h4
      norm_num at h4
  · exfalso
    rw [DihedralGroup.orderOf_sr] at hx
    norm_num at hx

theorem dihedral_rot_le (n : ℕ) {g : DihedralGroup n} (hg : ∃ j, g = DihedralGroup.r j) :
    g ∈ zpowers (DihedralGroup.r (1 : ZMod n)) := by
  obtain ⟨j, rfl⟩ := hg
  refine ⟨(j.cast : ℤ), ?_⟩
  simp only [DihedralGroup.r_one_zpow, ZMod.intCast_cast, ZMod.cast_id', id_eq]

theorem sd_coord {n : ℕ} (hn : 3 ≤ n) (g : SemidihedralGroup n) :
    ∃ i e, g = element n hn i e :=
  let p := coordinateEquiv n hn g
  ⟨p.1, p.2, by
    change g = (coordinateEquiv n hn).symm (p.1, p.2)
    rw [Prod.mk.eta, Equiv.symm_apply_apply]⟩

theorem sd_rot_of_comm {n : ℕ} (hn : 4 ≤ n) {x g : SemidihedralGroup n} (hx : orderOf x = 4)
    (h4 : 4 < Nat.card (centralizer ({x} : Set (SemidihedralGroup n))))
    (hg : g ∈ centralizer ({x} : Set (SemidihedralGroup n))) : g ∈ rotationSubgroup n := by
  have hn3 : 3 ≤ n := le_trans (by norm_num) hn
  obtain ⟨i, ε, rfl⟩ := sd_coord hn3 x
  rcases exponent_cases ε with rfl | rfl
  ·
    obtain ⟨j, δ, rfl⟩ := sd_coord hn3 g
    rw [element_mem_rotationSubgroup_iff]
    rcases exponent_cases δ with rfl | rfl
    · rfl
    · exfalso
      have hc := mem_centralizer_singleton_iff.mp hg
      rw [element_rotation_mul, element_reflection_mul, element_eq_iff] at hc
      have hfix : twist n * i = i := by
        have := hc.1
        linear_combination this
      rcases (twist_fixed_iff n hn i).mp hfix with h | h
      · subst h
        rw [element_zero_zero, orderOf_one] at hx
        norm_num at hx
      · subst h
        rw [← z_eq_element n hn3, orderOf_z n hn3] at hx
        norm_num at hx
  ·
    exfalso
    apply (not_lt.mpr ?_) h4
    classical
    let s : Finset (SemidihedralGroup n) :=
      {element n hn3 0 0, element n hn3 (half n : ZMod (modulus n)) 0, element n hn3 i 1,
        element n hn3 (i + (half n : ZMod (modulus n))) 1}
    have hsub : (centralizer ({element n hn3 i 1} : Set (SemidihedralGroup n)) :
        Set (SemidihedralGroup n)) ⊆ (s : Set (SemidihedralGroup n)) := by
      intro g hg
      have hc := mem_centralizer_singleton_iff.mp hg
      obtain ⟨j, δ, rfl⟩ := sd_coord hn3 g
      simp only [s, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, element_eq_iff]
      rcases exponent_cases δ with rfl | rfl
      · rw [element_rotation_mul, element_reflection_mul, element_eq_iff] at hc
        have hfix : twist n * j = j := by
          have := hc.1
          linear_combination -this
        rcases (twist_fixed_iff n hn j).mp hfix with h | h
        · left; exact ⟨h, rfl⟩
        · right; left; exact ⟨h, rfl⟩
      · rw [element_reflection_mul, element_reflection_mul, element_eq_iff] at hc
        have hfix : twist n * (j - i) = j - i := by
          have := hc.1
          linear_combination -this
        rcases (twist_fixed_iff n hn (j - i)).mp hfix with h | h
        · right; right; left; exact ⟨by linear_combination h, rfl⟩
        · right; right; right; exact ⟨by linear_combination h, rfl⟩
    calc Nat.card (centralizer ({element n hn3 i 1} : Set (SemidihedralGroup n)))
        ≤ Nat.card (s : Set (SemidihedralGroup n)) := Nat.card_mono (Set.toFinite _) hsub
      _ = s.card := Nat.card_coe_set_eq _ |>.trans (Set.ncard_coe_finset s)
      _ ≤ 4 := Finset.card_le_four

end CFSG.ComponentClassification.HSFLit.Sec8.GapDS
