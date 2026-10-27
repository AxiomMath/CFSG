module

public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.FooteLit.TwoSub

open CFSG Subgroup CFSG.Open CFSG.Semidihedral

variable {G : Type*} [Group G]

@[expose] noncomputable def sdHomOf (n : ℕ) (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1)
    (hb : b ^ 2 = 1) (hba : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) : SemidihedralGroup n →* G :=
  PresentedGroup.toGroup (f := ![a, b]) (by
    intro r hr
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using ha
    · simpa using hb
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hba, mul_inv_cancel])

theorem sdHomOf_r (n : ℕ) (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1) (hb : b ^ 2 = 1)
    (hba : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) : sdHomOf n a b ha hb hba (r n) = a :=
  PresentedGroup.toGroup.of _

theorem sdHomOf_s (n : ℕ) (a b : G) (ha : a ^ (2 ^ (n - 1)) = 1) (hb : b ^ 2 = 1)
    (hba : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1)) : sdHomOf n a b ha hb hba (s n) = b :=
  PresentedGroup.toGroup.of _

theorem nonempty_mulEquiv_semidihedral_of {n : ℕ} (hn : 4 ≤ n) {H : Subgroup G} [Finite H]
    (hH : Nat.card H ≤ 2 ^ n) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (hao : orderOf a = 2 ^ (n - 1)) (hb2 : b ^ 2 = 1) (hba : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hbn : b ∉ zpowers a) : Nonempty (H ≃* SemidihedralGroup n) := by
  have ha1 : a ^ (2 ^ (n - 1)) = 1 := by rw [← hao]; exact pow_orderOf_eq_one a
  set φ := sdHomOf n a b ha1 hb2 hba
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [mem_bot]
    obtain ⟨c, rfl, -⟩ := unique_normal_form n (by omega) g
    rw [map_mul, map_pow, map_pow, sdHomOf_r, sdHomOf_s] at hg
    have hi : c.1.val < 2 ^ (n - 1) := c.1.2
    have he : c.2.val < 2 := c.2.2
    by_cases he1 : c.2.val = 0
    · rw [he1, pow_zero, mul_one] at hg ⊢
      have hc0 : c.1.val = 0 := by
        by_contra h0
        have := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero h0) hg
        omega
      rw [hc0, pow_zero]
    · exfalso
      have he' : c.2.val = 1 := by omega
      rw [he', pow_one] at hg
      apply hbn
      rw [show b = (a ^ c.1.val)⁻¹ from eq_inv_of_mul_eq_one_right hg]
      exact inv_mem (pow_mem (mem_zpowers a) _)
  have hle : φ.range ≤ H := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    fin_cases k
    · exact (sdHomOf_r n a b ha1 hb2 hba) ▸ ha
    · exact (sdHomOf_s n a b ha1 hb2 hba) ▸ hb
  have hcard : Nat.card φ.range = 2 ^ n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card n (by omega)]
  have heq : φ.range = H := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard]
    exact hH
  exact ⟨(MulEquiv.subgroupCongr heq.symm).trans (MonoidHom.ofInjective hinj).symm⟩

end CFSG.ComponentClassification.FooteLit.TwoSub
