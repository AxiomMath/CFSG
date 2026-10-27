module

public import CFSG.CharacterTheory.Semidihedral.FocalFusion

public section

namespace CFSG.Semidihedral.InvolutionFusion

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_ambient_conjugate_mem_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : G) (hx : IsPGroup p (Subgroup.zpowers x)) :
    ∃ y : S, IsConj x (y : G) := by
  obtain ⟨P, hP⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  refine ⟨⟨g * x * g⁻¹, ?_⟩, isConj_iff.mpr ⟨g, rfl⟩⟩
  change g * x * g⁻¹ ∈ (S : Subgroup G)
  rw [← hg, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (P : Subgroup G)
    (hP (Subgroup.mem_zpowers x))

@[expose] def conjugatedEquiv (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (g : G) :
    SemidihedralGroup n ≃* (g • S : Sylow 2 G) :=
  f.trans (S.equivSMul g)

theorem conjugatedEquiv_apply_coe (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (g : G) (x : SemidihedralGroup n) :
    (conjugatedEquiv n S f g x : G) = g * (f x : G) * g⁻¹ := by
  change (Subgroup.equivSMul (MulAut.conj g) (S : Subgroup G) (f x) : G) = _
  rw [Subgroup.equivSMul_apply_coe]
  rfl

theorem supplied_s_isConj_z [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    IsConj (f (s n) : G) (f (z n) : G) := by
  have hs := ((FocalFusion.semidihedral_focal_subgroup_four_cases n hn S f).2.2.2.2.mp
    hG).1
  change IsConj (f (s n) : G) ((f (r n) ^ (modulus n / 2) : S) : G) at hs
  simpa only [z, map_pow, modulus_div_two n (by omega)] using hs

theorem supplied_involution_isConj_z [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2)
    (x : SemidihedralGroup n) (hx : orderOf x = 2) :
    IsConj (f x : G) (f (z n) : G) := by
  rcases (involution_iff n (by omega) x).mp hx with rfl | ⟨j, rfl⟩
  · exact IsConj.refl _
  · have hsj : IsConj (s n) (r n ^ (2 * j.val) * s n) := by
      have h := even_outside_conjugate n hn (j.val : ℤ)
      change IsConj (s n) (r n ^ ((2 : ℕ) * j.val : ℤ) * s n) at h
      rw [← Int.natCast_mul, zpow_natCast] at h
      exact h
    exact ((FocalFusion.ambientHom n (S : Subgroup G) f).map_isConj hsj.symm).trans
      (supplied_s_isConj_z n hn S f hG)

theorem ambient_involution_isConj_z [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    IsConj t (f (z n) : G) := by
  have hpt : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨y, hty⟩ := exists_ambient_conjugate_mem_sylow S t hpt
  have hy : orderOf (f.symm y) = 2 := by
    have hi := orderOf_injective (FocalFusion.ambientHom n (S : Subgroup G) f)
      (FocalFusion.ambientHom_injective n (S : Subgroup G) f) (f.symm y)
    change orderOf (f (f.symm y) : G) = orderOf (f.symm y) at hi
    rw [f.apply_symm_apply] at hi
    exact hi.symm.trans ((conjugate_orderOf_eq hty).symm.trans ht)
  exact hty.trans (by
    simpa only [f.apply_symm_apply] using
      supplied_involution_isConj_z n hn S f hG (f.symm y) hy)

theorem exists_centered_semidihedral_sylow [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) (t : G) (ht : orderOf t = 2) :
    ∃ (S_t : Sylow 2 G) (f_t : SemidihedralGroup n ≃* S_t),
      (f_t (z n) : G) = t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (ambient_involution_isConj_z n hn S f hG t ht).symm
  exact ⟨g • S, conjugatedEquiv n S f g,
    (conjugatedEquiv_apply_coe n S f g (z n)).trans hg⟩

theorem involution_centered_sylow_existence [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (hG : ∀ H : Subgroup G, H.index ≠ 2) :
    ∀ t : G, orderOf t = 2 →
      IsConj t (f (z n) : G) ∧
        ∃ (S_t : Sylow 2 G) (f_t : SemidihedralGroup n ≃* S_t),
          (f_t (z n) : G) = t ∧
          ((f_t (r n) ^ (2 ^ (n - 2)) : S_t) : G) = t := by
  intro t ht
  refine ⟨ambient_involution_isConj_z n hn S f hG t ht, ?_⟩
  obtain ⟨S_t, f_t, hz⟩ := exists_centered_semidihedral_sylow n hn S f hG t ht
  exact ⟨S_t, f_t, hz, by simpa only [z, half, map_pow] using hz⟩

end CFSG.Semidihedral.InvolutionFusion
