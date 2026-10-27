module

public import CFSG.LargeExtraspecial.S45QSylow
public import CFSG.Fischer.Classification.Recognition.SymOOrth

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S45Q

open Module Subgroup CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem isSimpleGroup_isometryGroup [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) :
    IsSimpleGroup (TauCeti.BilinForm.isometryGroup β) := by
  obtain ⟨k, hk⟩ := LinearMap.BilinForm.IsAlt.even_finrank hβ hnd
  exact CFSG.Fischer.Classification.Recognition.SymO.isSimpleGroup_isometryGroup β hβ hnd
    (k := k) (by omega) (by omega)

theorem spTransvection_mul_comm (hβ : β.IsAlt) {u w : V} (huw : β u w = 0) :
    spTransvection β hβ u * spTransvection β hβ w =
      spTransvection β hβ w * spTransvection β hβ u := by
  have hwu : β w u = 0 := by rw [isAlt_symm hβ, huw]
  ext v
  simp only [LinearEquiv.mul_apply, spTransvection_apply, map_add, map_smul, huw, hwu]
  match_scalars <;> ring

section Dihedral

variable (hβ : β.IsAlt) {a b z : V} (hab : β a b = 1) (haz : β a z = 0) (hbz : β b z = 0)
include hβ hab haz hbz

theorem spTransvection_triple_apply (v : V) :
    (spTransvection β hβ a * (spTransvection β hβ b * spTransvection β hβ (b + z))) v =
      v + (β v a + β v b + β v (b + z)) • a + β v b • b + β v (b + z) • (b + z) := by
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hza : β z a = 0 := by rw [isAlt_symm hβ, haz]
  have hzb : β z b = 0 := by rw [isAlt_symm hβ, hbz]
  simp only [LinearEquiv.mul_apply, spTransvection_apply, map_add, map_smul,
    hβ.self_eq_zero, hba, hza, hzb]
  match_scalars <;> ring_nf

theorem spTransvection_triple_sq_apply (v : V) :
    ((spTransvection β hβ a * (spTransvection β hβ b * spTransvection β hβ (b + z))) ^ 2) v =
      v + β v z • a + β v (a + z) • z := by
  have hba : β b a = 1 := by rw [isAlt_symm hβ, hab]
  have hza : β z a = 0 := by rw [isAlt_symm hβ, haz]
  have hzb : β z b = 0 := by rw [isAlt_symm hβ, hbz]
  rw [sq, LinearEquiv.mul_apply, spTransvection_triple_apply hβ hab haz hbz,
    spTransvection_triple_apply hβ hab haz hbz]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hβ.self_eq_zero, hab,
    hba, haz, hza, hbz, hzb, smul_eq_mul]
  match_scalars <;> ring_nf <;> reduce_mod_char

end Dihedral

theorem nonabelianSylowTwo_isometryGroup [FiniteDimensional (ZMod 2) V] (hβ : β.IsAlt)
    (hnd : β.Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) V) :
    S5.NonabelianSylowTwo (TauCeti.BilinForm.isometryGroup β) := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨a, ha⟩ := exists_ne (0 : V)
  have hne : ∀ {w : V}, w ≠ 0 → ∃ u, β u w = 1 := fun {w} hw => by
    by_contra h
    push Not at h
    apply hw
    refine hnd.2 w fun u => ?_
    rcases zmod2_eq_zero_or_eq_one (β u w) with h0 | h1
    · exact h0
    · exact absurd h1 (h u)
  obtain ⟨b, hb⟩ := hne ha
  have hab : β a b = 1 := by rw [isAlt_symm hβ, hb]
  obtain ⟨z, hz0, haz, hbz⟩ := S4.exists_ne_zero_perp_pair hnd (by omega) a b
  set x := spTransvection β hβ a
  set y := spTransvection β hβ b * spTransvection β hβ (b + z)
  have hsq := spTransvection_triple_sq_apply hβ hab haz hbz
  have hxx : x * x = 1 := S4.spTransvection_mul_self hβ a
  have hbbz : β (b + z) b = 0 := by
    rw [map_add, LinearMap.add_apply, hβ.self_eq_zero, isAlt_symm hβ, hbz, add_zero]
  have hyy : y * y = 1 := by
    calc y * y = spTransvection β hβ b * (spTransvection β hβ (b + z) * spTransvection β hβ b) *
          spTransvection β hβ (b + z) := by simp only [y]; group
      _ = spTransvection β hβ b * (spTransvection β hβ b * spTransvection β hβ (b + z)) *
          spTransvection β hβ (b + z) := by rw [spTransvection_mul_comm hβ hbbz]
      _ = (spTransvection β hβ b * spTransvection β hβ b) *
          (spTransvection β hβ (b + z) * spTransvection β hβ (b + z)) := by group
      _ = 1 := by rw [S4.spTransvection_mul_self, S4.spTransvection_mul_self, one_mul]
  have hT2 : (x * y) ^ 2 ≠ 1 := by
    intro h
    obtain ⟨v, hv⟩ := hne hz0
    have h1 := hsq v
    rw [h, hv, one_smul] at h1
    change v = v + a + β v (a + z) • z at h1
    rw [add_assoc, left_eq_add] at h1
    rcases zmod2_eq_zero_or_eq_one (β v (a + z)) with h0 | h0
    · rw [h0, zero_smul, add_zero] at h1
      exact ha h1
    · rw [h0, one_smul] at h1
      have : β b a = β b z := by
        rw [eq_neg_of_add_eq_zero_left h1, map_neg, zmod2_neg]
      rw [isAlt_symm hβ, hab, hbz] at this
      exact one_ne_zero this
  refine nonabelianSylowTwo_of_mem (spTransvection_mem_isometryGroup hβ a)
    (mul_mem (spTransvection_mem_isometryGroup hβ b) (spTransvection_mem_isometryGroup hβ _))
    hxx hyy (k := 2) ?_ ?_
  · rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul]
    ext v
    rw [sq ((x * y) ^ 2), LinearEquiv.mul_apply, hsq, hsq]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hβ.self_eq_zero,
      haz, smul_eq_mul]
    have hza : β z a = 0 := by rw [isAlt_symm hβ, haz]
    rw [hza]
    change _ = v
    match_scalars <;> ring_nf <;> reduce_mod_char
  · intro h
    apply hT2
    rw [sq, show x * y * (x * y) = x * (y * x) * y by group, ← h,
      show x * (x * y) * y = (x * x) * (y * y) by group, hxx, hyy, one_mul]

end CFSG.LargeExtraspecial.S45Q
