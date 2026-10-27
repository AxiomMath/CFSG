module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.AltStdSmall4.W49

open Subgroup Matrix GL62
open scoped Pointwise

theorem mat_ext' {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext h)

@[expose] def BlockScalar (M : GL (Fin 6) (ZMod 2)) (P : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    Prop :=
  ∀ v w : Fin 3 → ZMod 2, (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ Fin.append v w =
    Fin.append (P.1 • v + P.2.1 • w) (P.2.2.1 • v + P.2.2.2 • w)

theorem blockScalar_one : BlockScalar 1 (1, 0, 0, 1) := fun v w => by
  rw [Units.val_one, Matrix.one_mulVec]
  simp

theorem blockScalar_z0 : BlockScalar z₀ (1, 1, 0, 1) := fun v w => by
  rw [z0_mulVec]
  simp

theorem blockScalar_gN : BlockScalar gN (0, 1, 1, 0) := fun v w => by
  rw [gN_mulVec]
  simp

theorem BlockScalar.mul {M N : GL (Fin 6) (ZMod 2)} {P P' : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2}
    (hM : BlockScalar M P) (hN : BlockScalar N P') :
    BlockScalar (M * N) (P.1 * P'.1 + P.2.1 * P'.2.2.1, P.1 * P'.2.1 + P.2.1 * P'.2.2.2,
      P.2.2.1 * P'.1 + P.2.2.2 * P'.2.2.1, P.2.2.1 * P'.2.1 + P.2.2.2 * P'.2.2.2) := fun v w => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hN, hM]
  congr 1 <;> simp only [smul_add, smul_smul, add_smul] <;> abel

theorem BlockScalar.comm_dg {M : GL (Fin 6) (ZMod 2)} {P : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2}
    (hM : BlockScalar M P) (A : GL (Fin 3) (ZMod 2)) : dg A * M = M * dg A := by
  apply Units.ext
  apply mat_ext'
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← append_fst_snd x, hM, dg_mulVec, dg_mulVec, hM, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]

theorem BlockScalar.eq {M N : GL (Fin 6) (ZMod 2)} {P : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2}
    (hM : BlockScalar M P) (hN : BlockScalar N P) : M = N := by
  apply Units.ext
  apply mat_ext'
  intro x
  rw [← append_fst_snd x, hM, hN]

theorem gN_mul_self : gN * gN = 1 := by
  have h := blockScalar_gN.mul blockScalar_gN
  simp only [mul_zero, mul_one, zero_mul, add_zero, zero_add] at h
  exact h.eq blockScalar_one

@[expose] def S3sub : Subgroup (GL (Fin 6) (ZMod 2)) := closure {z₀, gN}

theorem exists_blockScalar {x : GL (Fin 6) (ZMod 2)} (hx : x ∈ S3sub) : ∃ P, BlockScalar x P := by
  have hz0i : z₀⁻¹ = z₀ := z0_inv
  have hgNi : gN⁻¹ = gN := inv_eq_of_mul_eq_one_right gN_mul_self
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨_, blockScalar_one⟩
  | mul_left x hx y _ hy =>
    obtain ⟨P, hP⟩ := hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, blockScalar_z0.mul hP⟩
    · exact ⟨_, blockScalar_gN.mul hP⟩
  | inv_mul_cancel x hx y _ hy =>
    obtain ⟨P, hP⟩ := hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [hz0i]
      exact ⟨_, blockScalar_z0.mul hP⟩
    · rw [hgNi]
      exact ⟨_, blockScalar_gN.mul hP⟩

theorem card_S3sub_le : Nat.card S3sub ≤ 16 := by
  classical
  choose P hP using fun x : S3sub => exists_blockScalar x.2
  have hinj : Function.Injective P := fun x y hxy => by
    have h1 := hP x
    rw [hxy] at h1
    exact Subtype.ext (h1.eq (hP y))
  calc Nat.card S3sub ≤ Nat.card (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :=
        Nat.card_le_card_of_injective P hinj
    _ = 16 := by
      simp only [Nat.card_prod, Nat.card_zmod]

theorem S3sub_le_centralizer : S3sub ≤ centralizer (dg.range : Set (GL (Fin 6) (ZMod 2))) := by
  intro x hx
  obtain ⟨P, hP⟩ := exists_blockScalar hx
  rw [mem_centralizer_iff]
  rintro _ ⟨A, rfl⟩
  exact hP.comm_dg A

theorem S3sub_le_normalizer : S3sub ≤ normalizer (dg.range : Set (GL (Fin 6) (ZMod 2))) :=
  fun s hs => by
    rw [mem_normalizer_iff]
    intro x
    have hc := mem_centralizer_iff.1 (S3sub_le_centralizer hs)
    constructor
    · intro hx
      rw [← hc x hx, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 := hc _ hx
      have h2 : s * x = s * (s * x * s⁻¹) := by
        rw [← h1]
        group
      rw [mul_left_cancel h2]
      exact hx

theorem card_GL3' : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem card_MN_le : Nat.card MN ≤ 2688 := by
  have hle : MN ≤ dg.range ⊔ S3sub := sup_le (sup_le le_sup_left (zpowers_le.2
    (mem_sup_right (subset_closure (Set.mem_insert z₀ {gN})))))
    (zpowers_le.2 (mem_sup_right (subset_closure (Set.mem_insert_of_mem z₀ rfl))))
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left dg.range S3sub S3sub_le_normalizer
  have hsurj : Function.Surjective (fun p : dg.range × S3sub =>
      (⟨(p.1 : GL (Fin 6) (ZMod 2)) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
        (dg.range ⊔ S3sub : Subgroup (GL (Fin 6) (ZMod 2))))) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ (dg.range : Set (GL (Fin 6) (ZMod 2))) *
        (S3sub : Set (GL (Fin 6) (ZMod 2))) := by
      rw [← hm]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hdg : Nat.card dg.range ≤ 168 := by
    rw [← card_GL3']
    exact Nat.card_le_card_of_surjective _ dg.rangeRestrict_surjective
  calc Nat.card MN ≤ Nat.card (dg.range ⊔ S3sub : Subgroup (GL (Fin 6) (ZMod 2))) :=
        Subgroup.card_le_of_le hle
    _ ≤ Nat.card (dg.range × S3sub) := Nat.card_le_card_of_surjective _ hsurj
    _ = Nat.card dg.range * Nat.card S3sub := Nat.card_prod _ _
    _ ≤ 168 * 16 := Nat.mul_le_mul hdg card_S3sub_le
    _ = 2688 := by norm_num

abbrev z0Lit : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 1, 0; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem z0Lit_mulVec : ∀ x : Fin 6 → ZMod 2, z0Lit *ᵥ x = Fin.append (fst x + snd x) (snd x) := by
  decide

theorem coe_z0 : (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = z0Lit :=
  mat_ext' fun x => by rw [z0_mulVec', z0Lit_mulVec]

@[expose] def A5 : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 1; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 1, 1; 0, 1, 0], by decide, by decide⟩

@[expose] def A51 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 1, 0], by decide, by decide⟩

@[expose] def A52 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩

abbrev dgA5Lit : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 1, 1, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 1, 1; 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0]

abbrev dgA51Lit : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 1, 0, 0, 0; 0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 1; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0]

abbrev dgA52Lit : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1;
    0, 0, 0, 1, 0, 0]

theorem dgA5Lit_mulVec : ∀ x : Fin 6 → ZMod 2, dgA5Lit *ᵥ x =
    Fin.append (!![1, 1, 1; 0, 0, 1; 1, 0, 0] *ᵥ fst x)
      (!![1, 1, 1; 0, 0, 1; 1, 0, 0] *ᵥ snd x) := by
  decide

theorem dgA51Lit_mulVec : ∀ x : Fin 6 → ZMod 2, dgA51Lit *ᵥ x =
    Fin.append (!![0, 1, 1; 0, 1, 0; 1, 0, 0] *ᵥ fst x)
      (!![0, 1, 1; 0, 1, 0; 1, 0, 0] *ᵥ snd x) := by
  decide

theorem dgA52Lit_mulVec : ∀ x : Fin 6 → ZMod 2, dgA52Lit *ᵥ x =
    Fin.append (!![0, 1, 0; 0, 0, 1; 1, 0, 0] *ᵥ fst x)
      (!![0, 1, 0; 0, 0, 1; 1, 0, 0] *ᵥ snd x) := by
  decide

theorem coe_dg_A5 : (dg A5 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = dgA5Lit :=
  mat_ext' fun x => by rw [dg_mulVec', dgA5Lit_mulVec]; rfl

theorem coe_dg_A51 : (dg A51 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = dgA51Lit :=
  mat_ext' fun x => by rw [dg_mulVec', dgA51Lit_mulVec]; rfl

theorem coe_dg_A52 : (dg A52 : Matrix (Fin 6) (Fin 6) (ZMod 2)) = dgA52Lit :=
  mat_ext' fun x => by rw [dg_mulVec', dgA52Lit_mulVec]; rfl

theorem orderOf_eq_five {x : GL (Fin 6) (ZMod 2)}
    (h5 : (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 5 = 1)
    (h1 : (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) ≠ 1) : orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h => h1 ?_
  · rw [Units.val_pow_eq_pow_val, h5, Units.val_one]
  · rw [h, Units.val_one]

theorem w5_pow : (gSMat * z0Lit * dgA5Lit) ^ 5 = 1 := by decide

theorem w5_ne : gSMat * z0Lit * dgA5Lit ≠ 1 := by decide

theorem w5'_pow : (gGMat * dgA51Lit * gGMat * dgA52Lit) ^ 5 = 1 := by decide

theorem w5'_ne : gGMat * dgA51Lit * gGMat * dgA52Lit ≠ 1 := by decide

theorem five_dvd_card_MS : 5 ∣ Nat.card MS := by
  have hw : gS * z₀ * dg A5 ∈ MS :=
    mul_mem (mul_mem (mem_sup_right (mem_zpowers gS)) (mem_sup_left (mem_sup_right
      (mem_zpowers z₀)))) (mem_sup_left (mem_sup_left ⟨A5, rfl⟩))
  have hval : ((gS * z₀ * dg A5 : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      gSMat * z0Lit * dgA5Lit := by
    rw [Units.val_mul, Units.val_mul, coe_z0, coe_dg_A5]
    rfl
  have ho : orderOf (gS * z₀ * dg A5) = 5 := by
    refine orderOf_eq_five ?_ ?_ <;> rw [hval]
    · exact w5_pow
    · exact w5_ne
  rw [← ho]
  exact Subgroup.orderOf_dvd_natCard MS hw

theorem five_dvd_card_MG : 5 ∣ Nat.card MG := by
  have hgG : gG ∈ MG := mem_sup_right (mem_zpowers gG)
  have hw : gG * dg A51 * gG * dg A52 ∈ MG :=
    mul_mem (mul_mem (mul_mem hgG (mem_sup_left (mem_sup_left ⟨A51, rfl⟩))) hgG)
      (mem_sup_left (mem_sup_left ⟨A52, rfl⟩))
  have hval : ((gG * dg A51 * gG * dg A52 : GL (Fin 6) (ZMod 2)) :
      Matrix (Fin 6) (Fin 6) (ZMod 2)) = gGMat * dgA51Lit * gGMat * dgA52Lit := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dg_A51, coe_dg_A52]
    rfl
  have ho : orderOf (gG * dg A51 * gG * dg A52) = 5 := by
    refine orderOf_eq_five ?_ ?_ <;> rw [hval]
    · exact w5'_pow
    · exact w5'_ne
  rw [← ho]
  exact Subgroup.orderOf_dvd_natCard MG hw

theorem card_ne_56448 : Nat.card MN ≠ 56448 ∧ Nat.card MS ≠ 56448 ∧ Nat.card MG ≠ 56448 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := card_MN_le
    omega
  · have := five_dvd_card_MS
    rw [h] at this
    norm_num at this
  · have := five_dvd_card_MG
    rw [h] at this
    norm_num at this

end CFSG.OddStandard.AltStdSmall4.W49
