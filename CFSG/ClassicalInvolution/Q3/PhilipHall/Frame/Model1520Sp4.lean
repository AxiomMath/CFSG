module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Orth
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Core

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Sp

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

variable {F : Type} [Field F]

theorem transvection_pow_three {κ : Type*} [Fintype κ] [DecidableEq κ] {p q : κ} (hpq : p ≠ q)
    (h3 : (3 : F) = 0) (c : F) : (Matrix.transvection p q c) ^ 3 = 1 := by
  rw [pow_three, Matrix.transvection_mul_transvection_same p q hpq,
    Matrix.transvection_mul_transvection_same p q hpq]
  have : c + (c + c) = 0 := by linear_combination c * h3
  rw [this, Matrix.transvection_zero]

theorem longBlock_upper_cube (h3 : (3 : F) = 0) (k : Fin 2) (c : F) :
    (longBlock F 2 k (sl2Upper c)) ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, longBlock_sl2Upper, mat_elt_positiveLong,
    transvection_pow_three (by simp) h3 c, map_one]

theorem longBlock_lower_cube (h3 : (3 : F) = 0) (k : Fin 2) (c : F) :
    (longBlock F 2 k (sl2Lower c)) ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, longBlock_sl2Lower, mat_elt_negativeLong,
    transvection_pow_three (by simp) h3 c, map_one]

theorem exact_fix [Finite F] (hF3 : Nat.card F = 3) (β : MulAut (StatedProj (StatedSp 2 F)))
    (α : MulAut (StatedSp 2 F)) (hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g))
    {r : StatedSp 2 F} (hr : r ^ 3 = 1) (hfix : β (proj 2 F r) = proj 2 F r) : α r = r := by
  have hz : α r * r⁻¹ ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, hfix, mul_inv_cancel]
  have hzc : α r * r⁻¹ ∈ Subgroup.center (StatedSp 2 F) := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]; exact hz
  set z := α r * r⁻¹ with hzdef
  have hαr : α r = z * r := by rw [hzdef]; group
  have hcomm : Commute z r := (Subgroup.mem_center_iff.mp hzc r).symm
  have hz3 : z ^ 3 = 1 := by
    have h1 : (α r) ^ 3 = 1 := by rw [← map_pow, hr, map_one]
    rw [hαr, hcomm.mul_pow, hr, mul_one] at h1
    exact h1
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u =
      (z : GL (Fin 2 ⊕ Fin 2) F) := by
    have := Subgroup.mem_subgroupOf.mp hz
    exact this
  have hu3 : u ^ 3 = 1 := by
    have h := congrArg (fun g : StatedSp 2 F => (g : GL (Fin 2 ⊕ Fin 2) F)) hz3
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h
    rw [← hu, ← map_pow] at h
    have h' := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F =>
      ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (Sum.inl 0) (Sum.inl 0))) h
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Units.ext_iff, Matrix.diagonal_pow] using h'
  have hu2 : u ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := Fˣ) (x := u)
    rwa [Nat.card_units, hF3] at h
  have hu1 : u = 1 := by
    calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
      _ = 1 := by rw [hu3, hu2]; simp
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [← hu, hu1, map_one]
    rfl
  rw [hαr, hz1, one_mul]

theorem three_eq_zero' [Finite F] (hF3 : Nat.card F = 3) : (3 : F) = 0 :=
  Model1520Aux.three_eq_zero_of_card_eq_three hF3

theorem sp4_rigid3 [Finite F] (hF3 : Nat.card F = 3) (β : MulAut (StatedProj (StatedSp 2 F)))
    (hk : ∃ k : ℕ, β ^ (3 ^ k) = 1)
    (hfixU : ∀ (k : Fin 2) (c : F), β (proj 2 F (longBlock F 2 k (sl2Upper c))) =
      proj 2 F (longBlock F 2 k (sl2Upper c)))
    (hfixL : ∀ (k : Fin 2) (c : F), β (proj 2 F (longBlock F 2 k (sl2Lower c))) =
      proj 2 F (longBlock F 2 k (sl2Lower c))) : β = 1 := by
  have h3 : (3 : F) = 0 := three_eq_zero' hF3
  have h2 : (2 : F) ≠ 0 := by
    intro h
    exact one_ne_zero (show (1 : F) = 0 by linear_combination h3 - h)
  obtain ⟨A, σ, hβ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  set α : MulAut (StatedSp 2 F) := conjSp 2 F A * fieldSp 2 F σ with hα
  have hαproj : ∀ g, proj 2 F (α g) = β (proj 2 F g) := fun g => by rw [hβ]; rfl
  have hu : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (σ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := exact_fix hF3 β α hαproj (longBlock_upper_cube h3 k t) (hfixU k t)
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (σ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have hg := exact_fix hF3 β α hαproj (longBlock_lower_cube h3 k t) (hfixL k t)
    have := rel_of_fixed A σ _ hg
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (A : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, a, b, ha, hb, hAab⟩ := sp4_shape σ _ hdet hu hl
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rw [hAab] at hμ
  have hAA : a * a = b * b := sp4_sq a b μ hμ
  subst hσ
  rw [show fieldAut 2 F (RingEquiv.refl F) = 1 from map_one _, mul_one] at hβ
  have hcen : ((A * A : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ∈
      Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 (a * a) (mul_ne_zero ha ha), ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Units.val_mul, hAab,
      diag_sq a b hAA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rfl
  have hconj : conjAut 2 F (A * A) = 1 := by
    ext p
    obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) p
    show proj 2 F (conjSp 2 F (A * A) g) = proj 2 F g
    congr 1
    apply Subtype.ext
    rw [coe_conjSp, ← Subgroup.mem_center_iff.mp hcen (g : GL (Fin 2 ⊕ Fin 2) F),
      mul_inv_cancel_right]
  have hββ : β * β = 1 := by rw [hβ, ← map_mul, hconj]
  obtain ⟨k, hk⟩ := hk
  have h2' : orderOf β ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hββ)
  have h3' : orderOf β ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg := Nat.dvd_gcd h2' h3'
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem diagonal_commute_transvection {κ : Type*} [Fintype κ] [DecidableEq κ] (d : κ → F)
    {p q : κ} (hd : d p = d q) (c : F) :
    Matrix.diagonal d * Matrix.transvection p q c = Matrix.transvection p q c * Matrix.diagonal d := by
  rw [Matrix.transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases hap : p = a <;> by_cases hbq : q = b
  · subst hap; subst hbq; simp [hd, mul_comm]
  · simp [hap, hbq]
  · simp [hap, hbq]
  · simp [hap, hbq]

theorem upper_commute_longInv (k : Fin 2) (c : F) :
    longBlock F 2 k (sl2Upper c) * longInv F 2 0 = longInv F 2 0 * longBlock F 2 k (sl2Upper c) := by
  apply mat_injective
  rw [map_mul, map_mul, longBlock_sl2Upper, mat_elt_positiveLong, mat_longInv]
  refine (diagonal_commute_transvection _ ?_ c).symm
  fin_cases k <;> simp [mem_coords]

theorem lower_commute_longInv (k : Fin 2) (c : F) :
    longBlock F 2 k (sl2Lower c) * longInv F 2 0 = longInv F 2 0 * longBlock F 2 k (sl2Lower c) := by
  apply mat_injective
  rw [map_mul, map_mul, longBlock_sl2Lower, mat_elt_negativeLong, mat_longInv]
  refine (diagonal_commute_transvection _ ?_ c).symm
  fin_cases k <;> simp [mem_coords]

theorem rigid3_psp4 [Finite F] (hF3 : Nat.card F = 3) :
    Rigid3 (StatedProj (StatedSp 2 F)) (proj 2 F (longInv F 2 0)) := by
  have h3 : (3 : F) = 0 := three_eq_zero' hF3
  refine ⟨{s | ∃ (k : Fin 2) (c : F), s = proj 2 F (longBlock F 2 k (sl2Upper c)) ∨
    s = proj 2 F (longBlock F 2 k (sl2Lower c))}, ?_, ?_⟩
  · rintro s ⟨k, c, rfl | rfl⟩
    · refine ⟨?_, ?_⟩
      · rw [← map_pow, longBlock_upper_cube h3, map_one]
      · rw [← map_mul, ← map_mul, upper_commute_longInv]
    · refine ⟨?_, ?_⟩
      · rw [← map_pow, longBlock_lower_cube h3, map_one]
      · rw [← map_mul, ← map_mul, lower_commute_longInv]
  · intro β hk hfix
    exact sp4_rigid3 hF3 β hk (fun k c => hfix _ ⟨k, c, Or.inl rfl⟩)
      (fun k c => hfix _ ⟨k, c, Or.inr rfl⟩)

theorem isPerfect_psp4 [Finite F] (hF3 : Nat.card F = 3) :
    Group.IsPerfect (StatedProj (StatedSp 2 F)) := by
  have : Group.IsPerfect (TauCeti.GLSymplecticFin 2 F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin F 2
      (Or.inr (Or.inl ⟨hF3, le_refl 2⟩))
  let e : TauCeti.GLSymplecticFin 2 F ≃* StatedSp 2 F :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic 2 F).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic
        (n := 2) (K := F)).symm)
  have : Group.IsPerfect (StatedSp 2 F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (spScalars 2 F))
    (QuotientGroup.mk'_surjective _)

theorem model1520_of_PSp {G : Type} [Group G] [Finite G] [Finite F] {X : Subgroup G} {t : G}
    (htX : t ∈ X) (ht : t * t = 1) (hF3 : Nat.card F = 3)
    (e : ↥X ⧸ Subgroup.center ↥X ≃* StatedProj (StatedSp 2 F))
    (het : e (QuotientGroup.mk ⟨t, htX⟩) = proj 2 F (longInv F 2 0)) : Model1520 X t :=
  model1520_of_rigid3 htX ht (isPerfect_psp4 hF3) e het (rigid3_psp4 hF3)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Sp
