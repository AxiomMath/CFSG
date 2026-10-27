module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUFix

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K] {f : ℕ}

theorem smul_one_map {n : ℕ} (g : K → K) (hg : g 0 = 0) (a : K) :
    (a • (1 : Matrix (Fin n) (Fin n) K)).map g = g a • 1 := by
  ext i j
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, hg]

@[expose] noncomputable def torusGL : Kˣ →* GL (Fin (2 + 2)) K :=
  blkGL.comp (((GeneralLinearGroup.scalar (Fin 2)).comp invMonoidHom).prod
    (GeneralLinearGroup.scalar (Fin 2)))

theorem coe_torusGL (c : Kˣ) :
    (torusGL c : GL (Fin (2 + 2)) K).val = blk (((c⁻¹ : Kˣ) : K) • 1) ((c : K) • 1) := by
  simp only [torusGL, MonoidHom.comp_apply, MonoidHom.prod_apply, invMonoidHom_apply]
  rw [coe_blkGL]
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]

theorem blk_smul_one_mem_genSU {a b : K} (ha : a ^ 2 ^ f * a = 1) (hb : b ^ 2 ^ f * b = 1)
    (hab : a * b = 1) :
    (blk (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • (1 : Matrix (Fin 2) (Fin 2) K))).det = 1 ∧
      ((blk (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • (1 : Matrix (Fin 2) (Fin 2) K))).map
        (· ^ 2 ^ f))ᵀ *
        blk (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  have h0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero f two_ne_zero)
  refine ⟨?_, ?_⟩
  · rw [det_blk, det_smul, det_smul, det_one, Fintype.card_fin, mul_one, mul_one,
      ← mul_pow, hab, one_pow]
  · rw [blk_map_fun (fun x : K => x ^ 2 ^ f) h0, smul_one_map (fun x : K => x ^ 2 ^ f) h0,
      smul_one_map (fun x : K => x ^ 2 ^ f) h0, transpose_blk]
    simp only [transpose_smul, transpose_one]
    rw [blk_mul, smul_one_mul_smul_one, smul_one_mul_smul_one, ha, hb]
    simp only [one_smul, blk_one]

theorem torusGL_mem {c : Kˣ} (hc : c ∈ rootsOfUnity (2 ^ f + 1) K) :
    torusGL c ∈ StatedSU (2 + 2) (2 ^ f) K := by
  have hc' : (c : K) ^ 2 ^ f * c = 1 := by
    have h1 := congrArg Units.val ((mem_rootsOfUnity _ _).mp hc)
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h1
  have hci : ((c⁻¹ : Kˣ) : K) ^ 2 ^ f * ((c⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, ← mul_inv, hc', inv_one]
  unfold StatedSU
  refine Subgroup.subset_closure ?_
  change (torusGL c : GL (Fin (2 + 2)) K).val.det = 1 ∧
    ((torusGL c : GL (Fin (2 + 2)) K).val.map (· ^ 2 ^ f))ᵀ *
      (torusGL c : GL (Fin (2 + 2)) K).val = 1
  rw [coe_torusGL]
  exact blk_smul_one_mem_genSU hci hc' (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])

variable (K f) in
@[expose] noncomputable def torusU : rootsOfUnity (2 ^ f + 1) K →* StatedSU (2 + 2) (2 ^ f) K :=
  (torusGL.comp (rootsOfUnity (2 ^ f + 1) K).subtype).codRestrict _ fun c => torusGL_mem c.2

theorem coe_torusU (c : rootsOfUnity (2 ^ f + 1) K) :
    ((torusU K f c : StatedSU (2 + 2) (2 ^ f) K) : GL (Fin (2 + 2)) K).val =
      blk ((((c : Kˣ)⁻¹ : Kˣ) : K) • 1) (((c : Kˣ) : K) • 1) :=
  coe_torusGL _

variable (K f) in
@[expose] noncomputable def uBarT : Subgroup (StatedProj (StatedSU (2 + 2) (2 ^ f) K)) :=
  ((uProj K (2 + 2) f).comp (torusU K f)).range

theorem blk_mul_smul_one_comm (X D : Matrix (Fin 2) (Fin 2) K) (a b : K) :
    blk X D * blk (a • 1) (b • 1) = blk (a • 1) (b • 1) * blk X D := by
  rw [blk_mul, blk_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

theorem uBarT_commute_uBarL {t l : StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    (ht : t ∈ uBarT K f) (hl : l ∈ uBarL K 2 f) : t * l = l * t := by
  obtain ⟨c, rfl⟩ := ht
  obtain ⟨S, rfl⟩ := hl
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_torusU, coe_uL, ← blk_mul_smul_one_comm]

theorem uBarT_commute_uBarW {t w : StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    (ht : t ∈ uBarT K f) (hw : w ∈ uBarW K 2 f) : t * w = w * t := by
  obtain ⟨c, rfl⟩ := ht
  obtain ⟨X, rfl⟩ := hw
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_torusU, coe_uW, ← blk_mul_smul_one_comm]

theorem exists_rootsOfUnity_ne_one {ζ : K} (hζ : ζ ^ 2 ^ f * ζ = 1) (hζ1 : ζ ≠ 1) :
    ∃ c : rootsOfUnity (2 ^ f + 1) K, ((c : Kˣ) : K) = ζ ∧ c ≠ 1 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hζ
    exact zero_ne_one hζ
  refine ⟨⟨Units.mk0 ζ hζ0, (mem_rootsOfUnity _ _).mpr (Units.ext ?_)⟩, rfl, fun h1 => hζ1 ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, pow_succ, hζ]
  · have := congrArg (fun c : rootsOfUnity (2 ^ f + 1) K => ((c : Kˣ) : K)) h1
    simpa using this

end Torus

section Bar

variable {K : Type} [Field K] [CharP K 2] {f : ℕ} {τ : K ≃+* K} {A : GL (Fin (2 + 2)) K}
  {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))}

theorem false_of_fix_torus_bar (h : UnitaryFieldData 2 f K)
    (hα : ∀ g : StatedSU (2 + 2) (2 ^ f) K,
      ∃ hg : A * glAut τ (g : GL (Fin (2 + 2)) K) * A⁻¹ ∈ StatedSU (2 + 2) (2 ^ f) K,
        α (uProj K (2 + 2) f g) = uProj K (2 + 2) f ⟨_, hg⟩)
    (hτ : ∀ c, τ c = h.bar c) {A₁ D : Matrix (Fin 2) (Fin 2) K} (hA : A.val = blk A₁ D)
    {c : rootsOfUnity (2 ^ f + 1) K} (hc : c ≠ 1)
    (hfix : α (uProj K (2 + 2) f (torusU K f c)) = uProj K (2 + 2) f (torusU K f c)) : False := by
  set u : K := ((c : Kˣ) : K) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hcq : u ^ 2 ^ f * u = 1 := by
    have h1 := congrArg Units.val ((mem_rootsOfUnity _ _).mp c.2)
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_succ] at h1
  have hbar : τ u = u⁻¹ := by rw [hτ, h.bar_apply]; exact eq_inv_of_mul_eq_one_left hcq
  obtain ⟨c', hc'⟩ := exists_scalar_of_fix hα hfix
  rw [coe_torusU, blk_map_fun _ (map_zero τ), smul_one_map _ (map_zero τ),
    smul_one_map _ (map_zero τ), Units.val_inv_eq_inv_val, map_inv₀, ← hu, hbar, inv_inv, hA,
    blk_mul, blk_mul, blk_smul] at hc'
  obtain ⟨h1, h2⟩ := blk_injective hc'
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h1 h2
  obtain ⟨hA₁, hD⟩ := det_ne_zero_of_blk hA
  have hA₁0 : A₁ ≠ 0 := fun h0 => hA₁ (by rw [h0, det_zero])
  have hD0 : D ≠ 0 := fun h0 => hD (by rw [h0, det_zero])
  have e1 : u⁻¹ = (c' : K) * u := by
    have h3 : (u⁻¹ - (c' : K) * u) • A₁ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hA₁0)
  have e2 : u = (c' : K) * u⁻¹ := by
    have h3 : (u - (c' : K) * u⁻¹) • D = 0 := by rw [sub_smul, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hD0)
  have e3 : u * u = u⁻¹ * u⁻¹ := by
    calc u * u = (c' : K) * u⁻¹ * u := by rw [← e2]
      _ = (c' : K) := by rw [mul_assoc, inv_mul_cancel₀ hu0, mul_one]
      _ = (c' : K) * u * u⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hu0, mul_one]
      _ = u⁻¹ * u⁻¹ := by rw [← e1]
  have e4 : u = u⁻¹ := eq_of_mul_self_eq e3
  have e5 : u = 1 := by
    have h6 : u * u = 1 * 1 :=
      calc u * u = u * u⁻¹ := by rw [← e4]
        _ = 1 * 1 := by rw [mul_inv_cancel₀ hu0, mul_one]
    exact eq_of_mul_self_eq h6
  apply hc
  apply Subtype.ext
  apply Units.ext
  rw [← hu, e5]
  rfl

end Bar

end CFSG.ComponentClassification.RankTwoClassical
