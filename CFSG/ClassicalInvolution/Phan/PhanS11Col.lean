module

public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

section Col

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K)

@[expose] noncomputable def gram7 (a b : W7 K) : K :=
  hrm D a a * hrm D b b - hrm D a b * hrm D b a

@[expose] noncomputable def Col7 (a b : W7 K) : Prop :=
  polar (quadOdd 3 K) a b = 0 ∧ gram7 D a b ≠ 0

@[expose] noncomputable def det3_7 (a b c : W7 K) : K :=
  hrm D a a * (hrm D b b * hrm D c c - hrm D b c * hrm D c b) -
    hrm D a b * (hrm D b a * hrm D c c - hrm D b c * hrm D c a) +
    hrm D a c * (hrm D b a * hrm D c b - hrm D b b * hrm D c a)

@[expose] noncomputable def Geom7 (a b c : W7 K) : Prop :=
  Col7 D a b ∧ Col7 D b c ∧ Col7 D c a ∧ (det3_7 D a b c ≠ 0 ∨ ∃ s t : K, c = s • a + t • b)

theorem gram7_smul (c d : K) (a b : W7 K) :
    gram7 D (c • a) (d • b) = (c * D.τ c) * (d * D.τ d) * gram7 D a b := by
  simp only [gram7, hrm_smul_left, hrm_smul_right]
  ring

theorem col7_smul {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) {a b : W7 K} :
    Col7 D (c • a) (d • b) ↔ Col7 D a b := by
  have hτc : D.τ c ≠ 0 := fun h => hc (by rw [← D.tau_tau c, h, map_zero])
  have hτd : D.τ d ≠ 0 := fun h => hd (by rw [← D.tau_tau d, h, map_zero])
  have hf : (c * D.τ c) * (d * D.τ d) ≠ 0 := mul_ne_zero (mul_ne_zero hc hτc) (mul_ne_zero hd hτd)
  unfold Col7
  rw [gram7_smul, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => h2 (by rw [h, mul_zero])⟩
    have : (c * d) * polar (quadOdd 3 K) a b = 0 := by
      simp only [smul_eq_mul] at h1
      linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hc hd)
  · rintro ⟨h1, h2⟩
    exact ⟨by simp [h1], mul_ne_zero hf h2⟩

theorem col7_actK (g : spinGroup (quadOdd 3 F)) (a b : W7 K) :
    Col7 D (actK g a) (actK g b) ↔ Col7 D a b := by
  unfold Col7 gram7
  rw [polar_actK, hrm_actK, hrm_actK, hrm_actK, hrm_actK]

theorem det3_7_actK (g : spinGroup (quadOdd 3 F)) (a b c : W7 K) :
    det3_7 D (actK g a) (actK g b) (actK g c) = det3_7 D a b c := by
  simp only [det3_7, hrm_actK]

theorem actK_actK_inv (g : spinGroup (quadOdd 3 F)) (x : W7 K) : actK g (actK g⁻¹ x) = x := by
  rw [← actK_mul, mul_inv_cancel, actK_one]

theorem actK_inv_actK (g : spinGroup (quadOdd 3 F)) (x : W7 K) : actK g⁻¹ (actK g x) = x := by
  rw [← actK_mul, inv_mul_cancel, actK_one]

end Col

section Transport

variable {F K : Type} [Field F] [Field K] [Algebra F K] (D : KDat F K) (c₂ : K)
  (h2K : (2 : K) ≠ 0) (hc : c₂ * D.τ c₂ = -1 / 4)

theorem hrm_Θ (x y : Std.Vec K) :
    hrm D (ΘEquiv D c₂ h2K hc x) (ΘEquiv D c₂ h2K hc y) = Std.her (stdModel D h2K) x y := by
  rw [hrm, ΘEquiv_apply, ΘEquiv_apply, ← Θ_tauV D c₂ h2K, polar_Θ D c₂ h2K hc]
  rfl

theorem polar_ΘEquiv (x y : Std.Vec K) :
    polar (quadOdd 3 K) (ΘEquiv D c₂ h2K hc x) (ΘEquiv D c₂ h2K hc y) =
      Std.bf (stdModel D h2K) x y := by
  rw [ΘEquiv_apply, ΘEquiv_apply, polar_Θ D c₂ h2K hc]

theorem isFF_iff_isFF7 (x : Std.Vec K) :
    Std.IsFF (stdModel D h2K) x ↔ IsFF7 D (ΘEquiv D c₂ h2K hc x) := by
  unfold Std.IsFF IsFF7
  rw [hrm_Θ D c₂ h2K hc, ← polar_ΘEquiv D c₂ h2K hc, QuadraticMap.polar_self]
  refine and_congr_left fun _ => ?_
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left h2K, fun h => by rw [h, mul_zero]⟩

theorem col_iff_col7 (x y : Std.Vec K) :
    Std.Col (stdModel D h2K) x y ↔
      Col7 D (ΘEquiv D c₂ h2K hc x) (ΘEquiv D c₂ h2K hc y) := by
  unfold Std.Col Col7 gram7 Std.gram
  rw [polar_ΘEquiv D c₂ h2K hc, hrm_Θ D c₂ h2K hc, hrm_Θ D c₂ h2K hc, hrm_Θ D c₂ h2K hc,
    hrm_Θ D c₂ h2K hc]

theorem geom_iff_geom7 (x y z : Std.Vec K) :
    Std.Geom (stdModel D h2K) x y z ↔
      Geom7 D (ΘEquiv D c₂ h2K hc x) (ΘEquiv D c₂ h2K hc y) (ΘEquiv D c₂ h2K hc z) := by
  unfold Std.Geom Geom7
  rw [← col_iff_col7 D c₂ h2K hc, ← col_iff_col7 D c₂ h2K hc, ← col_iff_col7 D c₂ h2K hc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  refine or_congr ?_ ?_
  · unfold Std.det3 det3_7
    simp only [hrm_Θ D c₂ h2K hc]
  · constructor
    · rintro ⟨s, t, h⟩
      exact ⟨s, t, by rw [h, map_add, map_smul, map_smul]⟩
    · rintro ⟨s, t, h⟩
      refine ⟨s, t, ?_⟩
      apply (ΘEquiv D c₂ h2K hc).injective
      rw [h, map_add, map_smul, map_smul]

end Transport

end CFSG.ClassicalInvolution.PhanB3.S
