module

public import CFSG.ClassicalInvolution.ModelFacts.MF15One
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts.OrthAut
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def frameHypFam (fr : Frame Q) : Fin 2 → Bool → V := fun i s =>
  if i = 0 then (if s then fr.e₁ else fr.f₁) else (if s then fr.e₂ else fr.f₂)

theorem isHypFam_frameHypFam (fr : Frame Q) : IsHypFam Q (frameHypFam fr) := by
  refine ⟨fun i s => ?_, fun i j hij s t => ?_, fun i s => ?_⟩
  · fin_cases i <;> cases s <;> simp [frameHypFam, Frame.Q_e₁, Frame.Q_f₁, Frame.Q_e₂, Frame.Q_f₂]
  · fin_cases i <;> fin_cases j <;> cases s <;> cases t <;>
      simp [frameHypFam, Frame.polar_e₁_e₂, Frame.polar_e₁_f₂, Frame.polar_f₁_e₂,
        Frame.polar_f₁_f₂, Frame.polar_e₂_e₁, Frame.polar_f₂_e₁, Frame.polar_e₂_f₁,
        Frame.polar_f₂_f₁] at hij ⊢
  · fin_cases i <;> cases s <;>
      simp [frameHypFam, Frame.polar_e₁_f₁, Frame.polar_f₁_e₁, Frame.polar_e₂_f₂,
        Frame.polar_f₂_e₂]

theorem frame_map_eq_of_apply (fr fr' : Frame Q) {g : V ≃ₗ[F] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : g fr.e₁ = fr'.e₁)
    (h2 : g fr.f₁ = fr'.f₁) (h3 : g fr.e₂ = fr'.e₂) (h4 : g fr.f₂ = fr'.f₂) :
    fr.map hg = fr' := by
  obtain ⟨⟨e₁, f₁, a₁, b₁, c₁⟩, ⟨e₂, f₂, a₂, b₂, c₂⟩, o⟩ := fr
  obtain ⟨⟨e₁', f₁', a₁', b₁', c₁'⟩, ⟨e₂', f₂', a₂', b₂', c₂'⟩, o'⟩ := fr'
  simp only [Frame.map, Frame.e₁, Frame.f₁, Frame.e₂, Frame.f₂] at h1 h2 h3 h4 ⊢
  subst h1 h2 h3 h4
  rfl

theorem exists_isometry_frame [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (fr fr' : Frame Q) :
    ∃ g : V ≃ₗ[F] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      ∀ A : SL(2, F), fr'.La A = g * fr.La A * g⁻¹ := by
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨g, hg, hgv⟩ :=
    exists_isometry_of_isHypFam (isHypFam_frameHypFam fr) (isHypFam_frameHypFam fr')
  have h1 : g fr.e₁ = fr'.e₁ := by simpa [frameHypFam] using hgv 0 true
  have h2' : g fr.f₁ = fr'.f₁ := by simpa [frameHypFam] using hgv 0 false
  have h3 : g fr.e₂ = fr'.e₂ := by simpa [frameHypFam] using hgv 1 true
  have h4 : g fr.f₂ = fr'.f₂ := by simpa [frameHypFam] using hgv 1 false
  refine ⟨g, hg, fun A => ?_⟩
  rw [← frame_map_eq_of_apply fr fr' hg h1 h2' h3 h4, Frame.map_La]

theorem La_one_apply (fr : Frame Q) (v : V) : fr.La 1 v = v := by
  rw [map_one]; rfl

theorem La_eq_one_of_isScalar (fr : Frame Q) [FiniteDimensional F V]
    (hperp : fr.perp ≠ ⊥) (A : SL(2, F)) (hs : ∃ s : F, ∀ v, fr.La A v = s • v) : A = 1 := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  have h1 : fr.La A r = r := Frame.La_apply_of_coords_eq_zero fr A ((Frame.mem_perp_iff fr).mp hr)
  have hs1 : s = 1 := by
    have := hs r
    rw [h1] at this
    have h3 : (1 - s) • r = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
    have := (smul_eq_zero.mp h3).resolve_right hr0
    linear_combination -this
  apply fr.La_injective
  ext v
  rw [hs v, hs1, one_smul, La_one_apply]

theorem sl2_sq_eq_neg_one_of_orderOf_four (h2 : (2 : F) ≠ 0) (A : SL(2, F))
    (h4 : orderOf A = 4) : (A : Matrix (Fin 2) (Fin 2) F) * A = -1 := by
  have hA4 : A ^ 4 = 1 := by rw [← h4]; exact pow_orderOf_eq_one A
  set B : SL(2, F) := A ^ 2 with hB
  have hBB : B * B = 1 := by
    calc B * B = A ^ 4 := by rw [hB, ← pow_add]
      _ = 1 := hA4
  have hB1 : B ≠ 1 := by
    rw [hB]; exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h4]; norm_num)
  have hBm : (B : Matrix (Fin 2) (Fin 2) F) = (A : Matrix (Fin 2) (Fin 2) F) * A := by
    rw [hB, pow_two]; rfl
  rw [← hBm]
  have hM : (B : Matrix (Fin 2) (Fin 2) F) * B = 1 := by
    have := congrArg (fun z : SL(2, F) => (z : Matrix (Fin 2) (Fin 2) F)) hBB
    simpa using this
  have hdet : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := B.2
  have hM1 : (B : Matrix (Fin 2) (Fin 2) F) ≠ 1 := fun h => hB1 (Subtype.ext h)
  set M : Matrix (Fin 2) (Fin 2) F := (B : Matrix (Fin 2) (Fin 2) F) with hMdef
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have := congrFun (congrFun hM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    have := congrFun (congrFun hM 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    have := congrFun (congrFun hM 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet; exact hdet
  by_cases hsum : M 0 0 + M 1 1 = 0
  · exfalso
    exact h2 (by linear_combination M 0 0 * hsum - h00 - hd)
  · have hb : M 0 1 = 0 := by
      have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp this).resolve_right hsum
    have hc : M 1 0 = 0 := by
      have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp this).resolve_right hsum
    rw [hb, hc] at h00 hd
    have ha : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination h00
    rcases mul_eq_zero.mp ha with h | h
    · exfalso
      have ha1 : M 0 0 = 1 := sub_eq_zero.mp h
      have hd1 : M 1 1 = 1 := by rw [ha1] at hd; linear_combination hd
      apply hM1
      rw [Matrix.eta_fin_two M, hb, hc, ha1, hd1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have ha1 : M 0 0 = -1 := eq_neg_of_add_eq_zero_left h
      have hd1 : M 1 1 = -1 := by rw [ha1] at hd; linear_combination -hd
      rw [Matrix.eta_fin_two M, hb, hc, ha1, hd1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem isScalar_pow_La_iff (h2 : (2 : F) ≠ 0) [FiniteDimensional F V] (fr : Frame Q)
    (hperp : fr.perp ≠ ⊥) (A : SL(2, F)) (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1)
    (m : ℕ) : (∃ s : F, ∀ v, (fr.La A ^ m) v = s • v) ↔ 4 ∣ m := by
  have h4 : orderOf A = 4 := by
    rw [← orderOf_injective fr.La fr.La_injective A]
    exact orderOf_La_eq_four h2 fr A hA
  constructor
  · rintro ⟨s, hs⟩
    have h1 : A ^ m = 1 := La_eq_one_of_isScalar fr hperp (A ^ m)
      ⟨s, fun v => by rw [map_pow]; exact hs v⟩
    rw [← h4]
    exact orderOf_dvd_of_pow_eq_one h1
  · intro h
    refine ⟨1, fun v => ?_⟩
    have h1 : A ^ m = 1 := by
      rw [← h4] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    rw [← map_pow, h1, one_smul]
    exact La_one_apply fr v

end CFSG.ClassicalInvolution.ModelFacts.MF15
