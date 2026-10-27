module

public import CFSG.ClassicalInvolution.Asc77.AscC25V9

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Diag

variable (F : Type) [Field F] [Finite F]

@[expose] noncomputable def sqHom : Fˣ →* ℤˣ := by
  classical
  letI := Fintype.ofFinite F
  exact (quadraticChar F).toUnitHom

variable {F}

theorem sqHom_eq_one_iff (u : Fˣ) : sqHom F u = 1 ↔ IsSquare (u : F) := by
  classical
  let := Fintype.ofFinite F
  have := quadraticChar_one_iff_isSquare (F := F) u.ne_zero
  unfold sqHom
  rw [Units.ext_iff]
  simpa using this

theorem sqHom_map (σ : F ≃+* F) (u : Fˣ) :
    sqHom F (Units.map (σ.toRingHom : F →* F) u) = sqHom F u := by
  have hsq : IsSquare ((Units.map (σ.toRingHom : F →* F) u : Fˣ) : F) ↔ IsSquare (u : F) := by
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨σ.symm r, ?_⟩
      apply σ.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      exact hr
    · rintro ⟨r, hr⟩
      exact ⟨σ r, by simp [hr]⟩
  rcases Int.units_eq_one_or (sqHom F u) with h | h
  · rw [h, sqHom_eq_one_iff, hsq, ← sqHom_eq_one_iff, h]
  · have h1 : sqHom F u ≠ 1 := by rw [h]; decide
    have h2 : sqHom F (Units.map (σ.toRingHom : F →* F) u) ≠ 1 := by
      rw [Ne, sqHom_eq_one_iff, hsq, ← sqHom_eq_one_iff]
      exact h1
    rw [h]
    rcases Int.units_eq_one_or (sqHom F (Units.map (σ.toRingHom : F →* F) u)) with h3 | h3
    · exact absurd h3 h2
    · exact h3

@[expose] noncomputable def diagGL : GL (Fin 2) F →* ℤˣ :=
  (sqHom F).comp Matrix.GeneralLinearGroup.det

theorem diagGL_scalar : (diagGL (F := F)).comp (Matrix.GeneralLinearGroup.scalar (Fin 2)) = 1 := by
  ext u
  simp [diagGL, Matrix.GeneralLinearGroup.det_scalar]

@[expose] noncomputable def diagPGL : PGL2 F →* ℤˣ :=
  Matrix.ProjGenLinGroup.lift diagGL diagGL_scalar

theorem diagPGL_mk (g : GL (Fin 2) F) :
    diagPGL (Matrix.ProjGenLinGroup.mk g : PGL2 F) = sqHom F (Matrix.GeneralLinearGroup.det g) :=
  rfl

theorem diagPGL_field (σ : F ≃+* F) (g : PGL2 F) : diagPGL (pgl2RingEquiv σ g) = diagPGL g := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk g =>
    change diagPGL (pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) g)) = _
    rw [pgl2RingEquiv_mk]
    change sqHom F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map σ.toRingHom g)) =
      sqHom F (Matrix.GeneralLinearGroup.det g)
    rw [Matrix.GeneralLinearGroup.map_det]
    exact sqHom_map σ _

@[expose] noncomputable def diagGamma : PGammaL2 F →* ℤˣ :=
  SemidirectProduct.lift diagPGL (1 : (F ≃+* F) →* ℤˣ) (fun σ => by
    ext g
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.one_apply, mul_one, one_mul, inv_one]
    rw [pgl2FieldAut_apply, diagPGL_field])

theorem diagGamma_apply (α : PGammaL2 F) : diagGamma α = diagPGL α.left := by
  change diagPGL α.left * (1 : (F ≃+* F) →* ℤˣ) α.right = diagPGL α.left
  simp

end Diag

section Alg

variable {F : Type} [Field F] [Finite F]

theorem isSquare_of_mul_pow_eq {m : ℕ} (hm : Odd m) (hcard : Nat.card F = m ^ 2)
    (hchar : ringChar F ≠ 2) {d u : F} (hd : d ≠ 0) (hu : u ≠ 0) (hum : u ^ m = u)
    (h : d * d ^ m = u ^ 2) : IsSquare d := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨j, rfl⟩ := hm
  rw [FiniteField.isSquare_iff hchar hd, ← Nat.card_eq_fintype_card, hcard]
  have h1 : (2 * j + 1) ^ 2 / 2 = (2 * j + 2) * j := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  rw [h1, pow_mul]
  have h2 : d ^ (2 * j + 2) = u ^ 2 := by
    rw [← h]
    ring
  rw [h2, ← pow_mul]
  have h3 : u ^ (2 * j) * u = 1 * u := by
    rw [← pow_succ, hum, one_mul]
  exact mul_right_cancel₀ hu h3

end Alg

section Invol

variable {p f : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.Asc77.AscL62 in
theorem diagGamma_eq_one_of_involution (hp : p ≠ 2) (hf : f ≠ 0)
    (α : PGammaL2 (GaloisField p f)) (hα : α * α = 1) (hσ : α.right ≠ 1) :
    diagGamma α = 1 := by
  classical
  have hσ2 : α.right * α.right = 1 := by
    have h2 := congrArg SemidirectProduct.right hα
    simpa using h2
  have hleft : α.left * (pgl2FieldAut (GaloisField p f) α.right) α.left = 1 := by
    have h2 := congrArg SemidirectProduct.left hα
    simpa using h2
  obtain ⟨k, hfk, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ
  rw [diagGamma_apply]
  obtain ⟨g, hg⟩ := Matrix.ProjGenLinGroup.mk_surjective α.left
  set σ := α.right with hσdef
  have hmk : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map σ.toRingHom g) =
      pgl2FieldAut (GaloisField p f) σ α.left := by
    rw [← hg, pgl2FieldAut_apply]
    exact (pgl2RingEquiv_mk σ g).symm
  have hcen : g * Matrix.GeneralLinearGroup.map σ.toRingHom g ∈
      Subgroup.center (GL (Fin 2) (GaloisField p f)) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, hmk, hg]
    exact hleft
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨u, hu⟩ := hcen
  have hσσ : ∀ x : GaloisField p f, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hσ2
    simpa using this
  have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id _ := by
    ext x
    exact hσσ x
  have hMM : Matrix.GeneralLinearGroup.map σ.toRingHom
      (Matrix.GeneralLinearGroup.map σ.toRingHom g) = g := by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom
          (Matrix.GeneralLinearGroup.map σ.toRingHom g) =
        Matrix.GeneralLinearGroup.map (σ.toRingHom.comp σ.toRingHom) g := rfl
      _ = g := by rw [hcomp]; rfl
  set M' := Matrix.GeneralLinearGroup.map σ.toRingHom g with hM'
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ.toRingHom : _ →* _) u) =
      M' * g := by
    rw [← Matrix.GeneralLinearGroup.map_scalar, hu, map_mul, hMM]
  have h2 : M' * g = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
    have h3 : M' = g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
      rw [hu]
      group
    rw [h3, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have h4 : σ (u : GaloisField p f) = (u : GaloisField p f) := by
    have h5 := h1.trans h2
    have h6 := congrArg (fun x : GL (Fin 2) (GaloisField p f) => x.val 0 0) h5
    simpa using h6
  have h7 : (Matrix.GeneralLinearGroup.det g : GaloisField p f) *
      σ (Matrix.GeneralLinearGroup.det g : GaloisField p f) = (u : GaloisField p f) ^ 2 := by
    have h8 := congrArg (fun x : GL (Fin 2) (GaloisField p f) =>
      ((Matrix.GeneralLinearGroup.det x : (GaloisField p f)ˣ) : GaloisField p f)) hu
    simpa [Matrix.GeneralLinearGroup.det_scalar, map_mul, Matrix.GeneralLinearGroup.map_det, hM',
      eq_comm] using h8
  have hpodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hm : Odd (p ^ k) := hpodd.pow
  have hcard : Nat.card (GaloisField p f) = (p ^ k) ^ 2 := by
    rw [GaloisField.card p f hf, hfk, ← pow_mul, mul_comm]
  have hchar : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp
  have hum : (u : GaloisField p f) ^ (p ^ k) = u := by
    rw [← hfrob]
    exact h4
  have hsq : IsSquare (Matrix.GeneralLinearGroup.det g : GaloisField p f) :=
    isSquare_of_mul_pow_eq hm hcard hchar (Units.ne_zero _) (Units.ne_zero _) hum
      (by rw [← hfrob]; exact h7)
  rw [← hg, diagPGL_mk, sqHom_eq_one_iff]
  exact hsq

end Invol

section Char

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def diagChar (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    Subgroup.normalizer (K : Set G) →* ℤˣ :=
  diagGamma.comp (normalizerToPGammaL2Mod e (gf_facts hp hq).2.1 (gf_facts hp hq).2.2.1
    (gf_facts hp hq).2.2.2)

theorem diagChar_eq_one_of_involution (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G}
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1)
    (hσ : fieldChar hp hq e ⟨a, haN⟩ ≠ 1) : diagChar hp hq e ⟨a, haN⟩ = 1 := by
  have h1 : (⟨a, haN⟩ : Subgroup.normalizer (K : Set G)) * ⟨a, haN⟩ = 1 := Subtype.ext ha2
  refine diagGamma_eq_one_of_involution hp (gf_facts hp hq).1 _ ?_ hσ
  rw [← map_mul, h1, map_one]

end Char

end CFSG.ClassicalInvolution.Asc77.C25V
