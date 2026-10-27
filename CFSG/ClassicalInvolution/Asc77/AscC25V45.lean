module

public import CFSG.ClassicalInvolution.Asc77.AscC25V43
import CFSG.ClassicalInvolution.AschTight.S1911F0b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.GorensteinWalter
open scoped MatrixGroups

section Norm

variable {F : Type} [Field F] [Finite F]

theorem exists_pow_succ_eq {m : ℕ} (hm : 2 ≤ m) (hcard : Nat.card F = m ^ 2) {μ : F} (hμ : μ ≠ 0)
    (hμm : μ ^ m = μ) : ∃ l : F, l ^ (m + 1) = μ := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  let μu : Fˣ := Units.mk0 μ hμ
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp (hg μu)
  have hμu : μu ^ (m - 1) = 1 := by
    apply Units.ext
    have h1 : μ ^ (m - 1) * μ = 1 * μ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hμm, one_mul]
    simpa [μu] using mul_right_cancel₀ hμ h1
  have hN : Nat.card Fˣ = m ^ 2 - 1 := by rw [Nat.card_units, hcard]
  have hord : orderOf g = m ^ 2 - 1 := by
    rw [← hN]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ (s * ((m - 1 : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, hs, zpow_natCast, hμu]
  have h3 : ((m ^ 2 - 1 : ℕ) : ℤ) ∣ s * ((m - 1 : ℕ) : ℤ) := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.mpr h2
  have hm1 : ((m - 1 : ℕ) : ℤ) ≠ 0 := by
    have : 1 ≤ m - 1 := by omega
    omega
  have h4 : (m + 1 : ℤ) ∣ s := by
    have e1 : ((m ^ 2 - 1 : ℕ) : ℤ) = ((m + 1 : ℤ)) * ((m - 1 : ℕ) : ℤ) := by
      have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub this, Nat.cast_sub (show 1 ≤ m by omega)]
      ring
    rw [e1] at h3
    exact (mul_dvd_mul_iff_right hm1).mp h3
  obtain ⟨s', hs'⟩ := h4
  refine ⟨((g ^ s' : Fˣ) : F), ?_⟩
  have h5 : (g ^ s') ^ (m + 1) = μu := by
    rw [← zpow_natCast, ← zpow_mul, ← hs]
    congr 1
    rw [hs']
    push_cast
    ring
  have h6 := congrArg (fun u : Fˣ => (u : F)) h5
  simpa [μu] using h6

end Norm

section Hilbert90

variable {p f : ℕ} [Fact p.Prime]

open CFSG.ClassicalInvolution.Asc77.AscL62 in
open CFSG.ClassicalInvolution.Disconnected.AschTight.S1911 in
theorem exists_pgl_conj_inr (hp : p ≠ 2) (hf : f ≠ 0) (hq : 5 ≤ p ^ f)
    (α : PGammaL2 (GaloisField p f)) (hα : α * α = 1) (hσ : α.right ≠ 1) :
    ∃ γ : PGL2 (GaloisField p f),
      α.left = γ * (pgl2FieldAut (GaloisField p f) α.right γ)⁻¹ := by
  classical
  have hσ2 : α.right * α.right = 1 := by
    have h2 := congrArg SemidirectProduct.right hα
    simpa using h2
  have hleft : α.left * (pgl2FieldAut (GaloisField p f) α.right) α.left = 1 := by
    have h2 := congrArg SemidirectProduct.left hα
    simpa using h2
  obtain ⟨k, hfk, hfrob⟩ := eq_frobenius_of_sq_eq_one hf hσ2 hσ
  obtain ⟨b, hb⟩ := Matrix.ProjGenLinGroup.mk_surjective α.left
  set σ := α.right with hσdef
  have hσσ : ∀ x : GaloisField p f, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : GaloisField p f ≃+* GaloisField p f => τ x) hσ2
    simpa using this
  have hcomp : σ.toRingHom.comp σ.toRingHom = RingHom.id _ := by
    ext x
    exact hσσ x
  have hMM : ∀ x : GL (Fin 2) (GaloisField p f),
      Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map σ.toRingHom x) =
        x := fun x => by
    calc Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.map σ.toRingHom x) =
        Matrix.GeneralLinearGroup.map (σ.toRingHom.comp σ.toRingHom) x := rfl
      _ = x := by rw [hcomp]; rfl
  have hcen : b * Matrix.GeneralLinearGroup.map σ.toRingHom b ∈
      Subgroup.center (GL (Fin 2) (GaloisField p f)) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul, mk_map_eq_pgl2FieldAut σ b, hb]
    exact hleft
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨μ, hμ⟩ := hcen
  have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ.toRingHom : _ →* _) μ) =
      Matrix.GeneralLinearGroup.map σ.toRingHom b * b := by
    rw [← Matrix.GeneralLinearGroup.map_scalar, hμ, map_mul, hMM]
  have h2 : Matrix.GeneralLinearGroup.map σ.toRingHom b * b =
      Matrix.GeneralLinearGroup.scalar (Fin 2) μ := by
    have h3 : Matrix.GeneralLinearGroup.map σ.toRingHom b =
        b⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) μ := by
      rw [hμ]
      group
    rw [h3, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have h4 : σ (μ : GaloisField p f) = (μ : GaloisField p f) := by
    have h5 := h1.trans h2
    have h6 := congrArg (fun x : GL (Fin 2) (GaloisField p f) => x.val 0 0) h5
    simpa using h6
  have hpodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp
  have hm : Odd (p ^ k) := hpodd.pow
  have hcard : Nat.card (GaloisField p f) = (p ^ k) ^ 2 := by
    rw [GaloisField.card p f hf, hfk, ← pow_mul, mul_comm]
  have hm3 : 3 ≤ p ^ k := by
    have h5 : 5 ≤ (p ^ k) ^ 2 := by
      rw [← hcard, GaloisField.card p f hf]
      exact hq
    by_contra hlt
    have h6 : p ^ k ≤ 2 := by omega
    have h7 := Nat.pow_le_pow_left h6 2
    omega
  have hμm : (μ : GaloisField p f) ^ (p ^ k) = μ := by
    rw [← hfrob]
    exact h4
  have hμi : ((μ : GaloisField p f)⁻¹) ^ (p ^ k) = (μ : GaloisField p f)⁻¹ := by
    rw [inv_pow, hμm]
  obtain ⟨l, hl⟩ := exists_pow_succ_eq (m := p ^ k) (by omega) hcard (inv_ne_zero μ.ne_zero) hμi
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero _)] at hl
    exact (inv_ne_zero μ.ne_zero) hl.symm
  let lu : (GaloisField p f)ˣ := Units.mk0 l hl0
  have hb' : (Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b) *
      Matrix.GeneralLinearGroup.map σ.toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b) =
        1 := by
    rw [map_mul, Matrix.GeneralLinearGroup.map_scalar]
    have h7 : lu * Units.map (σ.toRingHom : _ →* _) lu * μ = 1 := by
      apply Units.ext
      show l * σ l * (μ : GaloisField p f) = 1
      rw [hfrob l, ← pow_succ', hl, inv_mul_cancel₀ μ.ne_zero]
    calc (Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b) *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ.toRingHom : _ →* _) lu) *
            Matrix.GeneralLinearGroup.map σ.toRingHom b)
        = Matrix.GeneralLinearGroup.scalar (Fin 2) lu *
            (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ.toRingHom : _ →* _) lu) *
              (b * Matrix.GeneralLinearGroup.map σ.toRingHom b)) := by
          rw [mul_assoc, ← mul_assoc b, ← Matrix.GeneralLinearGroup.scalar_commute _ b,
            mul_assoc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2)
            (lu * Units.map (σ.toRingHom : _ →* _) lu * μ) := by
          rw [← hμ, map_mul, map_mul, mul_assoc]
      _ = 1 := by rw [h7, map_one]
  have hA : ((Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b : GL (Fin 2) (GaloisField p f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p f)) *
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b : GL (Fin 2) (GaloisField p f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField p f)).map σ = 1 := by
    have h8 := congrArg (fun x : GL (Fin 2) (GaloisField p f) =>
      (x : Matrix (Fin 2) (Fin 2) (GaloisField p f))) hb'
    exact h8
  obtain ⟨P, hPdet, hAP⟩ := exists_mul_map_eq_self hcard hm3 σ hfrob hσσ _ hA
  let Pg : GL (Fin 2) (GaloisField p f) := Matrix.nonsingInvUnit P hPdet
  have hPg : (Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b) *
      Matrix.GeneralLinearGroup.map σ.toRingHom Pg = Pg := Units.ext hAP
  refine ⟨Matrix.ProjGenLinGroup.mk Pg, ?_⟩
  rw [← hb]
  have hmk : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b) =
      Matrix.ProjGenLinGroup.mk b := by
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  rw [← hmk]
  have h' : Matrix.GeneralLinearGroup.scalar (Fin 2) lu * b =
      Pg * (Matrix.GeneralLinearGroup.map σ.toRingHom Pg)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hPg
  rw [h', map_mul, map_inv, mk_map_eq_pgl2FieldAut σ Pg]

theorem eq_inl_mul_inr_mul_inv (α : PGammaL2 (GaloisField p f)) (γ : PGL2 (GaloisField p f))
    (h : α.left = γ * (pgl2FieldAut (GaloisField p f) α.right γ)⁻¹) :
    α = SemidirectProduct.inl γ * SemidirectProduct.inr α.right * (SemidirectProduct.inl γ)⁻¹ := by
  apply SemidirectProduct.ext
  · simp [h]
  · simp

end Hilbert90

end CFSG.ClassicalInvolution.Asc77.C25V
