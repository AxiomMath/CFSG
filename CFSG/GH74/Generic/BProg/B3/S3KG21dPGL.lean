module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

namespace CFSG.GH74.Generic.BProg.B3.S3KG

open Matrix Subgroup CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem ringAut_pow_apply' {p : ℕ} {σ : F ≃+* F} (hσ : ∀ a, σ a = a ^ p) (k : ℕ) (x : F) :
    (σ ^ k) x = x ^ (p ^ k) := by
  induction k with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ k ih => rw [pow_succ', RingAut.mul_apply, ih, hσ, ← pow_mul, ← pow_succ]

theorem exists_sqrt_frobenius (hF : ringChar F ≠ 2) {φ : F ≃+* F} (hφ : φ * φ = 1)
    (hφ1 : φ ≠ 1) : ∃ q₀ : ℕ, q₀ ^ 2 = Nat.card F ∧ Odd q₀ ∧ ∀ x, φ x = x ^ q₀ := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hcardN : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨σ, hσ, hord, htop, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      n.pos hcardN
  have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hord]; exact n.pos)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [htop]; exact Subgroup.mem_top φ))
  have hφe : φ = σ ^ (m % (n : ℕ)) := by rw [← hm, ← hord, pow_mod_orderOf]
  set e := m % (n : ℕ) with he
  have he0 : e ≠ 0 := by
    intro h0
    apply hφ1
    rw [hφe, h0, pow_zero]
  have hen : e < n := Nat.mod_lt _ n.pos
  have h2e : (n : ℕ) ∣ 2 * e := by
    rw [← hord]
    apply orderOf_dvd_of_pow_eq_one
    rw [mul_comm, pow_mul, ← hφe, sq, hφ]
  have h2e' : 2 * e = n := by
    obtain ⟨c, hc⟩ := h2e
    have hc2 : c < 2 := by
      by_contra hc2
      push Not at hc2
      have := Nat.mul_le_mul_left (n : ℕ) hc2
      omega
    interval_cases c <;> omega
  refine ⟨ringChar F ^ e, ?_, (hp.odd_of_ne_two hF).pow, fun x => ?_⟩
  · rw [← pow_mul, mul_comm, h2e', hcardN]
  · rw [hφe]
    exact ringAut_pow_apply' hσ e x

theorem isOddPrimePower_card (hF : ringChar F ≠ 2) : IsOddPrimePower (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, hp, hp.odd_of_ne_two hF, n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩

abbrev pslRange (F : Type) [Field F] : Subgroup (PGL2 F) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range

theorem left_mem_of_mul_self (hF : ringChar F ≠ 2) {w : PGammaL2 F} (hw : w * w = 1)
    (hφ : w.right ≠ 1) : w.left ∈ pslRange F := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hφφ : w.right * w.right = 1 := by
    have h := congrArg SemidirectProduct.right hw
    rwa [SemidirectProduct.mul_right, SemidirectProduct.one_right] at h
  have hl : w.left * pgl2FieldAut F w.right w.left = 1 := by
    have h := congrArg SemidirectProduct.left hw
    rwa [SemidirectProduct.mul_left, SemidirectProduct.one_left] at h
  obtain ⟨q₀, hq₀, hq₀odd, hφq⟩ := exists_sqrt_frobenius hF hφφ hφ
  set φ := w.right with hφdef
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective w.left
  rw [← hG] at hl ⊢
  have hmap : pgl2FieldAut F φ (Matrix.ProjGenLinGroup.mk G) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map φ.toRingHom G) := by
    rw [pgl2FieldAut_apply]
    exact pgl2RingEquiv_mk φ G
  rw [hmap, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hl
  obtain ⟨u, hu⟩ := hl
  set Gφ := Matrix.GeneralLinearGroup.map φ.toRingHom G with hGφ
  have hφφx : ∀ x, φ (φ x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hφφ
    simpa only [RingAut.mul_apply, RingAut.one_apply] using this
  have hGφφ : Matrix.GeneralLinearGroup.map φ.toRingHom Gφ = G := by
    ext i j
    simp [hGφ, hφφx]
  have h2 : Gφ * G = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map φ.toRingHom u) := by
    have := congrArg (Matrix.GeneralLinearGroup.map φ.toRingHom) hu
    rw [map_mul, hGφφ, Matrix.GeneralLinearGroup.map_scalar] at this
    exact this.symm
  have hφu : φ (u : F) = u := by
    have e1 : G * (Gφ * G) = (G * Gφ) * G := (mul_assoc _ _ _).symm
    rw [h2, ← hu, Matrix.GeneralLinearGroup.scalar_commute u G] at e1
    have e2 := mul_left_cancel e1
    have e3 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) e2
    simpa using e3
  have hdet : (G : Matrix (Fin 2) (Fin 2) F).det * φ (G : Matrix (Fin 2) (Fin 2) F).det =
      (u : F) ^ 2 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F).det) hu
    simp only [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    have hGφdet : (Gφ : Matrix (Fin 2) (Fin 2) F).det = φ (G : Matrix (Fin 2) (Fin 2) F).det :=
      (RingHom.map_det φ.toRingHom (G : Matrix (Fin 2) (Fin 2) F)).symm
    rw [← hGφdet, ← this, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two, sq]
  set d := (G : Matrix (Fin 2) (Fin 2) F).det with hd
  have hd0 : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero G
  rw [hφq] at hdet hφu
  obtain ⟨k, hk⟩ := hq₀odd
  have hu2k : (u : F) ^ (2 * k) = 1 := by
    have hu0 : (u : F) ≠ 0 := u.ne_zero
    have h1 : (u : F) ^ (2 * k) * u = 1 * u := by rw [← pow_succ, ← hk, hφu, one_mul]
    exact mul_right_cancel₀ hu0 h1
  have hcardF : Fintype.card F = q₀ ^ 2 := by rw [← Nat.card_eq_fintype_card, hq₀]
  have hhalf : Fintype.card F / 2 = (q₀ + 1) * k := by
    rw [hcardF, show q₀ ^ 2 = 2 * ((q₀ + 1) * k) + 1 by rw [hk]; ring]
    generalize (q₀ + 1) * k = m
    omega
  have hsq : IsSquare d := by
    rw [FiniteField.isSquare_iff hF hd0, hhalf, pow_mul,
      show d ^ (q₀ + 1) = (u : F) ^ 2 by rw [pow_succ, mul_comm, hdet], ← pow_mul, hu2k]
  exact (pgl2_mk_mem_psl2_range_iff_det_isSquare G).mpr hsq

end CFSG.GH74.Generic.BProg.B3.S3KG
