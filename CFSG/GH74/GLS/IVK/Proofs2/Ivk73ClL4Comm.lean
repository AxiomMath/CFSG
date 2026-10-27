module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSFacts

public noncomputable section

namespace CFSG.GH74.GLS.IVK

open CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag Polynomial

namespace RowSComm

section VLevel

variable {k E : Type} [Field k] [CommRing E] [Algebra k E]

theorem eq_one_or_zero_of_eq_smul {M : Type} [AddCommGroup M] [Module k M] (c : k) (a : M)
    (h : a = c • a) : c = 1 ∨ a = 0 := by
  have h1 : (1 - c) • a = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl (sub_eq_zero.mp h2).symm
  · exact Or.inr h2

theorem vec2_ext {R : Type} {u w : Fin 2 → R} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  funext i; fin_cases i
  · exact h0
  · exact h1

theorem upper_comm [Nontrivial E] (T : (Fin 2 → E) →ₗ[k] (Fin 2 → E))
    (hinj : Function.Injective T)
    (hup : ∀ x : E, ∃ c : k, ∀ v : Fin 2 → E,
      T ![v 0 + x * v 1, v 1] = c • ![T v 0 + x * T v 1, T v 1]) (x : E) (v : Fin 2 → E) :
    T ![v 0 + x * v 1, v 1] = ![T v 0 + x * T v 1, T v 1] := by
  obtain ⟨c, hc⟩ := hup x
  have hne0 : T ![1, 0] ≠ 0 := by
    intro h
    have := hinj (h.trans (map_zero T).symm)
    have h0 := congrFun this 0
    simp at h0
  have h1 := hc ![1, 0]
  have hc1 : c = 1 := by
    have e1 : T ![1, 0] 1 = c • T ![1, 0] 1 := by
      have := congrFun h1 1
      simpa using this
    rcases eq_one_or_zero_of_eq_smul c _ e1 with h | h
    · exact h
    · have e0 : T ![1, 0] 0 = c • T ![1, 0] 0 := by
        have := congrFun h1 0
        simpa [h] using this
      rcases eq_one_or_zero_of_eq_smul c _ e0 with h' | h'
      · exact h'
      · exact absurd (by ext i; fin_cases i <;> simp [h, h']) hne0
  rw [hc v, hc1, one_smul]

theorem lower_comm [Nontrivial E] (T : (Fin 2 → E) →ₗ[k] (Fin 2 → E))
    (hinj : Function.Injective T)
    (hlo : ∀ x : E, ∃ c : k, ∀ v : Fin 2 → E,
      T ![v 0, x * v 0 + v 1] = c • ![T v 0, x * T v 0 + T v 1]) (x : E) (v : Fin 2 → E) :
    T ![v 0, x * v 0 + v 1] = ![T v 0, x * T v 0 + T v 1] := by
  obtain ⟨c, hc⟩ := hlo x
  have hne1 : T ![0, 1] ≠ 0 := by
    intro h
    have := hinj (h.trans (map_zero T).symm)
    have h0 := congrFun this 1
    simp at h0
  have h1 := hc ![0, 1]
  have hc1 : c = 1 := by
    have e0 : T ![0, 1] 0 = c • T ![0, 1] 0 := by
      have := congrFun h1 0
      simpa using this
    rcases eq_one_or_zero_of_eq_smul c _ e0 with h | h
    · exact h
    · have e1 : T ![0, 1] 1 = c • T ![0, 1] 1 := by
        have := congrFun h1 1
        simpa [h] using this
      rcases eq_one_or_zero_of_eq_smul c _ e1 with h' | h'
      · exact h'
      · exact absurd (by ext i; fin_cases i <;> simp [h, h']) hne1
  rw [hc v, hc1, one_smul]

theorem commutant_V [Nontrivial E] (T : (Fin 2 → E) →ₗ[k] (Fin 2 → E))
    (hinj : Function.Injective T)
    (hup : ∀ x : E, ∃ c : k, ∀ v : Fin 2 → E,
      T ![v 0 + x * v 1, v 1] = c • ![T v 0 + x * T v 1, T v 1])
    (hlo : ∀ x : E, ∃ c : k, ∀ v : Fin 2 → E,
      T ![v 0, x * v 0 + v 1] = c • ![T v 0, x * T v 0 + T v 1]) :
    ∃ c0 : E, ∀ v : Fin 2 → E, T v = ![c0 * v 0, c0 * v 1] := by
  have hu := upper_comm T hinj hup
  have hl := lower_comm T hinj hlo
  have z : (![0, 0] : Fin 2 → E) = 0 := by ext i; fin_cases i <;> simp
  have hn : ∀ (x : E) (v : Fin 2 → E), T ![x * v 1, 0] = ![x * T v 1, 0] := by
    intro x v
    have h := hu x v
    have e : ![v 0 + x * v 1, v 1] = v + ![x * v 1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e, map_add] at h
    refine vec2_ext ?_ ?_
    · have := congrFun h 0
      simp only [Pi.add_apply, Matrix.cons_val_zero] at this ⊢
      linear_combination this
    · have := congrFun h 1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this ⊢
      linear_combination this
  have hm : ∀ (x : E) (v : Fin 2 → E), T ![0, x * v 0] = ![0, x * T v 0] := by
    intro x v
    have h := hl x v
    have e : ![v 0, x * v 0 + v 1] = v + ![0, x * v 0] := by
      ext i; fin_cases i <;> simp [add_comm]
    rw [e, map_add] at h
    refine vec2_ext ?_ ?_
    · have := congrFun h 0
      simp only [Pi.add_apply, Matrix.cons_val_zero] at this ⊢
      linear_combination this
    · have := congrFun h 1
      simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this ⊢
      linear_combination this
  have ha1 : T ![1, 0] 1 = 0 := by
    have := congrFun (hn 1 ![1, 0]) 0
    simp [z] at this
    exact this.symm
  have hb0 : T ![0, 1] 0 = 0 := by
    have := congrFun (hm 1 ![0, 1]) 1
    simp [z] at this
    exact this.symm
  have hab : T ![1, 0] 0 = T ![0, 1] 1 := by
    have := congrFun (hn 1 ![0, 1]) 0
    simpa using this
  refine ⟨T ![1, 0] 0, fun v => ?_⟩
  have hv : v = ![v 0, 0] + ![0, v 1] := by ext i; fin_cases i <;> simp
  have h0 : T ![v 0, 0] = ![T ![1, 0] 0 * v 0, 0] := by
    have := hn (v 0) ![0, 1]
    simp only [mul_one, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, ← hab, mul_comm]
  have h1 : T ![0, v 1] = ![0, T ![1, 0] 0 * v 1] := by
    have := hm (v 1) ![1, 0]
    simp only [mul_one, Matrix.cons_val_zero] at this
    rw [this, mul_comm]
  rw [hv, map_add, h0, h1]
  ext i; fin_cases i <;> simp

end VLevel

section Coord

variable {k : Type} [Field k] (ν : kˣ)

theorem exists_coord [Nontrivial (extension (ν : k))] (z : extension (ν : k)) :
    ∃ x y : k, z = algebraMap k (extension (ν : k)) x +
      algebraMap k (extension (ν : k)) y * AdjoinRoot.root (quadraticPolynomial (ν : k)) := by
  obtain ⟨f, hf, rfl⟩ :=
    (AdjoinRoot.powerBasis' (quadraticPolynomial_monic (ν : k))).exists_eq_aeval z
  have h2 : f.natDegree ≤ 1 := by
    have := quadraticPolynomial_natDegree (ν : k)
    simp only [AdjoinRoot.powerBasis'_dim] at hf
    omega
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one h2]
  simp [add_comm]

theorem coord_eq_zero {x y : k}
    (h : algebraMap k (extension (ν : k)) x +
      algebraMap k (extension (ν : k)) y * AdjoinRoot.root (quadraticPolynomial (ν : k)) = 0) :
    x = 0 ∧ y = 0 := by
  by_contra hne
  have hp : (C y * X + C x : k[X]) ≠ 0 := by
    intro hp
    apply hne
    have h1 := congrArg (fun p : k[X] => p.coeff 0) hp
    have h2 := congrArg (fun p : k[X] => p.coeff 1) hp
    simp at h1 h2
    exact ⟨h1, h2⟩
  have := PowerBasis.dim_le_natDegree_of_root
    (AdjoinRoot.powerBasis' (quadraticPolynomial_monic (ν : k))) hp (by
      simpa [add_comm] using h)
  have h3 : (C y * X + C x : k[X]).natDegree ≤ 1 := by
    compute_degree
  have := quadraticPolynomial_natDegree (ν : k)
  simp only [AdjoinRoot.powerBasis'_dim] at *
  omega

theorem coord_cases [Nontrivial (extension (ν : k))] (h2 : (2 : k) ≠ 0) (c : kˣ)
    {c0 : extension (ν : k)}
    (hsq : c0 * c0 = algebraMap k (extension (ν : k)) (c : k)) :
    ∃ x : kˣ, c0 = algebraMap k (extension (ν : k)) (x : k) ∨
      c0 = algebraMap k (extension (ν : k)) (x : k) *
        AdjoinRoot.root (quadraticPolynomial (ν : k)) := by
  obtain ⟨x, y, hxy⟩ := exists_coord ν c0
  have hroot : AdjoinRoot.root (quadraticPolynomial (ν : k)) ^ 2 =
      algebraMap k (extension (ν : k)) (ν : k) := extension_root_square (ν : k)
  have key : algebraMap k (extension (ν : k)) (x * x + y * y * (ν : k) - (c : k)) +
      algebraMap k (extension (ν : k)) (2 * x * y) *
        AdjoinRoot.root (quadraticPolynomial (ν : k)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_ofNat]
    rw [hxy] at hsq
    linear_combination hsq - (algebraMap k (extension (ν : k)) y) ^ 2 * hroot
  obtain ⟨h1, h3⟩ := coord_eq_zero ν key
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 h2
    · subst h5
      have hy : y ≠ 0 := by
        rintro rfl
        simp at h1
      refine ⟨Units.mk0 y hy, Or.inr ?_⟩
      simpa using hxy
  · subst h4
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h1
    refine ⟨Units.mk0 x hx, Or.inl ?_⟩
    simpa using hxy

end Coord

section Transport

variable {k : Type} [Field k] (ν : kˣ) {m : ℕ}
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin m → k))

theorem gl_scalar_mulVec (c : kˣ) (v : Fin m → k) :
    ((GeneralLinearGroup.scalar (Fin m) c : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ v =
      (c : k) • v := by
  rw [GeneralLinearGroup.coe_scalar, scalar_apply]
  ext i
  simp [mulVec_diagonal]

theorem transport_apply (B : GL (Fin m) k) (h : GL (Fin 2) (extension (ν : k))) (c : kˣ)
    (hB : B * rowSPi ν Ψ h = GeneralLinearGroup.scalar (Fin m) c * rowSPi ν Ψ h * B)
    (v : Fin 2 → extension (ν : k)) :
    Ψ.symm ((B : Matrix (Fin m) (Fin m) k) *ᵥ
        Ψ ((h : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ v)) =
      (c : k) • ((h : Matrix (Fin 2) (Fin 2) (extension (ν : k))) *ᵥ
        Ψ.symm ((B : Matrix (Fin m) (Fin m) k) *ᵥ Ψ v)) := by
  have := congrArg (fun A : GL (Fin m) k => (A : Matrix (Fin m) (Fin m) k) *ᵥ Ψ v) hB
  simp only [Units.val_mul, ← mulVec_mulVec, rowSPi_mulVec_apply, gl_scalar_mulVec] at this
  rw [rowSPi_mulVec ν Ψ h ((B : Matrix (Fin m) (Fin m) k) *ᵥ Ψ v)] at this
  rw [this, map_smul, LinearEquiv.symm_apply_apply]

@[expose] def rowSTrans (B : Matrix (Fin m) (Fin m) k) :
    (Fin 2 → extension (ν : k)) →ₗ[k] (Fin 2 → extension (ν : k)) :=
  (Ψ.symm : (Fin m → k) →ₗ[k] (Fin 2 → extension (ν : k))).comp
    ((Matrix.mulVecLin B).comp (Ψ : (Fin 2 → extension (ν : k)) →ₗ[k] (Fin m → k)))

theorem rowSTrans_apply (B : Matrix (Fin m) (Fin m) k) (v : Fin 2 → extension (ν : k)) :
    rowSTrans ν Ψ B v = Ψ.symm (B *ᵥ Ψ v) := rfl

theorem rowSU_mulVec (w : Fin m → k) :
    ((rowSU ν Ψ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ w =
      Ψ (AdjoinRoot.root (quadraticPolynomial (ν : k)) • Ψ.symm w) := by
  rw [rowSU, rowSPi_mulVec, GeneralLinearGroup.coe_scalar, scalar_apply]
  congr 2
  ext i
  simp [mulVec_diagonal, coe_rootUnit]

end Transport

section Transvection

variable {R : Type} [CommRing R]

@[expose] def upperSL (x : R) : SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def lowerSL (x : R) : SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_toGL_upperSL (x : R) :
    ((SpecialLinearGroup.toGL (upperSL x) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![1, x; 0, 1] := rfl

theorem coe_toGL_lowerSL (x : R) :
    ((SpecialLinearGroup.toGL (lowerSL x) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![1, 0; x, 1] := rfl

theorem upperSL_mulVec (x : R) (v : Fin 2 → R) :
    ((SpecialLinearGroup.toGL (upperSL x) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) *ᵥ v =
      ![v 0 + x * v 1, v 1] := by
  rw [coe_toGL_upperSL]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem lowerSL_mulVec (x : R) (v : Fin 2 → R) :
    ((SpecialLinearGroup.toGL (lowerSL x) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) *ᵥ v =
      ![v 0, x * v 0 + v 1] := by
  rw [coe_toGL_lowerSL]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end Transvection

section Normalizer

variable {k : Type} [Field k] (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k))

theorem exists_mul_of_normalizes [Nontrivial (extension (ν : k))] (B : GL (Fin 4) k)
    (hB : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
      B * rowSPi ν Ψ (SpecialLinearGroup.toGL g) =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * B) :
    ∃ c0 : extension (ν : k), ∀ w : Fin 4 → k,
      (B : Matrix (Fin 4) (Fin 4) k) *ᵥ w = Ψ (c0 • Ψ.symm w) := by
  have hinj : Function.Injective (rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k)) := by
    intro v v' h
    have h1 : (B : Matrix (Fin 4) (Fin 4) k) *ᵥ Ψ v =
        (B : Matrix (Fin 4) (Fin 4) k) *ᵥ Ψ v' := by
      have := congrArg Ψ h
      simpa only [rowSTrans_apply, LinearEquiv.apply_symm_apply] using this
    have h2 := congrArg (fun u => ((B⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ u) h1
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h2
    exact Ψ.injective h2
  have hup : ∀ x : extension (ν : k), ∃ c : k, ∀ v : Fin 2 → extension (ν : k),
      rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) ![v 0 + x * v 1, v 1] =
        c • ![rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 0 +
          x * rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 1,
          rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 1] := by
    intro x
    obtain ⟨c, hc⟩ := hB (upperSL x)
    refine ⟨c, fun v => ?_⟩
    have := transport_apply ν Ψ B _ c hc v
    rw [upperSL_mulVec, upperSL_mulVec] at this
    simpa only [rowSTrans_apply] using this
  have hlo : ∀ x : extension (ν : k), ∃ c : k, ∀ v : Fin 2 → extension (ν : k),
      rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) ![v 0, x * v 0 + v 1] =
        c • ![rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 0,
          x * rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 0 +
          rowSTrans ν Ψ (B : Matrix (Fin 4) (Fin 4) k) v 1] := by
    intro x
    obtain ⟨c, hc⟩ := hB (lowerSL x)
    refine ⟨c, fun v => ?_⟩
    have := transport_apply ν Ψ B _ c hc v
    rw [lowerSL_mulVec, lowerSL_mulVec] at this
    simpa only [rowSTrans_apply] using this
  obtain ⟨c0, hc0⟩ := commutant_V _ hinj hup hlo
  refine ⟨c0, fun w => ?_⟩
  have h1 := hc0 (Ψ.symm w)
  rw [rowSTrans_apply, LinearEquiv.apply_symm_apply] at h1
  apply Ψ.symm.injective
  rw [LinearEquiv.symm_apply_apply, h1]
  refine vec2_ext ?_ ?_ <;> simp

end Normalizer

end RowSComm

section Commutant

variable {k : Type} [Field k] (ν : kˣ)
  (Ψ : (Fin 2 → extension (ν : k)) ≃ₗ[k] (Fin 4 → k))

theorem rowS_commutant (hν : ¬ IsSquare (ν : k)) (h2 : (2 : k) ≠ 0) (B : GL (Fin 4) k)
    (hB : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : k)), ∃ c : kˣ,
      B * rowSPi ν Ψ (SpecialLinearGroup.toGL g) =
        GeneralLinearGroup.scalar (Fin 4) c * rowSPi ν Ψ (SpecialLinearGroup.toGL g) * B)
    (hB2 : ∃ c : kˣ, B ^ 2 = GeneralLinearGroup.scalar (Fin 4) c) :
    ∃ c : kˣ, B = GeneralLinearGroup.scalar (Fin 4) c ∨
      B = GeneralLinearGroup.scalar (Fin 4) c * rowSU ν Ψ := by
  have : Nontrivial (extension (ν : k)) := (extension_isField (ν : k) hν).nontrivial
  obtain ⟨c0, hc0⟩ := RowSComm.exists_mul_of_normalizes ν Ψ B hB
  obtain ⟨c, hc⟩ := hB2
  have hsq : c0 * c0 = algebraMap k (extension (ν : k)) (c : k) := by
    have h1 : ∀ w : Fin 4 → k, (B : Matrix (Fin 4) (Fin 4) k) *ᵥ
        ((B : Matrix (Fin 4) (Fin 4) k) *ᵥ w) = (c : k) • w := by
      intro w
      rw [mulVec_mulVec, ← Units.val_mul, ← sq, hc, RowSComm.gl_scalar_mulVec]
    set u : Fin 2 → extension (ν : k) := fun _ => 1 with hu
    have h2' := h1 (Ψ u)
    simp only [hc0, LinearEquiv.symm_apply_apply] at h2'
    have h3 : c0 • c0 • u = (c : k) • u := by
      apply Ψ.injective
      rw [h2', map_smul]
    have h4 := congrFun h3 0
    simpa [Algebra.smul_def, hu] using h4
  obtain ⟨x, hx | hx⟩ := RowSComm.coord_cases ν h2 c hsq
  · refine ⟨x, Or.inl ?_⟩
    apply eq_of_mulVec_eq
    intro w
    rw [hc0, RowSComm.gl_scalar_mulVec, hx, algebraMap_smul, map_smul,
      LinearEquiv.apply_symm_apply]
  · refine ⟨x, Or.inr ?_⟩
    apply eq_of_mulVec_eq
    intro w
    rw [hc0, Units.val_mul, ← mulVec_mulVec, RowSComm.rowSU_mulVec, RowSComm.gl_scalar_mulVec, hx,
      mul_smul, algebraMap_smul, map_smul]

end Commutant

end CFSG.GH74.GLS.IVK
