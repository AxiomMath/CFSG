module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowSupport
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

section Hyp

variable {r ε : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem exists_hypSU_hom (h : UnitaryFieldData p f K) {E : Matrix (HypIndex r ε) κ K}
    {Gi : Matrix κ κ K} (hGi : Gi * ((E.map h.bar)ᵀ * hypGram r ε K * E) = 1)
    (hGi' : ((E.map h.bar)ᵀ * hypGram r ε K * E) * Gi = 1) {H : Type*} [Group H]
    (Y : H →* Matrix κ κ K)
    (hY : ∀ x, ((Y x).map h.bar)ᵀ * ((E.map h.bar)ᵀ * hypGram r ε K * E) * Y x =
      (E.map h.bar)ᵀ * hypGram r ε K * E)
    (hYd : ∀ x, (Y x).det = 1) :
    ∃ ψ : H →* hypSU h r ε, ∀ x, ((ψ x : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
        suppMat E (Gi * (E.map h.bar)ᵀ * hypGram r ε K) (Y x) := by
  have hFE : Gi * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [← hGi]
    simp only [Matrix.mul_assoc]
  set Φ : H →* GL (HypIndex r ε) K := ((suppHom hFE).comp Y).toHomUnits with hΦ
  have hΦx : ∀ x, ((Φ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      suppMat E (Gi * (E.map h.bar)ᵀ * hypGram r ε K) (Y x) := fun x => by
    rw [hΦ, MonoidHom.coe_toHomUnits]
    rfl
  have hmem : ∀ x, Φ x ∈ hypSU h r ε := fun x => by
    rw [mem_hypSU, hΦx]
    exact ⟨suppMat_isometry h.bar_bar (hypGram_conjTranspose h) hGi hGi' (hY x),
      by rw [det_suppMat hFE, hYd]⟩
  exact ⟨Φ.codRestrict _ hmem, fun x => hΦx x⟩

theorem exists_eq_smul_one_of_mem_hypScalars {h : UnitaryFieldData p f K} {g : hypSU h r ε}
    (hg : g ∈ hypScalars h r ε) :
    ∃ c : K, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = c • 1 := by
  obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hg
  exact ⟨c, by rw [hc, GeneralLinearGroup.coe_scalar, scalar_apply, smul_one_eq_diagonal]⟩

theorem even_card_range_hypProj_comp {h : UnitaryFieldData p f K} {H : Type*} [Group H]
    [Finite H] (ψ : H →* hypSU h r ε) {x : H} (hx4 : x ^ 4 = 1)
    (hxs : ∀ c : K, ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) ≠
      c • 1) :
    Even (Nat.card ((hypProj h r ε).comp ψ).range) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y : ((hypProj h r ε).comp ψ).range := ⟨_, x, rfl⟩ with hy
  have hy1 : y ≠ 1 := by
    intro h1
    have h2 : hypProj h r ε (ψ x) = 1 := congrArg Subtype.val h1
    rw [← MonoidHom.mem_ker, ker_hypProj] at h2
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_mem_hypScalars h2
    exact hxs c hc
  have hy4 : y ^ 4 = 1 := Subtype.ext (by
    change hypProj h r ε (ψ x) ^ 4 = 1
    rw [← map_pow, ← map_pow, hx4, map_one, map_one])
  have hdvd : orderOf y ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hy4
  obtain ⟨k, hk, hyk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hyk
    exact hy1 hyk
  have h2 : 2 ∣ orderOf y := by
    rw [hyk]
    exact dvd_pow_self 2 hk0
  exact even_iff_two_dvd.mpr (h2.trans (orderOf_dvd_natCard y))

theorem semilinearAutHom_hypProj_of_mul_eq (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) {A : GL (HypIndex r ε) K} {σ : K ≃+* K}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε) (g : hypSU h r ε)
    (hg : A * glAut σ (g : GL (HypIndex r ε) K) = g * A) :
    semilinearAutHom h hr hε ⟨_, hx⟩ (hypProj h r ε g) = hypProj h r ε g := by
  rw [semilinearAutHom_apply]
  congr 1
  apply Subtype.ext
  change A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ = g
  rw [hg, mul_inv_cancel_right]

theorem glAut_refl {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K) :
    glAut (RingEquiv.refl K) g = g :=
  congrArg (fun φ : MulAut (GL ι K) => φ g) (map_one glAut)

theorem coe_glAut_of_bar {ι : Type} [Fintype ι] [DecidableEq ι] (h : UnitaryFieldData p f K)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c) (g : GL ι K) :
    ((glAut σ g : GL ι K) : Matrix ι ι K) = (g : Matrix ι ι K).map h.bar := by
  rw [coe_glAut]
  exact Matrix.ext fun i j => hσ _

end Hyp

section Plane

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def planeHom :
    SpecialLinearGroup (Fin 2) h.fixedField →* Matrix (Fin 2) (Fin 2) K :=
  (Units.coeHom _).comp
    (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map h.fixedField.subtype))

theorem planeHom_apply (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    planeHom h B = (B : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype :=
  rfl

theorem map_planeHom (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    (planeHom h B).map h.bar = planeHom h B := by
  ext i j
  rw [planeHom_apply, map_apply, map_apply]
  exact h.mem_fixedField.mp ((B : Matrix (Fin 2) (Fin 2) h.fixedField) i j).2

theorem det_planeHom (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    (planeHom h B).det = 1 := by
  rw [planeHom_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, B.2, map_one]

theorem transpose_mul_quatI_mul (M : Matrix (Fin 2) (Fin 2) K) :
    Mᵀ * QuaternionMatrices.quatI K * M = M.det • QuaternionMatrices.quatI K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuaternionMatrices.quatI, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem planeHom_isometry (g : K) (B : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((planeHom h B).map h.bar)ᵀ * (g • QuaternionMatrices.quatI K) * planeHom h B =
      g • QuaternionMatrices.quatI K := by
  rw [map_planeHom, Matrix.mul_smul, Matrix.smul_mul, transpose_mul_quatI_mul, det_planeHom,
    one_smul]

theorem planeHom_slQuatI :
    planeHom h (QuaternionMatrices.slQuatI h.fixedField) = QuaternionMatrices.quatI K := by
  rw [planeHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuaternionMatrices.slQuatI, QuaternionMatrices.quatI]

theorem quatI_ne_smul_one (c : K) : QuaternionMatrices.quatI K ≠ c • 1 := by
  intro h1
  have := congrFun (congrFun h1 0) 1
  simp [QuaternionMatrices.quatI] at this

end Plane

section Pair

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def pairHom :
    SpecialLinearGroup (Fin 2) K →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K where
  toFun B := fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0
    ((adjugate (B : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ
  map_one' := by simp [fromBlocks_one]
  map_mul' B B' := by
    simp [fromBlocks_multiply, adjugate_mul_distrib, Matrix.map_mul, transpose_mul]

theorem pairHom_apply (B : SpecialLinearGroup (Fin 2) K) :
    pairHom h B = fromBlocks (B : Matrix (Fin 2) (Fin 2) K) 0 0
      ((adjugate (B : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ :=
  rfl

theorem det_pairHom (B : SpecialLinearGroup (Fin 2) K) : (pairHom h B).det = 1 := by
  rw [pairHom_apply, det_fromBlocks_zero₂₁, det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, det_adjugate, B.2, one_pow, map_one, one_mul]

theorem pairHom_isometry (B : SpecialLinearGroup (Fin 2) K) :
    ((pairHom h B).map h.bar)ᵀ * fromBlocks 0 1 1 0 * pairHom h B = fromBlocks 0 1 1 0 := by
  have hBB' : adjugate (B : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [adjugate_mul, B.2, one_smul]
  have h1 : ((B : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
      ((adjugate (B : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ = 1 := by
    rw [← transpose_mul, ← Matrix.map_mul, hBB', Matrix.map_one _ (map_zero _) (map_one _),
      transpose_one]
  rw [pairHom_apply, fromBlocks_map, transpose_map, map_map_of_involutive h.bar_bar,
    fromBlocks_transpose, transpose_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [h1, hBB']

theorem pairHom_slQuatI_ne_smul_one (c : K) :
    pairHom h (QuaternionMatrices.slQuatI K) ≠ c • 1 := by
  intro h1
  rw [pairHom_apply] at h1
  have := congrFun (congrFun h1 (.inl 0)) (.inl 1)
  simp [QuaternionMatrices.slQuatI, QuaternionMatrices.quatI] at this

theorem pairHom_comm (l : K) (B : SpecialLinearGroup (Fin 2) K) :
    fromBlocks (l • 1) 0 0 ((-l) • 1) * pairHom h B =
      pairHom h B * fromBlocks (l • 1) 0 0 ((-l) • 1) := by
  rw [pairHom_apply, fromBlocks_multiply, fromBlocks_multiply]
  simp

end Pair

end CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
