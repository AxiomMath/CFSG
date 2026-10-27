module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldArith
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFieldMat

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField

open Matrix

@[expose] def fixSub {k : Type} [Field k] (τ : k ≃+* k) : Subfield k :=
  (RingHom.id k).eqLocusField (τ : k →+* k)

theorem mem_fixSub {k : Type} [Field k] {τ : k ≃+* k} {x : k} : x ∈ fixSub τ ↔ τ x = x := by
  simp [fixSub, RingHom.mem_eqLocusField, eq_comm]

variable {k : Type} [Field k] [Finite k]

namespace FrobData

variable (F : FrobData k)

theorem apply_apply_apply (x : k) : F.τ (F.τ (F.τ x)) = x := by
  have : Fintype k := Fintype.ofFinite k
  rw [F.apply_eq, F.apply_eq, F.apply_eq, ← pow_mul, ← pow_mul,
    show F.r * (F.r * F.r) = F.r ^ 3 by ring, F.card_eq, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem exists_unit_smul_fixed (g : Matrix (Fin 3) (Fin 3) k) (hg : g ≠ 0) (l : kˣ)
    (hl : g.map F.τ = (l : k) • g) : ∃ m : kˣ, ((m : k) • g).map F.τ = (m : k) • g := by
  have hmap : ∀ (a : k) (N : Matrix (Fin 3) (Fin 3) k),
      (a • N).map F.τ = F.τ a • N.map F.τ := fun a N => by ext i j; simp
  have h3 : ((g.map F.τ).map F.τ).map F.τ = g := by
    ext i j
    simp [F.apply_apply_apply]
  have h1 : (g.map F.τ).map F.τ = (F.τ l * l) • g := by
    rw [hl, hmap, hl, smul_smul]
  have h2 : g = (F.τ (F.τ l) * F.τ l * l) • g := by
    conv_lhs => rw [← h3]
    rw [h1, hmap, hl, smul_smul, map_mul]
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra hcon
    exact hg (by ext i j; by_contra hij; exact hcon ⟨i, j, hij⟩)
  have hnorm : (l : k) * F.τ l * F.τ (F.τ l) = 1 := by
    have h4 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h4
    have h5 : (F.τ (F.τ l) * F.τ l * l) * g i j = 1 * g i j := by rw [one_mul]; exact h4.symm
    have := mul_right_cancel₀ hij h5
    linear_combination this
  obtain ⟨m, hm⟩ := F.exists_unit_apply_eq l hnorm
  refine ⟨m, ?_⟩
  rw [hmap, hl, smul_smul, hm, mul_assoc, inv_mul_cancel₀ l.ne_zero, mul_one]

theorem exists_fixed_cube (h3 : 3 ∣ Nat.card k - 1) (y : GL (Fin 3) k)
    (hy : ∀ i j, F.τ ((y : Matrix (Fin 3) (Fin 3) k) i j) = (y : Matrix (Fin 3) (Fin 3) k) i j) :
    ∃ c : kˣ, (c : k) ^ 3 = (y : Matrix (Fin 3) (Fin 3) k).det := by
  have hdet : F.τ ((y : Matrix (Fin 3) (Fin 3) k).det) = (y : Matrix (Fin 3) (Fin 3) k).det := by
    have h1 := RingHom.map_det (F.τ : k →+* k) (y : Matrix (Fin 3) (Fin 3) k)
    have h2 : (F.τ : k →+* k).mapMatrix (y : Matrix (Fin 3) (Fin 3) k) =
        (y : Matrix (Fin 3) (Fin 3) k) := by
      ext i j
      exact hy i j
    rw [h2] at h1
    exact h1
  have hne : (y : Matrix (Fin 3) (Fin 3) k).det ≠ 0 := by
    simpa [Matrix.GeneralLinearGroup.det] using (Matrix.GeneralLinearGroup.det y).ne_zero
  obtain ⟨c, hc⟩ := F.exists_unit_cube_of_apply_eq h3
    (x := Units.mk0 _ hne) (by simpa using hdet)
  exact ⟨c, by simpa using congrArg Units.val hc⟩

theorem exists_fixed_frame (h3 : 3 ∣ Nat.card k - 1) (y : GL (Fin 3) k)
    (hy : ∀ i j, F.τ ((y : Matrix (Fin 3) (Fin 3) k) i j) = (y : Matrix (Fin 3) (Fin 3) k) i j)
    {c : kˣ} (hc : (c : k) ^ 3 = (y : Matrix (Fin 3) (Fin 3) k).det) {c' : k}
    (hy3 : (y : Matrix (Fin 3) (Fin 3) k) ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) k))
    (hlift : (y : Matrix (Fin 3) (Fin 3) k) ^ 3 = (c : k) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) k) →
      F.τ (c : k) = c) :
    ∃ (P : GL (Fin 3) k) (u : Fin 3 → k),
      (∀ i j, F.τ ((P : Matrix (Fin 3) (Fin 3) k) i j) = (P : Matrix (Fin 3) (Fin 3) k) i j) ∧
      ((P⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (y : Matrix (Fin 3) (Fin 3) k) *
        (P : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal u := by
  set Y : Matrix (Fin 3) (Fin 3) k := (y : Matrix (Fin 3) (Fin 3) k) with hY
  have hyk : ∀ i j, Y i j ∈ fixSub F.τ := fun i j => mem_fixSub.2 (hy i j)
  have hfY : (F.τ : k →+* k).mapMatrix Y = Y := by
    ext i j
    exact hy i j
  have hc'fix : F.τ c' = c' := by
    have h1 : (F.τ : k →+* k).mapMatrix (Y ^ 3) = Y ^ 3 := by rw [map_pow, hfY]
    rw [hy3] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h2
  have hdet0 : Y.det ≠ 0 := by
    simpa [Matrix.GeneralLinearGroup.det] using (Matrix.GeneralLinearGroup.det y).ne_zero
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hy3
    rw [zero_smul, Matrix.det_pow] at h1
    simp at h1
    exact hdet0 h1
  obtain ⟨ε, hε, hε3⟩ : ∃ ε ∈ fixSub F.τ, ε ^ 3 = c' := by
    rcases exists_cube_root_or_det_eq_of_subfield (fixSub F.τ) Y hyk (mem_fixSub.2 hc'fix) hy3
      with h | h
    · exact h
    · have hY3 : Y ^ 3 = (c : k) ^ 3 • (1 : Matrix (Fin 3) (Fin 3) k) := by rw [hy3, hc, h]
      exact ⟨c, mem_fixSub.2 (hlift hY3), by rw [hc, h]⟩
  have hε0 : ε ≠ 0 := by
    rintro rfl
    apply hc'0
    rw [← hε3]
    norm_num
  obtain ⟨ω, hω3, hω1, hωfix⟩ := F.exists_omega h3
  have hω3' : (ω : k) ^ 3 = 1 := by
    simpa [← Units.val_pow_eq_pow_val] using congrArg Units.val hω3
  have hω1' : (ω : k) ≠ 1 := fun h => hω1 (Units.ext h)
  obtain ⟨P, u, hP, hPu⟩ := exists_rational_diagonal (fixSub F.τ) Y hyk hε hε0
    (mem_fixSub.2 hωfix) hω3' hω1' (by rw [hε3]; exact hy3)
  exact ⟨P, u, fun i j => mem_fixSub.1 (hP i j), hPu⟩

end FrobData

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftField
