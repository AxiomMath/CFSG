module

public import CFSG.LieType.SemisimpleCentralizers.OrderThree.Adjoint

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_orthonormal_cols {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {d : ℕ}
    {P : Matrix (Fin d) (Fin d) K} (hP : P * P = P) (hPa : (P.map h.bar)ᵀ = P) :
    ∃ (k : ℕ) (U : Matrix (Fin d) (Fin k) K), (U.map h.bar)ᵀ * U = 1 ∧ U * (U.map h.bar)ᵀ = P := by
  classical
  let B0 : (Fin d → K) →ₛₗ[h.bar] (Fin d → K) →ₗ[K] K := gramForm h 1
  let W : Submodule K (Fin d → K) := LinearMap.range (Matrix.toLin' P)
  have hPw : ∀ w : Fin d → K, w ∈ W → P *ᵥ w = w := by
    rintro w ⟨z, rfl⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hP]
  have hsymm : B0.IsSymm := by
    have hG : ((1 : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ = 1 := by
      rw [Matrix.map_one h.bar (map_zero h.bar) (map_one h.bar), Matrix.transpose_one]
    have h' := gramForm_isSymm h (G := 1) hG
    simpa only [B0] using h'
  have hsep : B0.SeparatingLeft := by
    have h' := gramForm_separatingLeft h (G := 1)
      (by simp : (1 : Matrix (Fin d) (Fin d) K).det ≠ 0)
    simpa only [B0] using h'
  have hWsep : (B0.domRestrict₁₂ W W).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply hsep x.1
    intro v
    have hPv : P *ᵥ v ∈ W := ⟨v, by rw [Matrix.toLin'_apply]⟩
    have hxPv : B0 x.1 (P *ᵥ v) = 0 := by
      simpa only [LinearMap.domRestrict₁₂_apply] using hx ⟨P *ᵥ v, hPv⟩
    calc B0 x.1 v = B0 (P *ᵥ x.1) v := by rw [hPw x.1 x.2]
      _ = B0 x.1 ((P.map h.bar)ᵀ *ᵥ v) := by
            simpa only [B0] using gramForm_one_mulVec_left h P x.1 v
      _ = B0 x.1 (P *ᵥ v) := by rw [hPa]
      _ = 0 := hxPv
  have hB : (B0.domRestrict₁₂ W W).IsSymm := hsymm.domRestrict W
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (B := B0.domRestrict₁₂ W W) hB hWsep
  let U : Matrix (Fin d) (Fin (Module.finrank K W)) K :=
    Matrix.of fun i j => ((e j : W) : Fin d → K) i
  have hcol : ∀ j : Fin (Module.finrank K W),
      U *ᵥ Pi.single j 1 = ((e j : W) : Fin d → K) := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext x
    rfl
  have hUc : ∀ c : Fin (Module.finrank K W) → K,
      U *ᵥ c = ((∑ i, c i • e i : W) : Fin d → K) := by
    intro c
    ext x
    simp only [Matrix.mulVec_apply_eq_sum, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, U, Matrix.of_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hUstarU : (U.map h.bar)ᵀ * U = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply]
    rw [show (∑ x, h.bar (U x i) * U x j)
        = gramForm h 1 ((e i : W) : Fin d → K) ((e j : W) : Fin d → K) from by
      rw [gramForm_apply, Matrix.one_mulVec]
      simp only [dotProduct, U, Matrix.of_apply]]
    simpa only [B0, LinearMap.domRestrict₁₂_apply] using he i j
  have hsum_repr : ∀ y : W, (y : Fin d → K) = ∑ i, e.repr y i • ((e i : W) : Fin d → K) := by
    intro y
    have h := congrArg (fun z : W => (z : Fin d → K)) (e.sum_repr y)
    rw [← h]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
  have hproj : ∀ v : Fin d → K, (U * (U.map h.bar)ᵀ) *ᵥ v = P *ᵥ v := by
    intro v
    let c : Fin (Module.finrank K W) → K := (U.map h.bar)ᵀ *ᵥ v
    have hxmem : U *ᵥ c ∈ W := by
      rw [hUc c]
      exact (∑ i, c i • e i : W).2
    have hPmem : P *ᵥ v ∈ W := ⟨v, by rw [Matrix.toLin'_apply]⟩
    have hd : U *ᵥ c - P *ᵥ v = 0 := by
      refine Subtype.ext_iff.mp (hWsep ⟨U *ᵥ c - P *ᵥ v, W.sub_mem hxmem hPmem⟩ ?_)
      intro y
      show B0 (U *ᵥ c - P *ᵥ v) (y : Fin d → K) = 0
      have hdi : ∀ i, B0 ((e i : W) : Fin d → K) (U *ᵥ c - P *ᵥ v) = 0 := by
        intro i
        have ha : B0 ((e i : W) : Fin d → K) (U *ᵥ c) = B0 ((e i : W) : Fin d → K) v := by
          calc B0 ((e i : W) : Fin d → K) (U *ᵥ c)
              = B0 (U *ᵥ Pi.single i 1) (U *ᵥ c) := by rw [← hcol i]
            _ = gramForm h ((U.map h.bar)ᵀ * 1 * U) (Pi.single i 1) c :=
                  gramForm_mulVec h 1 U (Pi.single i 1) c
            _ = gramForm h 1 (Pi.single i 1) c := by rw [Matrix.mul_one, hUstarU]
            _ = gramForm h 1 (U *ᵥ Pi.single i 1) v :=
                  (gramForm_one_mulVec_left h U (Pi.single i 1) v).symm
            _ = B0 ((e i : W) : Fin d → K) v := by rw [hcol i]
        have hb : B0 ((e i : W) : Fin d → K) (P *ᵥ v) = B0 ((e i : W) : Fin d → K) v := by
          calc B0 ((e i : W) : Fin d → K) (P *ᵥ v)
              = B0 ((e i : W) : Fin d → K) ((P.map h.bar)ᵀ *ᵥ v) := by rw [hPa]
            _ = B0 (P *ᵥ ((e i : W) : Fin d → K)) v :=
                  (gramForm_one_mulVec_left h P ((e i : W) : Fin d → K) v).symm
            _ = B0 ((e i : W) : Fin d → K) v := by rw [hPw _ (e i).2]
        rw [map_sub, ha, hb, sub_self]
      have hdie : ∀ i, B0 (U *ᵥ c - P *ᵥ v) ((e i : W) : Fin d → K) = 0 := by
        intro i
        rw [← hsymm.eq ((e i : W) : Fin d → K) (U *ᵥ c - P *ᵥ v), hdi i, map_zero h.bar]
      rw [hsum_repr y]
      simp only [map_sum, map_smul, RingHom.id_apply, hdie, smul_zero,
        Finset.sum_const_zero]
    have h1 : (U * (U.map h.bar)ᵀ) *ᵥ v = U *ᵥ c := by rw [← Matrix.mulVec_mulVec]
    rw [h1]
    exact sub_eq_zero.mp hd
  have hQP : U * (U.map h.bar)ᵀ = P :=
    Matrix.ext_of_mulVec_single fun i => hproj (Pi.single i 1)
  exact ⟨Module.finrank K W, U, hUstarU, hQP⟩

end CFSG.LieType.SemisimpleCentralizers.OrderThree
