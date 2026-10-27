module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4UMem

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem diagonal_unitary (h : UnitaryFieldData p f K) {n : ℕ} (v : Fin n → K)
    (hv : ∀ i, v i ^ (p ^ f + 1) = 1) :
    ((Matrix.diagonal v).map h.bar)ᵀ * Matrix.diagonal v = 1 := by
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Function.comp, Pi.mul_apply, Pi.one_apply, h.bar_apply]
  rw [← pow_succ]
  exact hv i

theorem diagHomU_injective (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    Function.Injective (diagHomU h hdiv) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have hd' : diagUnit d.1 = 1 := congrArg Subtype.val hd
  apply Subtype.ext
  funext i
  have h1 := congrFun (congrFun (congrArg (fun u : GL (Fin 4) K =>
    (u : Matrix (Fin 4) (Fin 4) K)) hd') i) i
  have h2 : ((d.1 i : Kˣ) : K) = 1 := by
    rw [diagUnit_val] at h1
    simpa [diagM] using h1
  exact Units.ext h2

@[expose] def DiagSU (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    Subgroup (unitarySU p f K 4) :=
  (diagHomU h hdiv).range

theorem card_DiagSU_le [Finite K] (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : Nat.card (DiagSU h hdiv) ≤ 27 := by
  have hn := Nat.card_congr (MonoidHom.ofInjective (diagHomU_injective h hdiv)).symm.toEquiv
  rw [DiagSU, hn]
  exact card_dGroup_le K (card_mu3 K hζ)

@[expose] def F0U (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    Subgroup (unitarySU p f K 4) :=
  (F0d K).map (diagHomU h hdiv)

theorem card_F0U (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : Nat.card (F0U h hdiv) = 9 := by
  rw [F0U, Subgroup.card_map_of_injective (diagHomU_injective h hdiv), card_F0d K hζ]

theorem F0U_le_DiagSU (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) :
    F0U h hdiv ≤ DiagSU h hdiv :=
  Subgroup.map_le_range _ _

theorem dGroup_pow_three (d : dGroup K) : d ^ 3 = 1 := by
  apply Subtype.ext
  funext i
  have hi : (d.1 i) ^ 3 = 1 := Units.ext (by simpa using (mem_mu3 K).mp (d.2.1 i))
  simpa using hi

theorem F0U_pow_three (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1)
    {x : unitarySU p f K 4} (hx : x ∈ F0U h hdiv) : x ^ 3 = 1 := by
  obtain ⟨d, _, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow, dGroup_pow_three, map_one]

theorem zmu_mul_sq {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : ζ * ζ ^ 2 = 1 := by
  rw [← pow_succ']
  exact hζ.pow_eq_one

@[expose] def tEltU (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : unitarySU p f K 4 :=
  diagHomU h hdiv (Φ0 K (zmu K hζ, zmu K hζ ^ 2))

theorem tEltU_mem (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : tEltU h hdiv hζ ∈ F0U h hdiv :=
  Subgroup.mem_map_of_mem _ (Φ0_mem_F0d K _)

theorem tEltU_matrix (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) :
    (((tEltU h hdiv hζ : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![1, 1, ζ, ζ ^ 2] := by
  have hz : ζ * ζ ^ 2 = 1 := zmu_mul_sq hζ
  unfold tEltU
  rw [show ((diagHomU h hdiv (Φ0 K (zmu K hζ, zmu K hζ ^ 2)) : unitarySU p f K 4) :
      GL (Fin 4) K) = diagUnit (Φ0 K (zmu K hζ, zmu K hζ ^ 2)).1 from rfl, diagUnit_val]
  unfold diagM
  congr 1
  funext i
  fin_cases i <;> simp [Φ0, zmu, hz]

theorem pow_succ_of_cube {Q : ℕ} (hdiv : 3 ∣ Q + 1) {c : K} (hc : c ^ 3 = 1) :
    c ^ (Q + 1) = 1 := by
  obtain ⟨m, hm⟩ := hdiv
  rw [hm, pow_mul, hc, one_pow]

theorem zeta_ne_zero {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : ζ ≠ 0 :=
  hζ.ne_zero (by norm_num)

@[expose] def A0GL {ζ : K} (hζ : IsPrimitiveRoot ζ 3) : GL (Fin 2) K :=
  ⟨Matrix.diagonal ![ζ, ζ ^ 2], Matrix.diagonal ![ζ⁻¹, (ζ ^ 2)⁻¹], by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [zeta_ne_zero hζ],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [zeta_ne_zero hζ]⟩

@[expose] def A0U (h : UnitaryFieldData p f K) (hdiv : 3 ∣ p ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) : unitarySU p f K 2 :=
  ⟨A0GL hζ, by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · show (Matrix.diagonal ![ζ, ζ ^ 2]).det = 1
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simpa using zmu_mul_sq hζ
    · show ((Matrix.diagonal ![ζ, ζ ^ 2]).map h.bar)ᵀ * Matrix.diagonal ![ζ, ζ ^ 2] = 1
      apply diagonal_unitary h
      intro i
      fin_cases i
      · simpa using pow_succ_of_cube hdiv hζ.pow_eq_one
      · have h6 : (ζ ^ 2) ^ 3 = 1 := by
          calc (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 := by ring
            _ = 1 := by rw [hζ.pow_eq_one, one_pow]
        simpa using pow_succ_of_cube hdiv h6⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
