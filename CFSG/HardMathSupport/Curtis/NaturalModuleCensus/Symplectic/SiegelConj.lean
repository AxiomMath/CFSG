module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelFrame
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Frame

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem exists_frame_conj (v : StatedSp 2 K) {p : ℕ} (hvp : v ^ p = 1) (hp : (p : K) ≠ 0)
    {ζ : K} (hζp : ζ ^ p = 1) (hζ2 : ζ ^ 2 ≠ 1) {a a' : Fin 2 ⊕ Fin 2 → K} (ha : a ≠ 0)
    (ha' : a' ≠ 0) (hMa : spMat v *ᵥ a = ζ • a) (hMa' : spMat v *ᵥ a' = ζ⁻¹ • a')
    (haa' : pairedSympForm K 2 a a' = 0) :
    ∃ (g : StatedSp 2 K) (y : Fin 2 ⊕ Fin 2 → K),
      spMat g *ᵥ Pi.single (Sum.inl 0) 1 = a ∧ spMat g *ᵥ Pi.single (Sum.inl 1) 1 = y ∧
        pairedSympForm K 2 y a' = 1 ∧
        spMat v * spMat g = spMat g * diagonal (Sum.elim (fun _ => ζ) fun _ => ζ⁻¹) := by
  have hζinv2 : ζ⁻¹ ^ 2 ≠ 1 := by
    rw [inv_pow]; exact fun h => hζ2 (inv_eq_one.1 h)
  have hζζ : ζ * ζ ≠ 1 := by rw [← sq]; exact hζ2
  have hζζ' : ζ⁻¹ * ζ⁻¹ ≠ 1 := by rw [← sq]; exact hζinv2
  have hζinvp : ζ⁻¹ ^ p = 1 := by rw [inv_pow, hζp, inv_one]
  obtain ⟨z0, hz0⟩ := exists_dual ha'
  obtain ⟨y, hMy, hya'⟩ := exists_eigen_dual v hvp hp hζp (a := a') (z := z0)
    (by rw [hMa']) hz0
  obtain ⟨z1, hz1⟩ := exists_dual ha
  obtain ⟨y1, hMy1, hy1a⟩ := exists_eigen_dual v hvp hp hζinvp (a := a) (z := z1)
    (by rw [hMa, inv_inv]) hz1
  set μ := pairedSympForm K 2 y y1 with hμ
  set y'' := -y1 + μ • a' with hy''
  have hMy'' : spMat v *ᵥ y'' = ζ⁻¹ • y'' := by
    rw [hy'', mulVec_add, mulVec_neg, mulVec_smul, hMy1, hMa']
    simp [smul_comm μ ζ⁻¹]
  have hay : pairedSympForm K 2 a y = 0 := psf_eq_zero_of_eigen v hζζ hMa hMy
  have hay'' : pairedSympForm K 2 a y'' = 1 := by
    rw [hy'', map_add, map_neg, map_smul, haa', smul_eq_mul, mul_zero, add_zero,
      psf_neg_comm a y1, hy1a, neg_neg]
  have hyy'' : pairedSympForm K 2 y y'' = 0 := by
    rw [hy'', map_add, map_neg, map_smul, hya', smul_eq_mul, mul_one, ← hμ]; ring
  have hy''a' : pairedSympForm K 2 y'' a' = 0 := psf_eq_zero_of_eigen v hζζ' hMy'' hMa'
  set c : Fin 2 ⊕ Fin 2 → (Fin 2 ⊕ Fin 2 → K) := Sum.elim ![a, y] ![y'', a'] with hc
  have hgram : ∀ x y, pairedSympForm K 2 (c x) (c y) = (fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0) x y := by
    have s1 := pairedSympForm_self (k := K) (m := 2) a
    have s2 := pairedSympForm_self (k := K) (m := 2) y
    have s3 := pairedSympForm_self (k := K) (m := 2) y''
    have s4 := pairedSympForm_self (k := K) (m := 2) a'
    have hya : pairedSympForm K 2 y a = 0 := by rw [psf_neg_comm, hay, neg_zero]
    have hy''a : pairedSympForm K 2 y'' a = -1 := by rw [psf_neg_comm, hay'']
    have hy''y : pairedSympForm K 2 y'' y = 0 := by rw [psf_neg_comm, hyy'', neg_zero]
    have ha'a : pairedSympForm K 2 a' a = 0 := by rw [psf_neg_comm, haa', neg_zero]
    have ha'y : pairedSympForm K 2 a' y = -1 := by rw [psf_neg_comm, hya']
    have ha'y'' : pairedSympForm K 2 a' y'' = 0 := by rw [psf_neg_comm, hy''a', neg_zero]
    intro x y
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hc, haa', hay, hay'', hyy'', hya', hy''a', hya, hy''a, hy''y, ha'a, ha'y, ha'y'',
        s1, s2, s3, s4]
  obtain ⟨g, hg⟩ := exists_statedSp_of_frame c hgram
  refine ⟨g, y, ?_, ?_, hya', ?_⟩
  · simpa [hc] using hg (Sum.inl 0)
  · simpa [hc] using hg (Sum.inl 1)
  · apply Matrix.ext_of_mulVec_single
    intro x
    have hD : ∀ x : Fin 2 ⊕ Fin 2, diagonal (Sum.elim (fun _ : Fin 2 => ζ) fun _ => ζ⁻¹) *ᵥ
        (Pi.single x 1 : Fin 2 ⊕ Fin 2 → K) =
        (Sum.elim (fun _ : Fin 2 => ζ) (fun _ => ζ⁻¹) x) • (Pi.single x 1 : Fin 2 ⊕ Fin 2 → K) := by
      intro x
      rw [diagonal_mulVec_single, mul_one, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg x, hD, mulVec_smul, hg x]
    rcases x with i | i <;> fin_cases i <;> simp [hc, hMa, hMy, hMy'', hMa']

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
