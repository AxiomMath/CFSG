module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFourCore
public import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_invariant_subspace_of_cube_one (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K} (hg3 : g ^ 3 = 1)
    (hns : ¬ ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    ∃ W : Submodule K (Fin 3 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ v ∈ W, ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) ∈ W := by
  classical
  have h3 := hK.three_ne_zero hq
  have hmat3 : (g : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  obtain ⟨b, hb, heig⟩ := exists_common_eigenbasis hτ hτ1 h3 hmat3 hmat3 rfl
  choose k hk using fun i => (heig i).1
  by_cases hall : ∀ i j, k i = k j
  · exfalso
    apply hns
    refine ⟨τ ^ (k 0 : ℕ), ?_⟩
    apply eq_of_mulVec_eq_of_linearIndependent hb
    intro i
    rw [hk i, hall i 0, Matrix.smul_mulVec, Matrix.one_mulVec]
  · push Not at hall
    obtain ⟨i, j, hij⟩ := hall
    let f : Module.End K (Fin 3 → K) := Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)
    let W : Submodule K (Fin 3 → K) := f.eigenspace (τ ^ (k i : ℕ))
    have hbi : b i ∈ W := by
      rw [Module.End.mem_eigenspace_iff]
      rw [show f (b i) = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i from Matrix.toLin'_apply _ _]
      exact hk i
    refine ⟨W, ?_, ?_, ?_⟩
    · intro hbot
      rw [hbot] at hbi
      exact hb.ne_zero i (by simpa using hbi)
    · intro htop
      apply hns
      refine ⟨τ ^ (k i : ℕ), ?_⟩
      have hf : f = (τ ^ (k i : ℕ)) • LinearMap.id := by
        apply LinearMap.ext
        intro v
        have hv : v ∈ W := htop ▸ Submodule.mem_top
        rwa [Module.End.mem_eigenspace_iff] at hv
      have h2 : Matrix.toLin' ((τ ^ (k i : ℕ)) • (1 : Matrix (Fin 3) (Fin 3) K)) =
          (τ ^ (k i : ℕ)) • LinearMap.id := by
        rw [LinearEquiv.map_smul, Matrix.toLin'_one]
      exact Matrix.toLin'.injective (hf.trans h2.symm)
    · intro v hv
      have hmap : f v ∈ W :=
        (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem f).mp
          (Module.End.eigenspace_mem_invtSubmodule f (τ ^ (k i : ℕ))) v hv
      rwa [show f v = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v from Matrix.toLin'_apply _ _] at hmap

theorem exists_conj_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : Subgroup (GL (Fin 3) K)}
    (hBH : B ≤ glPi π 3 (p ^ f) K) (hZB : zPi π 3 (p ^ f) K ≤ B)
    (hB : ∀ b ∈ B, b ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, ⁅b, c⁆ ∈ zPi π 3 (p ^ f) K)
    (hB9 : (zPi π 3 (p ^ f) K).relIndex B = 9)
    (hno : ∀ b ∈ B, ∀ z ∈ zPi π 3 (p ^ f) K, ∀ g ∈ glPi π 3 (p ^ f) K, ∀ e : Kˣ,
      ((e : K) = τ ∨ (e : K) = τ ^ 2) → g⁻¹ * (b * z) * g ≠ diagE e) :
    ∃ b ∈ B, ∃ z ∈ zPi π 3 (p ^ f) K, ∃ g ∈ glPi π 3 (p ^ f) K,
      g⁻¹ * (b * z) * g = diagTau hτ := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  set Z : Subgroup (GL (Fin 3) K) := zPi π 3 (p ^ f) K with hZdef
  obtain ⟨b, hbB, hbZ, μ, hb3⟩ := exists_cube_split_mem hK hq hτ hτ1 hBH hZB hB hBc hB9
  have hb3Z : b ^ 3 ∈ Z := hB b hbB
  obtain ⟨y, ⟨z, hzZ, hy⟩, hcase⟩ :=
    rank3II_4_10_one hK hq hτ hτ1 (hBH hbB) hbZ hb3Z
  subst hy
  rcases hcase with ⟨⟨g, hg, hgD⟩, -, -⟩ | ⟨⟨g, hg, e, he, hgD⟩, -, -⟩ |
    ⟨hord, hirrx, hirry, hcyc, hcard, w, hw, hwo, hwC, hcent, hcard3⟩
  · exact ⟨b, hbB, z, hzZ, g, hg, hgD⟩
  · exact absurd hgD (hno b hbB z hzZ g hg e he)
  ·
    exfalso
    set s : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) μ with hs
    have hcomm : Commute b s := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ b
    have hg03 : (b * s⁻¹) ^ 3 = 1 := by
      rw [Commute.mul_pow hcomm.inv_right 3, hb3, hs, inv_pow, mul_inv_cancel]
    have hns : ¬ ∃ c : K, ((b * s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
      rintro ⟨c, hc⟩
      apply hbZ
      have hdet : ((b * s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
        ((b * s⁻¹).isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [hc, zero_smul, Matrix.det_zero] at hdet
        exact hdet rfl
      have hbmat : (b : Matrix (Fin 3) (Fin 3) K) =
          (c * (μ : K)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
        calc (b : Matrix (Fin 3) (Fin 3) K)
            = ((b * s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
              rw [← Units.val_mul, show (b * s⁻¹) * s = b from by group]
          _ = (c • (1 : Matrix (Fin 3) (Fin 3) K)) *
                ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by rw [hc]
          _ = (c * (μ : K)) • (1 : Matrix (Fin 3) (Fin 3) K) := by
              rw [hs, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
                ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, smul_smul]
      have hbscalar : b ∈ StatedScalars (Fin 3) K :=
        mem_statedScalars_of_eq_smul hbmat (mul_ne_zero hc0 μ.ne_zero)
      rw [zPi_eq hπ hq' hτ hτ1]
      exact Subgroup.mem_inf.mpr ⟨hBH hbB, hbscalar⟩
    obtain ⟨W, hWbot, hWtop, hWinv⟩ :=
      exists_invariant_subspace_of_cube_one hK hq hτ hτ1 hg03 hns
    obtain ⟨ξ, hξ, hz_eq⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hzZ
    have hglbz : (b * z : GL (Fin 3) K) = (b * s⁻¹) * (s * z) := by group
    have hsz : s * z = GeneralLinearGroup.scalar (Fin 3) (μ * ξ) := by
      rw [← hz_eq, hs, ← map_mul]
    have hmatbz : ((b * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((μ * ξ : Kˣ) : K)) • ((b * s⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hglbz, hsz, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    have hWy : ∀ v ∈ W, ((b * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
      intro v hv
      rw [hmatbz, Matrix.smul_mulVec]
      exact Submodule.smul_mem W _ (hWinv v hv)
    rcases hirry W hWy with h | h
    · exact hWbot h
    · exact hWtop h

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
