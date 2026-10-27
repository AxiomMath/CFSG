module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Escape
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.FixedVector
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.FixedEscape

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

theorem false_of_fixed_vector_flag {r : ℕ} {K : Type} [Field K] {p : ℕ} (hp : (p : K) ≠ 0)
    {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ r) {v : StatedSp r K} (hvp : v ^ p = 1)
    (hfix : ∀ g : StatedSp r K, g * v = v * g → g ∈ SymplecticHigher.flagStabilizer r K I)
    {i : ℕ} (hi : i ∈ I) {a : Fin r ⊕ Fin r → K}
    (haF : a ∈ SymplecticFlag.flag r K i) (ha0 : a ≠ 0) (hva : spMat v *ᵥ a = a) : False := by
  obtain ⟨x0, -⟩ := Function.ne_iff.1 ha0
  obtain ⟨i0, -⟩ : ∃ i : Fin r, True := by
    rcases x0 with i | i
    · exact ⟨i, trivial⟩
    · exact ⟨i, trivial⟩
  obtain ⟨z, hz⟩ := exists_pairedSympForm_eq_one ha0
  obtain ⟨b0, hb0v, hab0⟩ := exists_fixed_dual hvp hp hva hz
  obtain ⟨g, hge, hgf⟩ := exists_statedSp_pair (r := r) (K := K)
    (pairedSympForm_single i0) hab0
  have hginv : ∀ u, spMat g⁻¹ *ᵥ (spMat g *ᵥ u) = u := by
    intro u; rw [mulVec_mulVec, spMat_inv_mul, one_mulVec]
  have hcomm : Commute (g⁻¹ * v * g)
      (SymplecticTorusWeyl.lam i0 (lowerTransvection K)) := by
    refine commute_lam_of_fixes i0 ?_ ?_ _
    · rw [spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hge, hva, ← hge, hginv]
    · rw [spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hgf, hb0v, ← hgf, hginv]
  set w : StatedSp r K := g * SymplecticTorusWeyl.lam i0 (lowerTransvection K) * g⁻¹ with hw
  have hwv : w * v = v * w := by
    have := hcomm.eq
    calc w * v = g * ((SymplecticTorusWeyl.lam i0 (lowerTransvection K)) * (g⁻¹ * v * g)) * g⁻¹ := by
          rw [hw]; group
      _ = g * ((g⁻¹ * v * g) * (SymplecticTorusWeyl.lam i0 (lowerTransvection K))) * g⁻¹ := by
          rw [this]
      _ = v * w := by rw [hw]; group
  have hwa : spMat w *ᵥ a = a + b0 := by
    rw [hw, spMat_mul, spMat_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    have h2 : spMat g⁻¹ *ᵥ a = Pi.single (Sum.inl i0) 1 := by rw [← hge, hginv]
    rw [h2, lam_transvection_mulVec, mulVec_add, hge, hgf]
  have hws := SymplecticHigher.mem_flagStabilizer.1 (hfix w hwv) i hi
  have hmem : spMat w *ᵥ a ∈ SymplecticFlag.flag r K i :=
    spMat_mulVec_mem_of_mem_stabilizer hws haF
  rw [hwa] at hmem
  have hbF : b0 ∈ SymplecticFlag.flag r K i := by
    have := Submodule.sub_mem _ hmem haF
    simpa using this
  have hiso := SymplecticHigher.isCompleteIsotropicFlag_flag (r := r) (K := K)
  have h0 := hiso.2.2 i (hI i hi).2 a haF b0 hbF
  rw [hab0] at h0
  exact one_ne_zero h0

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SpResidual.FixedEscape
