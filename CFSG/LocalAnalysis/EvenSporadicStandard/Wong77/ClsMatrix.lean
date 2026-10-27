module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsWords
public import Certificates.Certificate24140

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Matrix CFSG.Blueprint

theorem matrix_classification
    (N : NativeSporadic.Carrier .M23 →* Mat) (a : Vec) (hC : N cE = comp a)
    (hY : N hE *ᵥ e0 = e0) : ∃ i : Fin 2, N gA = stdA i ∧ N gB = stdB i := by
  have hspec := clsCheck_spec Certificates.certificate24140
  have hC23 : comp a ^ 23 = 1 := by rw [← hC, ← map_pow, cE_pow, map_one]
  obtain ⟨i, rfl⟩ := hspec.cyc a (by rw [hC23, one_mulVec])
  have hC' : N cE = cM i := hC
  have hYc : N hE * cM i = cM i ^ 16 * N hE := by
    rw [← hC', ← map_pow, ← map_mul, ← map_mul, hE_cE]
  obtain ⟨hy1, hy2⟩ := hspec.yfix i
  have hYY : N hE = yM i := eq_of_fix_comm (aStd i) hY hy1 hYc hy2
  have hX4 : N tE ^ 4 = 1 := by rw [← map_pow, tE_pow, map_one]
  have hUX : yM i * N tE = N tE * upM i := by
    have := congrArg N hE_tE
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hC', hYY] at this
    exact this
  obtain ⟨hep1, hep2⟩ := hspec.ep i
  have hfixz : yM i *ᵥ (N tE *ᵥ epV i) = N tE *ᵥ epV i := by
    rw [Matrix.mulVec_mulVec, hUX, ← Matrix.mulVec_mulVec, hep1]
  have hXe : N tE *ᵥ epV i = e0 := by
    rcases hspec.fix i _ hfixz with h0 | h0
    · exfalso
      apply hep2
      calc epV i = (N tE ^ 4) *ᵥ epV i := by rw [hX4, one_mulVec]
        _ = (N tE ^ 3 * N tE) *ᵥ epV i := by rw [pow_succ]
        _ = N tE ^ 3 *ᵥ (N tE *ᵥ epV i) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [h0, Matrix.mulVec_zero]
    · exact h0
  have hphi : N tE = phi (yM i) (binvM i) (N tE *ᵥ e0) := eq_phi hUX hXe (hspec.binv i)
  have hy : N tE *ᵥ e0 = yV i := by
    apply hspec.uniq i
    · rw [← hphi]; exact hUX
    · rw [← hphi]; exact hX4
  have hXX : N tE = xM i := by rw [hphi, hy]; rfl
  have hA : N gA = stdA i := by
    rw [gA_word]
    simp only [map_mul, map_pow]
    rw [hC', hYY, hXX]
    exact (hspec.words i).1.symm
  refine ⟨i, hA, ?_⟩
  rw [gB_eq, map_mul, hA, hC']
  exact (hspec.words i).2.symm

end CFSG.EvenSporadicStandard.Wong77.Cls
