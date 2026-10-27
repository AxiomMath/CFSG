module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Good
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Tau
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Fix
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320A5
public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL coe_diagGL)
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine (rSL coe_rSL)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

variable {k : Type} [Field k]

@[expose] noncomputable def Bgl (u : kˣ) : GL (Fin 3) k :=
  diagGL u * Matrix.SpecialLinearGroup.toGL (rSL : SpecialLinearGroup (Fin 3) k)

theorem coe_Bgl (u : kˣ) : ((Bgl u : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = Mm (u : k) := by
  rw [Bgl, Units.val_mul, coe_diagGL_eq, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_rSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dm, Mm, Matrix.mul_apply, Fin.sum_univ_three]

theorem xDiag_mul_yInn (u : kˣ) : xDiag u * yInn = conjAut' 3 k (Bgl u) := by
  rw [Bgl, map_mul]
  congr 1
  rw [conjAut_toGL]
  rfl

theorem tau_piece (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    have := LinearFieldFour.charP_two_of_card_eq_four hk
    NormalPrime (c25Fix (Subgroup.zpowers (xDiag u * yInn)))
      (Subgroup.zpowers (proj 3 k (tau0 (val_mul_self_add hk hu)))) := by
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  set hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu with hωdef
  set t := proj 3 k (tau0 hω) with ht
  have hBx : xDiag u * yInn = conjAut' 3 k (Bgl u) := xDiag_mul_yInn u
  have key : ∀ y ∈ c25Fix (Subgroup.zpowers (xDiag u * yInn)), y⁻¹ * t * y ∈ Subgroup.zpowers t := by
    intro y hy
    obtain ⟨g, rfl⟩ := proj_surjective 3 k y
    have hfix : conjAut' 3 k (Bgl u) (proj 3 k g) = proj 3 k g := by
      rw [← hBx]
      exact (mem_c25Fix_zpowers_iff _ _).1 hy
    obtain ⟨c, hc⟩ := exists_smul_of_conjAut_fix (Bgl u) g hfix
    rw [coe_Bgl] at hc
    have hc' : (c : k) = 1 ∨ (c : k) = (u : k) ∨ (c : k) = (u : k) * (u : k) := by
      rcases units_eq hk hu c with h | h | h
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (by rw [h]; rfl))
    obtain ⟨e, he⟩ := tau_mul_conj hω hc' hc
    have he' : tau0 hω * g = g * tau0 hω ^ e := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_pow, coe_tau0]
      exact he
    have : g⁻¹ * tau0 hω * g = tau0 hω ^ e := by
      rw [mul_assoc, he', inv_mul_cancel_left]
    refine ⟨(e : ℤ), ?_⟩
    show t ^ (e : ℤ) = _
    rw [zpow_natCast, ht, ← map_pow, ← this, map_mul, map_mul, map_inv]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.zpowers_le, mem_c25Fix_zpowers_iff, hBx]
    refine conjAut_proj_eq_of_comm (Bgl u) (tau0 hω) ?_
    rw [coe_Bgl, coe_tau0]
    exact Mm_comm_tauM0 hω
  · intro x hx n hn
    have hle : Subgroup.zpowers t ≤ (Subgroup.zpowers t).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      have := key x⁻¹ (inv_mem hx)
      simpa [MulAut.conj_apply] using this
    have := hle hn
    simpa [MulAut.conj_apply] using this
  · have h7 : t ^ 7 = 1 := by
      rw [ht, ← map_pow, tau0_pow_seven hω, map_one]
    have hdvd : Nat.card (Subgroup.zpowers t) ∣ 7 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one h7
    exact (by norm_num : Nat.Coprime 3 7).coprime_dvd_right hdvd

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
