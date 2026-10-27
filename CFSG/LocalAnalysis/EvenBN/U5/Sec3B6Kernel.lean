module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Model

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem Ssub_pow_four {g : hypSU h 2 1} (hg : g ∈ Ssub h) : g ^ 4 = 1 := by
  obtain ⟨-, x, C, hgC⟩ := hg
  have hv : g * g ∈ Vsub h := mem_Vsub_of_mat (by rw [mat_mul, hgC, oddUni_mul_self])
  calc g ^ 4 = (g * g) * (g * g) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := Vsub_sq hv

theorem crd_one_eq_zero_of_mem_A₂sub {g : hypSU h 2 1} (hg : g ∈ A₂sub h) : crd g 1 = 0 :=
  (A₂sub_entries hg).2.2.1.1

theorem pow_four_eq_one_of_fixes {x : Gam h} (hV : ∀ v ∈ Vsub h, actΓ h x v ∈ Vsub h)
    (hS : ∀ g ∈ Ssub h, actΓ h x g ∈ Ssub h ∧ crd (actΓ h x g) = crd g) :
    Phi h x ^ 4 = 1 := by
  have := h.charP
  have h₁ : actΓ h x (z₁SU h) ∈ Vsub h := hV _ (ZPsub_le_Vsub z₁SU_mem_ZPsub)
  have h₂ : actΓ h x (vSU h !![0, 0; 0, 1] (isHerm_e₂₂ h)) ∈ Vsub h :=
    hV _ (vSU_mem_Vsub (isHerm_e₂₂ h))
  have hcol : ∀ a, a ≠ ιe₁ → a ≠ ιe₂ → lmat x a ιe₁ = 0 ∧ lmat x a ιe₂ = 0 :=
    fun a ha₁ ha₂ => lmat_col_plane h₁ h₂ ha₁ ha₂
  set l := lmat x ιz ιz with hl
  have hl0 : l ≠ 0 := lmat_zz_ne_zero hcol
  have key : ∀ v : Fin 2 → K, l • v = pblk x *ᵥ fun i => x.1.right (v i) := by
    intro v
    obtain ⟨g, hg, rfl⟩ := exists_Ssub_crd h v
    obtain ⟨hg', hcrd⟩ := hS g hg
    rw [← crd_act hcol hg hg', hcrd]
  have hM : pblk x = l • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have e1 := congrFun (key ![1, 0]) 0
    have e2 := congrFun (key ![1, 0]) 1
    have e3 := congrFun (key ![0, 1]) 0
    have e4 := congrFun (key ![0, 1]) 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_one, map_zero, mul_one, mul_zero,
      add_zero, zero_add] at e1 e2 e3 e4
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← e1, ← e2, ← e3, ← e4]
  have hσ : x.1.right = 1 := by
    refine RingEquiv.ext fun c => ?_
    show x.1.right c = c
    have e := congrFun (key ![c, 0]) 0
    rw [hM] at e
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, mul_zero, add_zero,
      Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by
        decide), mul_one] at e
    exact (mul_left_cancel₀ hl0 e).symm
  set u : Kˣ := (Units.mk0 l hl0)⁻¹ with hu
  set y := x * scalG u with hy
  have hyr : y.1.right = 1 := by
    rw [hy, Subgroup.coe_mul, SemidirectProduct.mul_right, hσ]
    simp [scalG]
  have hu' : (u : K) = l⁻¹ := by rw [hu, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hent : ∀ a b, lmat y a b = lmat x a b * l⁻¹ := by
    intro a b
    rw [hy, lmat_mul_of_right_one hσ, lmat_scalG, hu', Matrix.scalar_apply, Matrix.mul_diagonal]
  have hPW : IsParaW (lmat x) := by
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · obtain ⟨c1, c2⟩ := hcol ιz (by decide) (by decide)
      fin_cases i
      · exact c1
      · exact c2
    · obtain ⟨c1, c2⟩ := hcol (.inr (.inr j)) Sum.inr_ne_inl Sum.inr_ne_inl
      fin_cases i
      · exact c1
      · exact c2
  have hPx : IsPara (lmat x) := isPara_of_paraW hPW
  have hPy : IsPara (lmat y) := ⟨fun i => by rw [hent, hPx.1 i, zero_mul],
    fun i j => by rw [hent, hPx.2.1 i j, zero_mul], fun j => by rw [hent, hPx.2.2 j, zero_mul]⟩
  have hE : blkEE y = 1 := by
    ext i j
    have e := congrFun (congrFun hM i) j
    simp only [pblk, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul] at e
    rw [blkEE, Matrix.of_apply, hent, e, mul_comm, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
  have hzz : lmat y ιz ιz = 1 := by rw [hent, ← hl, mul_inv_cancel₀ hl0]
  have hEe : ∀ a b, lmat y (.inl a) (.inl b) = (1 : Matrix (Fin 2) (Fin 2) K) a b :=
    fun a b => congrFun (congrFun hE a) b
  have e11 : lmat y ιe₁ ιe₁ = 1 := by simpa using hEe 0 0
  have e12 : lmat y ιe₁ ιe₂ = 0 := by simpa using hEe 0 1
  have e21 : lmat y ιe₂ ιe₁ = 0 := by simpa using hEe 1 0
  have e22 : lmat y ιe₂ ιe₂ = 1 := by simpa using hEe 1 1
  obtain ⟨μ, -, hs⟩ := exists_sim_apply y
  have hμ : μ = 1 := by
    have s := hs ιz ιz
    simp only [hzz, hPy.2.2 0, hPy.2.2 1, map_zero, map_one, zero_mul, mul_zero, zero_add,
      add_zero, hypGram_apply, hypPartner_inr_inl, ↓reduceIte, mul_one] at s
    exact s.symm
  have hF : blkFF y = 1 := by
    have s11 := hs ιe₁ ιf₁
    have s12 := hs ιe₁ ιf₂
    have s21 := hs ιe₂ ιf₁
    have s22 := hs ιe₂ ιf₂
    simp [e11, e12, e21, e22, hPy.1, hPy.2.1, hμ, hypGram_apply] at s11 s12 s21 s22
    ext j k
    fin_cases j <;> fin_cases k
    · simpa [blkFF] using s11
    · simpa [blkFF] using s12
    · simpa [blkFF] using s21
    · simpa [blkFF] using s22
  have hy4 := lam_pow_four (mem_Lam.2 ⟨hyr, hPy, by rw [hE, Matrix.det_one]⟩) hE hF hzz
  have hPhi : Phi h y = Phi h x := by rw [hy, map_mul, Phi_scalG, mul_one]
  rw [← hPhi, ← map_pow, hy4, map_one]

end CFSG.LocalAnalysis.EvenBN.U5
