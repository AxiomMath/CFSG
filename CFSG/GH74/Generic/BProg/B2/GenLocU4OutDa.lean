module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutDaCore

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open GenLocU4Basic GenLocU4Out GenLocU4OutDaRot GenLocU4OutDaCore

namespace GenLocU4OutDa

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def swapS : Matrix (Fin 4) (Fin 4) K := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def swapφ (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin 4) K := swapS * M * swapS

theorem swapS_mul : (swapS : Matrix (Fin 4) (Fin 4) K) * swapS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapS, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapφ_mul (M N : Matrix (Fin 4) (Fin 4) K) : swapφ (M * N) = swapφ M * swapφ N := by
  unfold swapφ
  calc swapS * (M * N) * swapS = swapS * M * (swapS * swapS) * N * swapS := by
        rw [swapS_mul]; simp only [Matrix.mul_assoc, Matrix.mul_one]
    _ = (swapS * M * swapS) * (swapS * N * swapS) := by simp only [Matrix.mul_assoc]

theorem swapφ_swapφ (M : Matrix (Fin 4) (Fin 4) K) : swapφ (swapφ M) = M := by
  unfold swapφ
  calc swapS * (swapS * M * swapS) * swapS = (swapS * swapS) * M * (swapS * swapS) := by
        simp only [Matrix.mul_assoc]
    _ = M := by rw [swapS_mul]; simp

theorem swapφ_comm_iff (X G : Matrix (Fin 4) (Fin 4) K) :
    X * swapφ G = swapφ G * X ↔ swapφ X * G = G * swapφ X := by
  constructor
  · intro h
    have := congrArg swapφ h
    rwa [swapφ_mul, swapφ_mul, swapφ_swapφ] at this
  · intro h
    have := congrArg swapφ h
    rwa [swapφ_mul, swapφ_mul, swapφ_swapφ] at this

theorem swapφ_map (φ₀ : K →+* K) (G : Matrix (Fin 4) (Fin 4) K) :
    (swapφ G).map φ₀ = swapφ (G.map φ₀) := by
  have hS : (swapS : Matrix (Fin 4) (Fin 4) K).map φ₀ = swapS := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapS]
  unfold swapφ
  rw [Matrix.map_mul, Matrix.map_mul, hS]

theorem tT_eq : (tT : Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tT, Matrix.diagonal]

theorem swapφ_tT : swapφ (tT : Matrix (Fin 4) (Fin 4) K) = -tT := by
  rw [tT_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapφ, swapS, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapφ_xi : swapφ (xi : Matrix (Fin 4) (Fin 4) K) = xi := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapφ, swapS, xi, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapφ_bMat (c0 d0 c1 d1 : K) : swapφ (bMat c0 d0 c1 d1) = bMat c1 d1 c0 d0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapφ, swapS, bMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapS_unitary [Finite K] {q : ℕ} (hq0 : q ≠ 0) : IsUnitaryU q (swapS : Matrix (Fin 4) (Fin 4) K) := by
  unfold IsUnitaryU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapS, Matrix.mul_apply, Fin.sum_univ_four, zero_pow hq0]

theorem swapS_det : (swapS : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, swapS, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem swapφ_fix_iff (X G Gb : Matrix (Fin 4) (Fin 4) K) :
    X * swapφ Gb = swapφ G * X ↔ swapφ X * Gb = G * swapφ X := by
  constructor
  · intro h
    have := congrArg swapφ h
    rwa [swapφ_mul, swapφ_mul, swapφ_swapφ, swapφ_swapφ] at this
  · intro h
    have := congrArg swapφ h
    rwa [swapφ_mul, swapφ_mul, swapφ_swapφ] at this

theorem bMat_unitary_of [Finite K] {q : ℕ} (hq0 : q ≠ 0) (hodd : Odd q) {c0 d0 c1 d1 : K}
    (h00 : c0 ^ q * c0 + d0 ^ q * d0 = 1) (h01 : c0 ^ q * d0 - d0 ^ q * c0 = 0)
    (h22 : c1 ^ q * c1 + d1 ^ q * d1 = 1) (h23 : c1 ^ q * d1 - d1 ^ q * c1 = 0) :
    IsUnitaryU q (bMat c0 d0 c1 d1) := by
  unfold IsUnitaryU
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bMat, Matrix.mul_apply, Fin.sum_univ_four, zero_pow hq0, hodd.neg_pow] <;>
    first
    | linear_combination h00
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h22
    | linear_combination h23
    | linear_combination -h23

theorem outDaGen_holds [Finite K] :
    OutDaGen K p f := by
  intro hp hp2 hK hq B hBU hBm htB hxiB Γ h1 h2 h3 _ _ h6 _
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2' : (2 : K) ≠ 0 := two_ne_zero_of_card hp hp2 hK
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq0 : p ^ f ≠ 0 := hodd.pos.ne'
  have hring : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨ι, hι, hιq⟩ : ∃ ι : K, ι * ι = -1 ∧ ι ^ (p ^ f) = ι := by
    obtain ⟨ι, hι⟩ := isSquare_of_fixed hp hp2 hK (w := (-1 : K)) hodd.neg_one_pow
    exact ⟨ι, hι.symm, GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hι.symm⟩
  obtain ⟨c0, d0, c1, d1, hB⟩ : ∃ c0 d0 c1 d1 : K, B = bMat c0 d0 c1 d1 :=
    ⟨_, _, _, _, B_shape h2' htB hxiB⟩
  subst hB
  by_cases hmix : ∃ t : K, t * t = c0 + ι * d0
  · exact outDa_core hp hp2 hK hq _ hBU hBm htB hxiB hι hιq (by simpa [bMat] using hmix) Γ h1 h2 h3 h6
  have hmix1 : ∃ t : K, t * t = c1 + ι * d1 := by
    by_contra hn
    have hx : ¬ IsSquare (c0 + ι * d0) := fun ⟨r, hr⟩ => hmix ⟨r, hr.symm⟩
    have hy : ¬ IsSquare (c1 + ι * d1) := fun ⟨r, hr⟩ => hn ⟨r, hr.symm⟩
    obtain ⟨ρ, hρ⟩ := mul_isSquare_of_nonsquares hring hx hy
    exact not_both_nonsquares h hι hιq hBU hBm.2 hρ.symm
  obtain ⟨u1, u2, u3, u4⟩ := bMat_unitary hBU
  have hBU' : IsUnitaryU (p ^ f) (bMat c1 d1 c0 d0) := bMat_unitary_of hq0 hodd u3 u4 u1 u2
  have hBm' : IsMinusU (p ^ f) (bMat c1 d1 c0 d0) := by
    refine ⟨?_, fun μ hμ => ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [bMat]
    · have := hBm.2 μ hμ
      rw [det_bMat] at this ⊢
      rw [mul_comm (c1 * c1 + d1 * d1) (c0 * c0 + d0 * d0)]
      exact this
  have htB' : (tT : Matrix (Fin 4) (Fin 4) K) * bMat c1 d1 c0 d0 = bMat c1 d1 c0 d0 * tT := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tT, bMat, Matrix.mul_apply, Matrix.diagonal]
  have hxiB' : (xi : Matrix (Fin 4) (Fin 4) K) * bMat c1 d1 c0 d0 = -(bMat c1 d1 c0 d0 * xi) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xi, bMat, Matrix.mul_apply, Fin.sum_univ_four]
  have hSU := swapS_unitary (K := K) hq0
  obtain ⟨sS, hsS⟩ : ∃ sS : ↥(StatedSU 4 (p ^ f) K),
      ((sS : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = swapS :=
    ⟨suOf (p ^ f) _ hSU swapS_det, coe_suOf _ _ hSU swapS_det⟩
  have hsSsS : sS * sS = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp [Subgroup.coe_mul, Units.val_mul, hsS, swapS_mul]
  have hsSi : sS⁻¹ = sS := inv_eq_of_mul_eq_one_right hsSsS
  have hconj : ∀ g : ↥(StatedSU 4 (p ^ f) K),
      ((((MulAut.conj sS) g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        swapφ ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    intro g
    rw [MulAut.conj_apply, hsSi]
    simp [Subgroup.coe_mul, Units.val_mul, hsS, swapφ]
  have hfun : (fun x : K => x ^ (p ^ f)) = ⇑h.bar := (funext h.bar_apply).symm
  have hmapφ : ∀ G : Matrix (Fin 4) (Fin 4) K,
      (swapφ G).map (fun x : K => x ^ (p ^ f)) = swapφ (G.map (fun x : K => x ^ (p ^ f))) := by
    intro G
    rw [hfun]
    exact swapφ_map h.bar G
  have hfixIn : ∀ (X : Matrix (Fin 4) (Fin 4) K) (g : ↥(StatedSU 4 (p ^ f) K)),
      FixIn (swapφ X) g → FixIn X ((MulAut.conj sS) g) := by
    intro X g hg
    unfold FixIn at hg ⊢
    rw [hconj, swapφ_comm_iff]
    exact hg
  have hfixOut : ∀ (X : Matrix (Fin 4) (Fin 4) K) (g : ↥(StatedSU 4 (p ^ f) K)),
      FixOut (p ^ f) (swapφ X) g → FixOut (p ^ f) X ((MulAut.conj sS) g) := by
    intro X g hg
    unfold FixOut at hg ⊢
    rw [hconj, hmapφ, swapφ_fix_iff]
    exact hg
  have hTneg : ∀ g : ↥(StatedSU 4 (p ^ f) K), FixIn (tT : Matrix (Fin 4) (Fin 4) K) g →
      FixIn (swapφ (tT : Matrix (Fin 4) (Fin 4) K)) g := by
    intro g hg
    unfold FixIn at hg ⊢
    rw [swapφ_tT, neg_mul, mul_neg, hg]
  let Γ' : Subgroup ↥(StatedSU 4 (p ^ f) K) := Γ.comap (MulAut.conj sS).toMonoidHom
  have hmemΓ' : ∀ g, g ∈ Γ' ↔ (MulAut.conj sS) g ∈ Γ := fun g => Iff.rfl
  have h1' : ∀ g, FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ' :=
    fun g hg1 hg2 => (hmemΓ' g).2 (h1 _ (hfixIn _ g (hTneg g hg1)) (hfixIn _ g (by rwa [swapφ_xi])))
  have h2' : ∀ g, FixOut (p ^ f) (bMat c1 d1 c0 d0) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ' :=
    fun g hg1 hg2 => (hmemΓ' g).2 (h2 _ (hfixOut _ g (by rwa [swapφ_bMat]))
      (hfixIn _ g (hTneg g hg2)))
  have h3' : ∀ g, FixOut (p ^ f) (bMat c1 d1 c0 d0) g → FixIn (xi : Matrix (Fin 4) (Fin 4) K) g → g ∈ Γ' :=
    fun g hg1 hg2 => (hmemΓ' g).2 (h3 _ (hfixOut _ g (by rwa [swapφ_bMat]))
      (hfixIn _ g (by rwa [swapφ_xi])))
  have h6' : ∀ g, FixOut (p ^ f) (bMat c1 d1 c0 d0 * xi) g → FixIn (tT : Matrix (Fin 4) (Fin 4) K) g →
      g ∈ Γ' :=
    fun g hg1 hg2 => (hmemΓ' g).2 (h6 _ (hfixOut _ g (by rwa [swapφ_mul, swapφ_bMat, swapφ_xi]))
      (hfixIn _ g (hTneg g hg2)))
  have htop : Γ' = ⊤ :=
    outDa_core hp hp2 hK hq _ hBU' hBm' htB' hxiB' hι hιq (by simpa [bMat] using hmix1) Γ' h1' h2' h3' h6'
  rw [eq_top_iff]
  intro x _
  have hx : sS⁻¹ * x * sS ∈ Γ' := by rw [htop]; exact Subgroup.mem_top _
  rw [hmemΓ', MulAut.conj_apply] at hx
  have e : sS * (sS⁻¹ * x * sS) * sS⁻¹ = x := by group
  rwa [e] at hx

end GenLocU4OutDa

end CFSG.GH74.Generic.BProg.B2
