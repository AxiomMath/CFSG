module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpARadicalComm
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerData
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Torus
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (upperUnipotentSp)
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] noncomputable def sp8dLam (g : StatedSp 4 K) : Matrix (Fin 4) (Fin 4) K :=
  (mat 4 K g).toBlocks₁₁

theorem spARepMat_four_two_mul_self :
    (spARepMat 4 2 : Matrix (Fin 4) (Fin 4) K) * spARepMat 4 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spARepMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sp8d_block {g : StatedSp 4 K}
    (hg : g ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K))) :
    ∃ Q T : Matrix (Fin 4) (Fin 4) K, mat 4 K g = fromBlocks (sp8dLam g) Q 0 T ∧
      (sp8dLam g)ᵀ * T = 1 ∧ Qᵀ * T = Tᵀ * Q ∧ sp8dLam g * spARepMat 4 2 = spARepMat 4 2 * T := by
  obtain ⟨P, Q, R, T, hM⟩ : ∃ P Q R T : Matrix (Fin 4) (Fin 4) K,
      mat 4 K g = fromBlocks P Q R T := ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  have hP : sp8dLam g = P := by rw [sp8dLam, hM, toBlocks_fromBlocks₁₁]
  rw [hP]
  have hcomm := congrArg (mat 4 K) (mem_centralizer_singleton_iff.1 hg)
  rw [map_mul, map_mul, spARep, mat_upperUnipotentSp, hM, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_inj] at hcomm
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add] at hcomm
  obtain ⟨h11, h12, -, -⟩ := hcomm
  have hSR : spARepMat 4 2 * R = 0 := by
    have h := congrArg (fun M => M - P) h11
    simpa using h.symm
  have hR : R = 0 := by
    rw [← Matrix.one_mul R, ← spARepMat_four_two_mul_self, Matrix.mul_assoc, hSR,
      Matrix.mul_zero]
  subst hR
  have hsym := mat_transpose_mul_gram_mul g
  rw [hM, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hsym
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    transpose_zero, Matrix.mul_neg, Matrix.neg_mul, neg_zero] at hsym
  obtain ⟨-, hPT, -, hQT⟩ := hsym
  refine ⟨Q, T, hM, hPT, ?_, by rw [add_comm Q] at h12; exact add_right_cancel h12⟩
  have h := congrArg (fun M => M + Tᵀ * Q) hQT
  simpa [add_comm] using h

section Block

variable {g : StatedSp 4 K} (hg : g ∈ centralizer ({spARep 4 2} : Set (StatedSp 4 K)))
include hg

theorem sp8dLam_transpose_mul :
    (sp8dLam g)ᵀ * spARepMat 4 2 * sp8dLam g = spARepMat 4 2 := by
  obtain ⟨Q, T, -, hPT, -, hPS⟩ := sp8d_block hg
  have hT : T = spARepMat 4 2 * (sp8dLam g * spARepMat 4 2) := by
    rw [hPS, ← Matrix.mul_assoc, spARepMat_four_two_mul_self, Matrix.one_mul]
  calc (sp8dLam g)ᵀ * spARepMat 4 2 * sp8dLam g =
        (sp8dLam g)ᵀ * spARepMat 4 2 * sp8dLam g * (spARepMat 4 2 * spARepMat 4 2) := by
          rw [spARepMat_four_two_mul_self, Matrix.mul_one]
    _ = (sp8dLam g)ᵀ * (spARepMat 4 2 * (sp8dLam g * spARepMat 4 2)) * spARepMat 4 2 := by
          simp only [Matrix.mul_assoc]
    _ = spARepMat 4 2 := by rw [← hT, hPT, Matrix.one_mul]

theorem sp8dLam_mul (g' : StatedSp 4 K) : sp8dLam (g' * g) = sp8dLam g' * sp8dLam g := by
  obtain ⟨Q, T, hM, -, -, -⟩ := sp8d_block hg
  rw [sp8dLam, map_mul, hM, ← fromBlocks_toBlocks (mat 4 K g'), fromBlocks_multiply,
    toBlocks_fromBlocks₁₁, Matrix.mul_zero, add_zero]
  rfl

theorem sp8d_conj_upperUnipotentSp {X : Matrix (Fin 4) (Fin 4) K} (hX : Xᵀ = X) :
    g * upperUnipotentSp 4 K hX * g⁻¹ =
      upperUnipotentSp 4 K (transpose_mul_mul_transpose (sp8dLam g) hX) := by
  obtain ⟨Q, T, hM, hPT, -, -⟩ := sp8d_block hg
  rw [mul_inv_eq_iff_eq_mul]
  apply mat_injective
  rw [map_mul, map_mul, hM, mat_upperUnipotentSp, mat_upperUnipotentSp, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add]
  rw [Matrix.mul_assoc (sp8dLam g * X), hPT, Matrix.mul_one, add_comm]

theorem sp8d_eq_upperUnipotentSp_of_lam (h1 : sp8dLam g = 1) :
    ∃ (Y : Matrix (Fin 4) (Fin 4) K) (hY : Yᵀ = Y), g = upperUnipotentSp 4 K hY := by
  obtain ⟨Q, T, hM, hPT, hQT, -⟩ := sp8d_block hg
  rw [h1, transpose_one, Matrix.one_mul] at hPT
  subst hPT
  rw [Matrix.mul_one, transpose_one, Matrix.one_mul] at hQT
  refine ⟨Q, hQT, mat_injective ?_⟩
  rw [hM, h1, mat_upperUnipotentSp]

end Block

theorem sp8dLam_leviEmbedGL (A : GL (Fin 4) K) :
    sp8dLam (leviEmbedGL K 4 A) = (A : Matrix (Fin 4) (Fin 4) K) := by
  rw [sp8dLam, mat_leviEmbedGL, toBlocks_fromBlocks₁₁]

theorem sp8dLam_one : sp8dLam (1 : StatedSp 4 K) = 1 := by
  rw [sp8dLam, map_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁]

section Transport

variable [CharP K 2] (hK : Nat.card K = 2)

@[expose] noncomputable def sp8dEquiv : ZMod 2 ≃+* K :=
  RingEquiv.ofBijective (ZMod.castHom (dvd_refl 2) K)
    ⟨(ZMod.castHom (dvd_refl 2) K).injective, fun x => by
      rcases eq_zero_or_eq_one_of_natCard_two hK x with rfl | rfl
      · exact ⟨0, map_zero _⟩
      · exact ⟨1, map_one _⟩⟩

@[expose] noncomputable def sp8dMap : Sp8dMat ≃+* Matrix (Fin 4) (Fin 4) K :=
  (sp8dEquiv hK).mapMatrix

theorem sp8dMap_apply (A : Sp8dMat) (i j : Fin 4) : sp8dMap hK A i j = sp8dEquiv hK (A i j) :=
  rfl

theorem sp8dMap_transpose (A : Sp8dMat) : sp8dMap hK Aᵀ = (sp8dMap hK A)ᵀ := rfl

theorem sp8dMap_S : sp8dMap hK sp8dS = (spARepMat 4 2 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  rw [sp8dMap_apply]
  fin_cases i <;> fin_cases j <;> simp [sp8dS, spARepMat]

theorem sp8dMap_C1 : sp8dMap hK sp8dC1 = (spARepMat 4 1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  rw [sp8dMap_apply]
  fin_cases i <;> fin_cases j <;> simp [sp8dC1, spARepMat]

@[expose] noncomputable def sp8dGL (A A' : Sp8dMat) (h : A * A' = 1) (h' : A' * A = 1) :
    GL (Fin 4) K :=
  ⟨sp8dMap hK A, sp8dMap hK A', by rw [← map_mul, h, map_one], by rw [← map_mul, h', map_one]⟩

theorem coe_sp8dGL (A A' : Sp8dMat) (h : A * A' = 1) (h' : A' * A = 1) :
    ((sp8dGL hK A A' h h' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = sp8dMap hK A := rfl

theorem coe_sp8dGL_inv (A A' : Sp8dMat) (h : A * A' = 1) (h' : A' * A = 1) :
    (((sp8dGL hK A A' h h')⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = sp8dMap hK A' :=
  rfl

theorem sp8dGL_mem_sp {A A' : Sp8dMat} (h : A * A' = 1) (h' : A' * A = 1)
    (hA : A * sp8dS * Aᵀ = sp8dS) :
    ((sp8dGL hK A A' h h' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * spARepMat 4 2 *
      ((sp8dGL hK A A' h h' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ = spARepMat 4 2 := by
  rw [coe_sp8dGL, ← sp8dMap_S, ← sp8dMap_transpose, ← map_mul, ← map_mul, hA]

end Transport

section Lifts

theorem sp8d_levi_comm_mem {P R : GL (Fin 4) K}
    (hP : (P : Matrix (Fin 4) (Fin 4) K) * spARepMat 4 2 * (P : Matrix (Fin 4) (Fin 4) K)ᵀ =
      spARepMat 4 2)
    (hR : (R : Matrix (Fin 4) (Fin 4) K) * spARepMat 4 2 * (R : Matrix (Fin 4) (Fin 4) K)ᵀ =
      spARepMat 4 2) :
    leviEmbedGL K 4 ⁅P, R⁆ ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
      centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ := by
  rw [map_commutatorElement]
  exact commutator_mem_commutator (leviEmbedGL_mem_centralizer_spARep hP)
    (leviEmbedGL_mem_centralizer_spARep hR)

theorem coe_commutatorElement_GL (P R : GL (Fin 4) K) :
    ((⁅P, R⁆ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        ((R⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]

theorem sp8d_inv_P1 : sp8dP1 * sp8dP1i = 1 := sp8d_inv.1
theorem sp8d_inv_P1' : sp8dP1i * sp8dP1 = 1 := sp8d_inv.2.1
theorem sp8d_inv_R1 : sp8dR1 * sp8dR1i = 1 := sp8d_inv.2.2.1
theorem sp8d_inv_R1' : sp8dR1i * sp8dR1 = 1 := sp8d_inv.2.2.2.1
theorem sp8d_inv_Pg : sp8dPg * sp8dPgi = 1 := sp8d_inv.2.2.2.2.1
theorem sp8d_inv_Pg' : sp8dPgi * sp8dPg = 1 := sp8d_inv.2.2.2.2.2.1
theorem sp8d_inv_Rg : sp8dRg * sp8dRgi = 1 := sp8d_inv.2.2.2.2.2.2.1
theorem sp8d_inv_Rg' : sp8dRgi * sp8dRg = 1 := sp8d_inv.2.2.2.2.2.2.2.1
theorem sp8d_inv_Ph : sp8dPh * sp8dPh = 1 := sp8d_inv.2.2.2.2.2.2.2.2.1
theorem sp8d_inv_Rh : sp8dRh * sp8dRhi = 1 := sp8d_inv.2.2.2.2.2.2.2.2.2.1
theorem sp8d_inv_Rh' : sp8dRhi * sp8dRh = 1 := sp8d_inv.2.2.2.2.2.2.2.2.2.2

variable [CharP K 2] (hK : Nat.card K = 2)

@[expose] noncomputable def sp8dB1GL : GL (Fin 4) K :=
  ⁅sp8dGL hK sp8dP1 sp8dP1i sp8d_inv_P1 sp8d_inv_P1', sp8dGL hK sp8dR1 sp8dR1i sp8d_inv_R1
    sp8d_inv_R1'⁆

@[expose] noncomputable def sp8dGGL : GL (Fin 4) K :=
  ⁅sp8dGL hK sp8dPg sp8dPgi sp8d_inv_Pg sp8d_inv_Pg', sp8dGL hK sp8dRg sp8dRgi sp8d_inv_Rg
    sp8d_inv_Rg'⁆

@[expose] noncomputable def sp8dHGL : GL (Fin 4) K :=
  ⁅sp8dGL hK sp8dPh sp8dPh sp8d_inv_Ph sp8d_inv_Ph, sp8dGL hK sp8dRh sp8dRhi sp8d_inv_Rh
    sp8d_inv_Rh'⁆

theorem coe_sp8dB1GL : ((sp8dB1GL hK : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    sp8dMap hK sp8dB1 := by
  rw [sp8dB1GL, coe_commutatorElement_GL, coe_sp8dGL, coe_sp8dGL, coe_sp8dGL_inv, coe_sp8dGL_inv,
    ← map_mul, ← map_mul, ← map_mul, ← sp8d_comm.1]

theorem coe_sp8dGGL : ((sp8dGGL hK : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    sp8dMap hK sp8dG := by
  rw [sp8dGGL, coe_commutatorElement_GL, coe_sp8dGL, coe_sp8dGL, coe_sp8dGL_inv, coe_sp8dGL_inv,
    ← map_mul, ← map_mul, ← map_mul, ← sp8d_comm.2.1]

theorem coe_sp8dHGL : ((sp8dHGL hK : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    sp8dMap hK sp8dH := by
  rw [sp8dHGL, coe_commutatorElement_GL, coe_sp8dGL, coe_sp8dGL, coe_sp8dGL_inv, coe_sp8dGL_inv,
    ← map_mul, ← map_mul, ← map_mul, ← sp8d_comm.2.2]

theorem sp8d_levi_gens_mem :
    leviEmbedGL K 4 (sp8dB1GL hK) ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ ∧
      leviEmbedGL K 4 (sp8dGGL hK) ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ ∧
      leviEmbedGL K 4 (sp8dHGL hK) ∈ ⁅centralizer ({spARep 4 2} : Set (StatedSp 4 K)),
        centralizer ({spARep 4 2} : Set (StatedSp 4 K))⁆ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sp8d_mem_sp
  exact ⟨sp8d_levi_comm_mem (sp8dGL_mem_sp hK _ _ h1) (sp8dGL_mem_sp hK _ _ h2),
    sp8d_levi_comm_mem (sp8dGL_mem_sp hK _ _ h3) (sp8dGL_mem_sp hK _ _ h4),
    sp8d_levi_comm_mem (sp8dGL_mem_sp hK _ _ h5) (sp8dGL_mem_sp hK _ _ h6)⟩

end Lifts

end CFSG.SeitzReduction.SymplecticPilot
