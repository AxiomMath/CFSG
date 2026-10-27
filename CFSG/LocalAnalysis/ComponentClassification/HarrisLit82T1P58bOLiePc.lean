module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthPc
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOLieComp
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp (comp_map_mulEquiv)
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth (even_of_skew' pc_comp_eq)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem false_of_pc (hK : ringChar K ≠ 2) {p f : ℕ} (hp : p.Prime) (hKc : Nat.card K = p ^ f)
    {F : Type*} [Field F] [Finite F] {d : ℕ} (hd : 7 ≤ d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = -1)
    (hz2 : orderOf (projH _ (⟨T, hT⟩ : matrixDerived (oQ R))) = 2)
    {M₁ M₂ : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (h₁H : M₁ ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (h₁ : IsPComponent 2 (M₁.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})))
    (e₁ : ↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* PSL(2, F))
    (h₂H : M₂ ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (h₂ : IsPComponent 2 (M₂.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})))
    (hz₂ : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ∈ M₂) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  set Tm := (T : Matrix (Fin d) (Fin d) K) with hTm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have hiso : Tmᵀ * Rm * Tm = Rm := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
    ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  have hTT' : Tm * (-Tm) = 1 := by rw [Matrix.mul_neg, hT2, neg_neg]
  have hε : Tmᵀ * Rm = (-1 : K) • (Rm * Tm) := by
    calc Tmᵀ * Rm = Tmᵀ * Rm * (Tm * (-Tm)) := by rw [hTT', Matrix.mul_one]
      _ = Tmᵀ * Rm * Tm * (-Tm) := by rw [Matrix.mul_assoc (Tmᵀ * Rm)]
      _ = Rm * (-Tm) := by rw [hiso]
      _ = (-1 : K) • (Rm * Tm) := by rw [Matrix.mul_neg, neg_one_smul]
  have hS2 : Tm * Tm = (-1 : K) • 1 := by rw [neg_one_smul]; exact hT2
  have hc0 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  obtain ⟨n, hn⟩ := even_of_skew' h2 hε
  obtain rfl : d = 2 * n := by omega
  obtain ⟨H₁, hgram₁, hAH₁⟩ := exists_pc_basis hK hR hc0 hS2 hε (fun _ => 1)
    (fun _ => one_ne_zero)
  obtain ⟨R₁, hR₁⟩ : ∃ R₁, R₁ = CatalogueBGraphForm.glTranspose (2 * n) K H₁ * R * H₁ :=
    ⟨_, rfl⟩
  have hgramR₁ : (H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K)ᵀ * R * H₁ = R₁ := by
    rw [hR₁]
    simp only [Units.val_mul, CatalogueBGraphForm.glTranspose_matrix]
  have hR₁m : (R₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(-1 : K))) := by
    rw [← hgramR₁, hgram₁]
    simp only [one_smul]
    rfl
  obtain ⟨hS, -, -⟩ := exists_transport_of_gram hgramR₁ (g := linPair T hTiso)
    (linPair_right T hTiso)
  set θ := oTransport H₁⁻¹ 1 hS with hθ
  set A := derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩ with hAdef
  have hAm : ((A : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (jMat (-1 : K)) := by
    rw [hAdef, coe_derivedTransport, Units.val_mul, Units.val_mul, inv_inv]
    calc ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * Tm * H₁ =
        ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * (Tm * H₁) := by
          rw [Matrix.mul_assoc]
      _ = ((H₁⁻¹ : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *
          ((H₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) K) * blkDiag n (jMat (-1 : K))) := by
          rw [hAH₁]
      _ = blkDiag n (jMat (-1 : K)) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]
  have hθz : θ (projH _ ⟨T, hT⟩) = projH _ A := by
    show oTransport H₁⁻¹ 1 hS (projH _ ⟨T, hT⟩) = projH _ (derivedTransport H₁⁻¹ 1 hS ⟨T, hT⟩)
    exact oTransport_proj _ _ _ _
  obtain ⟨h₁H', h₁'⟩ := comp_map_mulEquiv θ h₁H h₁
  obtain ⟨h₂H', h₂'⟩ := comp_map_mulEquiv θ h₂H h₂
  rw [hθz] at h₁H' h₁' h₂H' h₂'
  obtain ⟨hZ1, hrg1⟩ := pc_comp_eq hK hp hKc hc0 (by omega) hR₁m hAm h₁H' h₁'
  obtain ⟨hZ2, hrg2⟩ := pc_comp_eq hK hp hKc hc0 (by omega) hR₁m hAm h₂H' h₂'
  have h12 : M₁ = M₂ := Subgroup.map_injective θ.injective (hrg1.symm.trans hrg2)
  have hzR₁ : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ∈ M₁ := h12 ▸ hz₂
  have hzc : (⟨_, hzR₁⟩ : M₁) ∈ center M₁ := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (h₁H y.2))
  exact false_of_mem_center_psl2 e₁ hzc (by rw [Subgroup.orderOf_mk, hz2])

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
