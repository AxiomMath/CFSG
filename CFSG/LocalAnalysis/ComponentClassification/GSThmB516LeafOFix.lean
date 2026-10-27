module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCore

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_fixed_vector (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {A : GL (Fin d) K}
    (hA : A ∈ matrixIsometries (oQ R))
    (hA2 : (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) = 1)
    (hA1 : oκ _ (linPair A hA) ≠ 1) {N : Subgroup (GL (Fin d) K)}
    (hN : N ≤ matrixDerived (oQ R)) (hperf : ⁅N, N⁆ = N) (hfix : ∀ X ∈ N, X * A = A * X)
    (hQs : (N.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ (linPair A hA)))
    (hQc : IsPComponent 2 (((N.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ (linPair A hA))))) :
    ∃ v : Fin d → K, v ≠ 0 ∧ ∀ X ∈ N, (X : Matrix (Fin d) (Fin d) K) *ᵥ v = v := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hAR : (A : Matrix (Fin d) (Fin d) K)ᵀ * R * (A : Matrix (Fin d) (Fin d) K) = R := by
    have := hA
    rw [matrixIsometries_oQ h2 R hR, CatalogueBGraphForm.mem_isometryGroup] at this
    exact this
  obtain ⟨hab, c, hcA, horth, hdiag, -, -⟩ := exists_split_nf hK hR hAR hA2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hA hab c hcA horth hdiag
  set J := famJ hab with hJdef
  have hSA : S * A * S⁻¹ = signGL K J := by
    have := congrArg (fun g : similarityPairs _ => g.val.left) heq
    simp only [transPair_left, linPair_right, map_one, MulAut.one_apply] at this
    exact this
  set N' := N.map (MulAut.conj S).toMonoidHom with hN'
  have hN'H : N' ≤ matrixDerived (oQ (diagGL hw)) := by
    rw [← map_matrixDerived_conj S 1 hS]
    exact map_mono hN
  have hperf' : ⁅N', N'⁆ = N' := by rw [hN', ← Subgroup.map_commutator, hperf]
  have hfix' : ∀ X ∈ N', X * signGL K J = signGL K J * X := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [← hSA]
    change S * Y * S⁻¹ * (S * A * S⁻¹) = S * A * S⁻¹ * (S * Y * S⁻¹)
    calc S * Y * S⁻¹ * (S * A * S⁻¹) = S * (Y * A) * S⁻¹ := by group
      _ = S * (A * Y) * S⁻¹ := by rw [hfix Y hY]
      _ = S * A * S⁻¹ * (S * Y * S⁻¹) := by group
  obtain ⟨-, hQc'⟩ := DX.transport_comp hN S 1 hS hQs hQc
  rw [heq] at hQc'
  obtain ⟨I, hI, hNI⟩ := DX.Dr.exists_block_of_comp hK hw hN'H hperf' J hfix' hQc'
  have hne : oκ _ (sgnPair h2 hw J) ≠ 1 := by
    rw [hJdef, ← heq, ← oTransport_kappa]
    intro h1
    apply hA1
    exact (MulAut.congr (oTransport S 1 hS)).injective (by rw [h1, map_one])
  have hJ : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hne (X10Orth.oκ_sgnPair_eq_one h2 hw (Or.inl h))
  have hJc : Jᶜ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h =>
    hne (X10Orth.oκ_sgnPair_eq_one h2 hw (Or.inr (Finset.compl_eq_empty_iff _ |>.1 h)))
  obtain ⟨x, hx⟩ : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJc
    · rwa [compl_compl]
  have hxI : x ∉ I := Finset.mem_compl.1 hx
  refine ⟨((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single x 1, ?_, ?_⟩
  · intro h0
    have := congrArg (fun v => (S : Matrix (Fin d) (Fin d) K) *ᵥ v) h0
    simp only [mulVec_mulVec, mulVec_zero] at this
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this
    have h1 := congrFun this x
    simp at h1
  · intro X hX
    have hXI : S * X * S⁻¹ ∈ oBlock K hw I := hNI ⟨X, hX, rfl⟩
    have hent := ((mem_oIsoBlock_iff hw).1 (oBlock_le_oIsoBlock hw I hXI)).2
    have hfixe : ((S * X * S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Pi.single x 1 =
        Pi.single x 1 := by
      funext i
      rw [mulVec_single_one, col_apply, hent i x (Or.inr hxI)]
      by_cases hix : i = x
      · subst hix
        simp
      · simp [hix]
    have hXS : (X : Matrix (Fin d) (Fin d) K) * ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        ((S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          ((S * X * S⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [mulVec_mulVec, hXS, ← mulVec_mulVec, hfixe]

end CFSG.ComponentClassification.GSThmB.Orth516
