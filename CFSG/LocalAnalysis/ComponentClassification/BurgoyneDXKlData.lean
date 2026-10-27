module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXDrBlock
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT1a

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL)

variable {K : Type} [Field K] {d : ℕ}

structure K2Data (R : GL (Fin d) K) (M : Subgroup (GL (Fin d) K)) : Prop where
  le : M ≤ matrixDerived (oQ R)
  perf : ⁅M, M⁆ = M
  neg : (-1 : GL (Fin d) K) ∈ M
  inv : ∀ u ∈ M, u * u = 1 → u = 1 ∨ u = -1

theorem K2Data.transport {R R' : GL (Fin d) K} {M : Subgroup (GL (Fin d) K)}
    (h : K2Data R M) (S : GL (Fin d) K) (ν : Kˣ)
    (hS : ∀ v, oQ R' ((S : Matrix (Fin d) (Fin d) K) *ᵥ v) = ν * oQ R v) :
    K2Data R' (M.map (MulAut.conj S).toMonoidHom) := by
  set φ := (MulAut.conj S).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj S).injective
  have hφneg : φ (-1) = -1 := by
    change S * (-1) * S⁻¹ = -1
    rw [mul_neg_one, neg_mul, mul_inv_cancel]
  refine ⟨?_, ?_, ⟨-1, h.neg, hφneg⟩, ?_⟩
  · rw [← map_matrixDerived_conj S ν hS]
    exact map_mono h.le
  · rw [← Subgroup.map_commutator, h.perf]
  · rintro _ ⟨u, hu, rfl⟩ huu
    have huu' : u * u = 1 := hφinj (by rw [map_mul, huu, map_one])
    rcases h.inv u hu huu' with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1, hφneg])

theorem neg_one_ne_one_GL (h2 : (2 : K) ≠ 0) (hd : 0 < d) : (-1 : GL (Fin d) K) ≠ 1 := by
  intro h
  have e := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K) ⟨0, hd⟩ ⟨0, hd⟩) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at e
  exact h2 (by linear_combination -e)

theorem false_of_k2_sign [Finite K] (hK : ringChar K ≠ 2) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {M : Subgroup (GL (Fin d) K)} (hd : K2Data (diagGL hw) M) {J : Finset (Fin d)}
    (hJ : J.Nonempty) (hJc : Jᶜ.Nonempty)
    (hfix : ∀ X ∈ M, X * signGL K J = signGL K J * X)
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map
      (projH _)).subgroupOf (autFixed (oκ _ (sgnPair (Ring.two_ne_zero hK) hw J))))) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨I, hI, hMO⟩ := Dr.exists_block_of_comp hK hw hd.le hd.perf J hfix hQc
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJc
    · rw [compl_compl]
      exact hJ
  obtain ⟨j, hj⟩ := hIc
  have hnegI := oBlock_le_oIsoBlock hw I (hMO hd.neg)
  have e := mulVec_eq_of_mem_oIsoBlock hw hnegI (x := Pi.single j 1) fun i hi => by
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact (Finset.mem_compl.1 hj) hi
  have e' := congrFun e j
  simp only [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply,
    Pi.single_eq_same] at e'
  exact h2 (by linear_combination -e')

end CFSG.ComponentClassification.Burgoyne.DX.Kl
