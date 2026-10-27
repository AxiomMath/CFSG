module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Matrix CFSG.ComponentClassification.StandardRecognition

private noncomputable def symplecticMapEquiv {l : Type} [DecidableEq l] [Fintype l] {R R' : Type}
    [Field R] [Field R'] (φ : R ≃+* R') :
    Matrix.symplecticGroup l R ≃* Matrix.symplecticGroup l R' where
  toFun A := ⟨(A : Matrix (l ⊕ l) (l ⊕ l) R).map φ, SymplecticGroup.map_mem A.2 φ⟩
  invFun A := ⟨(A : Matrix (l ⊕ l) (l ⊕ l) R').map φ.symm, SymplecticGroup.map_mem A.2 φ.symm⟩
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' A B := Subtype.ext (by simp [Matrix.map_mul])

theorem nonempty_mulEquiv_alternating_six_of_symplectic_field {X : Type} [Group X] (K : Type)
    [Field K] [Fintype K] (hK : Fintype.card K = 2)
    (h : Nonempty (X ≃* commutator (symplecticGroup (Fin 2) K))) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by rw [hK, ZMod.card]
  let φ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  let ψ : symplecticGroup (Fin 2) K ≃* symplecticGroup (Fin 2) (ZMod 2) :=
    symplecticMapEquiv φ
  have hcomm : (commutator (symplecticGroup (Fin 2) K)).map ψ.toMonoidHom =
      commutator (symplecticGroup (Fin 2) (ZMod 2)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 ψ.surjective]
  refine nonempty_mulEquiv_alternating_six_of_symplectic X ?_
  exact ⟨e.trans ((ψ.subgroupMap (commutator (symplecticGroup (Fin 2) K))).trans
    (MulEquiv.subgroupCongr hcomm))⟩

end CFSG.OddStandard.SmallF3.HypA2
