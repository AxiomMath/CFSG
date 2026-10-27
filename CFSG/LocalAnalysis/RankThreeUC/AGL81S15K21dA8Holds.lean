module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Core
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dA8Par
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA8Proof

open CFSG.Quasithin.H13.C1294

noncomputable def slEquivGL (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* GL (Fin n) (ZMod 2) :=
  MulEquiv.ofBijective
    (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* _)
    ⟨Matrix.SpecialLinearGroup.toGL_injective, fun A => by
      have hdet : (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
        have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
        simpa using h2
      refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), hdet⟩, ?_⟩
      apply Units.ext
      rfl⟩

theorem not_isSolvable_alt8 : ¬ Group.IsSolvable (alternatingGroup (Fin 8)) := by
  intro h
  refine Equiv.Perm.not_isSolvable (Fin 8) ?_ (Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 8)).subtype (Equiv.Perm.sign (α := Fin 8)) fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩)
  rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card]
  norm_num

noncomputable def alt8EquivSL4 : alternatingGroup (Fin 8) ≃* SL4 :=
  CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans (slEquivGL 4).symm

theorem not_isSolvable_SL4 : ¬ Group.IsSolvable SL4 := fun h =>
  not_isSolvable_alt8 (solvable_of_solvable_injective (f := alt8EquivSL4.toMonoidHom)
    alt8EquivSL4.injective)

theorem k21dGeomAt_SL4 : K21dGeomAt SL4 := by
  rw [k21dGeomAt_iff]
  intro U D E hUDE
  obtain ⟨hU, hUD, hDs, hED, hE, hE9, hinv⟩ := hUDE
  obtain ⟨c, hc⟩ := exists_conj_upperSub hU
  have hU' : U.map (MulAut.conj c⁻¹).toMonoidHom = upperSub := by
    rw [hc, map_conj_inv_conj]
  have hyp := K21dHyp.map (MulAut.conj c⁻¹) ⟨hU, hUD, hDs, hED, hE, hE9, hinv⟩
  rw [hU'] at hyp
  obtain ⟨-, hUD', hDs', hED', -, hE9', -⟩ := hyp
  have h9 : 9 ∣ Nat.card (D.map (MulAut.conj c⁻¹).toMonoidHom) := by
    rw [← hE9']
    exact Subgroup.card_dvd_of_le hED'
  obtain ⟨hDchar, hD576⟩ := D_char not_isSolvable_SL4 hUD' hDs' h9
  have hconcl := concl_of_D (fun g => hDchar g) hD576 hED' hE9'
  exact K21dConcl.of_map (MulAut.conj c⁻¹) (by rw [hU']; exact hconcl)

end K21dA8Proof

theorem k21dGeomA8_holds : K21dGeomA8 := by
  intro S _ _ ⟨e⟩
  exact K21dA8Proof.k21dGeomAt_of_mulEquiv (e.trans K21dA8Proof.alt8EquivSL4)
    K21dA8Proof.k21dGeomAt_SL4

end CFSG.LocalAnalysis.RankThreeUC.S15
