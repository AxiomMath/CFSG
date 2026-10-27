module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinData
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.LargeExtraspecial.DW37Input
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421Cut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421HoldsProof

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open
  K421LinProof K421CGProof K421DataProof

@[expose] noncomputable def slEquivGL2 (n : ℕ) :
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

theorem nonempty_equiv_GL_of_typeA (r : ℕ) {S : Type} [Group S]
    (h : IsLieIdxOver S (TauCeti.LieTypeIndex.A r) (fun Q => Q = 2)) :
    Nonempty (S ≃* GL (Fin (r + 1)) (ZMod 2)) := by
  obtain ⟨Q, hQp, hQc, ⟨⟨i, hv⟩, hd, ⟨e⟩⟩⟩ := h
  have hd' : i = .A r Q := hd
  subst hd'
  have hp : Q.p = 2 ∧ Q.exponent = 1 := by
    have hdvd : Q.p ∣ 2 := by
      rw [← hQc, TauCeti.PrimePower.card_def]
      exact dvd_pow_self Q.p (Nat.ne_of_gt Q.exponent_pos)
    have h2 : Q.p = 2 := (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).mp hdvd
    have hpow : Q.p ^ Q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]; exact hQc
    rw [h2] at hpow
    exact ⟨h2, (Nat.prime_two.pow_eq_iff.mp hpow).2⟩
  have hmod := CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega)
    (CFSG.Models.lieModel_A r Q hv e)
  rw [hp.1, hp.2] at hmod
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 2) (r + 1) 2 1
    (by norm_num) (by rw [Nat.card_zmod, pow_one]) hmod
  exact ⟨e1.trans ((CFSG.LargeExtraspecial.DW.slEquivPSL (r + 1)).symm.trans
    (slEquivGL2 (r + 1)))⟩

theorem nonempty_equiv_GG_six {S : Type} [Group S] (h : IsLinTwo 6 S) : Nonempty (S ≃* GG 0) := by
  obtain ⟨ε⟩ := nonempty_equiv_GL_of_typeA 5 h
  let κ : Fin 6 ≃ Fin 0 ⊕ Idx := Fintype.equivOfCardEq (by simp)
  exact ⟨ε.trans (reindexGL κ)⟩

theorem nonempty_equiv_GG_seven {S : Type} [Group S] (h : IsLinTwo 7 S) :
    Nonempty (S ≃* GG 1) := by
  obtain ⟨ε⟩ := nonempty_equiv_GL_of_typeA 6 h
  let κ : Fin 7 ≃ Fin 1 ⊕ Idx := Fintype.equivOfCardEq (by simp)
  exact ⟨ε.trans (reindexGL κ)⟩

end K421HoldsProof

open K421HoldsProof K421DataProof

theorem K421DataLin_holds : K421DataLin := by
  intro S _ _ h
  rcases h with h6 | h7
  · obtain ⟨ε⟩ := nonempty_equiv_GG_six h6
    exact data421_of_equiv (by norm_num) ε
  · obtain ⟨ε⟩ := nonempty_equiv_GG_seven h7
    exact data421_of_equiv (by norm_num) ε

theorem K421NonTransLin_holds : K421NonTransLin := by
  intro S _ _ h
  rcases h with h6 | h7
  · obtain ⟨ε⟩ := nonempty_equiv_GG_six h6
    exact nonTrans_of_equiv (by norm_num) ε
  · obtain ⟨ε⟩ := nonempty_equiv_GG_seven h7
    exact nonTrans_of_equiv (by norm_num) ε

end CFSG.LocalAnalysis.RankThreeUC.S15
