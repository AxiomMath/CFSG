module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Type
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

theorem excU62Type_of_psu {E : Type} [Field E] [Finite E] {m : ℕ}
    (hE : Nat.card E = (2 ^ 1) ^ 2) (hm : m = 4 ∨ m = 5) {Q : Type} [Group Q]
    (e : Q ≃* StatedProj (StatedSU m (2 ^ 1) E)) : ExcU62Type Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨by omega, fun hr => by omega⟩
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hE]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (r + 1) (2 ^ 1)
  exact ⟨⟨.twistedA r q, hv⟩, ⟨by omega, rfl, rfl⟩, ⟨(e.trans eP).trans e₀.symm⟩⟩

theorem excU62Type_of_psl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 8) {Q : Type}
    [Group Q] (e : Q ≃* StatedProj (StatedSL 2 F)) : ExcU62Type Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 3 (by norm_num)
    (by rw [hF]; norm_num)
  let eP := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)
  let eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  exact ⟨⟨.A 1 q, hv⟩, ⟨rfl, rfl, rfl⟩,
    ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans
      (eP.trans eC.symm)⟩⟩

theorem excU62_lieQuot_or_small {X : Type} [Group X] {J : Subgroup X}
    (h : ExcU62Type (↥J ⧸ Subgroup.center ↥J)) :
    IsLieQuot ↥J (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d) ∨ IsBalSmall J := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  rcases excU62CompIdx_cases hd with h1 | h2
  · exact Or.inl ⟨d, h1, ⟨f⟩⟩
  · exact Or.inr (Or.inr (Or.inr ⟨d, h2, ⟨f⟩⟩))

end CFSG.HardMathSupport.Dickson.Bal207

end
