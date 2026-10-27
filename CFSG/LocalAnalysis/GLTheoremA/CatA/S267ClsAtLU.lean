module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLUni
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

abbrev ConcACaseLLinStatement : Prop :=
  ∀ {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}, p.Prime → p ≠ 2 →
    ∀ [S.Normal], ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsElemAbelian p B →
    p ^ GLATwoLocalRank p Ω ≤ Nat.card B → p ^ 4 ≤ Nat.card B →
    Nat.card ↥(B ⊓ centModSubgroup p S) = p → ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
    ∀ {n : ℕ}, 3 ≤ n → ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ}, ℓ.Prime → ℓ ≠ 2 → 1 ≤ f →
    Nat.card K = ℓ ^ f → p ≠ ℓ → p ∣ Nat.gcd n (Nat.card K - 1) →
    (PSimple p S ≃* StatedProj (StatedSL n K)) → S267ConcA p S B


theorem badClsAt_A (hLin : ConcACaseLLinStatement) (hGA : GriessAllModelsStatement) {n : ℕ}
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A n Q).Valid) (hn : 2 ≤ n) :
    BadClsAt ⟨.A n Q, hv⟩ := by
  classical
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC hp3B hHq
  rw [TauCeti.LieTypeIndex.characteristic_A] at hchar
  subst hchar
  obtain ⟨e⟩ := he
  haveI := hSn
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hKc : Nat.card (GaloisField Q.p Q.exponent) = Q.p ^ Q.exponent :=
    GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
  let e' : PSimple p S ≃* StatedProj (StatedSL (n + 1) (GaloisField Q.p Q.exponent)) :=
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n Q hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (n + 1) _)
  by_cases hdiag : p ∣ Nat.gcd (n + 1) (Nat.card (GaloisField Q.p Q.exponent) - 1)
  · exact Or.inl (hLin hp hp2 hperf hcore hB hrank hB4 hBC hp3B (by omega) Q.prime_p hq2
      Q.exponent_pos hKc (Ne.symm hqp) hdiag e')
  · have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf
      hcore (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e) (Ne.symm hqp)
      (fun _ => by rwa [hKc] at hdiag) (fun h => by cases h)
    exact concl_lin hp hp2 Q.prime_p hq2 hqp hcore hZ hB hrank hB4 hBC (n := n + 1) (by omega)
      Q.exponent_pos hKc hdiag e' rfl (by rw [hKc, TauCeti.PrimePower.card_def]) ⟨e⟩ hHq

theorem badClsAt_twistedA (hLU : ConcACaseLLUStatement) (hGA : GriessAllModelsStatement)
    {n : ℕ} {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA n Q).Valid) :
    BadClsAt ⟨.twistedA n Q, hv⟩ := by
  classical
  intro p q hp hp2 hq hq2 hqp Ω _ _ _ S B hSn hperf hcore hchar he hB _ hrank hB4 hBC hp3B hHq
  obtain ⟨e⟩ := he
  haveI := hSn
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩ = Q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA n Q
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩ = Q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA n Q
  have hcq : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩ = q := hchar
  subst hcq
  have hn : 2 ≤ n := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hf0 := TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA n Q, hv⟩
  have h : UnitaryFieldData (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩)
      (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩)
      (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩)) :=
    ⟨hq, hf0, GaloisField.card _ _ (by omega)⟩
  have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj n Q hv)
  by_cases hdiag : p ∣ Nat.gcd (n + 1)
      (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n Q, hv⟩ ^
        TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n Q, hv⟩ + 1)
  · exact Or.inl (concA_caseL_uni hLU hp hp2 hperf hcore hB hrank hB4 hBC hp3B (by omega) h
      hq2 hdiag e')
  · have hZ : Subgroup.center ↥S = ⊥ := ModelGen.center_eq_bot_of_classical hGA hp hp2 hperf
      hcore (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n Q hv e)
      (by rw [← hc]; exact Ne.symm hqp) (fun h => by cases h) (fun _ => by rwa [hc, hfe] at hdiag)
    exact concl_uni hp hp2 h hq2 hqp hcore hZ hB hrank hB4 hBC (n := n + 1) (by omega) hdiag e'
      hc.symm (by rw [TauCeti.PrimePower.card_def, hc, hfe]) ⟨e⟩ hHq

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls

end
