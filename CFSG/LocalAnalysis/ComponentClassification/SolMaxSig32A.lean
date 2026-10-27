module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDich

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

theorem pump_type (hPump : Sol78.AlternatingPumpUpInput) {Y : Type} [Group Y] [Finite Y]
    (hK : SectionRank.IsKGroupCat Y) {x : Y} (hx : orderOf x = 2) {T : Subgroup Y}
    (hTC : T ≤ centralizer ({x} : Set Y))
    (hTpc : IsPComponent 2 (T.subgroupOf (centralizer ({x} : Set Y)))) {k : ℕ} (hk : Odd k)
    (hk7 : 7 ≤ k) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin k)) :
    ∃ M : Subgroup Y, IsPComponent 2 M ∧ T ≤ M ⊔ conjugate M x ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set Y))) ∧
      ((conjugate M x = M ∧
          ((∃ m' : ℕ, Odd m' ∧ k ≤ m' ∧
              Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m'))) ∨
            (k = 7 ∧ Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.He)))) ∨
        (conjugate M x ≠ M ∧
          Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin k)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTE : T ≤ pLayer Y 2 := FooteLit.le_pLayer_of_isPComponent_centralizer_singleton hx hTC hTpc
  obtain ⟨M, hM, hTM, hTMpc⟩ := UnbalancedLayer.two_layer_fixed_component_orbit_location hx hTC
    hTpc hTE
  have hZT : Open.fusionZStar ↥T = pPrimeCore 2 ↥T := fusionZStar_eq_of_alt (by omega) eT
  let eTZ : ↥T ⧸ Open.fusionZStar ↥T ≃* alternatingGroup (Fin k) :=
    (QuotientGroup.quotientMulEquivOfEq hZT).trans eT
  refine ⟨M, hM, hTM, hTMpc, ?_⟩
  by_cases hfix : conjugate M x = M
  · refine Or.inl ⟨hfix, ?_⟩
    have hxN : x ∈ normalizer (M : Set Y) := mem_normalizer_of_conjugate_eq' hfix
    rw [hfix, sup_idem] at hTM
    have hZ : (Open.fusionZStar ↥T).map T.subtype ≤
        (pPrimeCore 2 ↥T).map T.subtype ⊔ (Open.fusionZStar ↥M).map M.subtype := by
      rw [hZT]
      exact le_sup_left
    rcases hPump Y hK M hM x hx hxN T hTM hTC hTpc hZ k hk hk7 ⟨eTZ⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  · obtain ⟨φ⟩ := CatLeaf.swap_case_type hx M hM (Ne.symm hfix) T (le_inf hTM hTC) hTMpc
    exact Or.inr ⟨hfix, ⟨φ.symm.trans eTZ⟩⟩

end CFSG.ComponentClassification.SolMax
