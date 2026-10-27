module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

section Facts

variable {X : Type} [Group X] [Finite X]

theorem autOrderIn_le_pow_of_pRank' {p r : ℕ} (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hr : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ r) :
    autOrderIn B K ≤ p ^ r := by
  have hA : IsElemAbelian p (B ⊓ Subgroup.normalizer (K : Set X)) := CFSG.Open.IsElemAbelian.mono hB inf_le_left
  have h := autOrderIn_le_pow_of_pRank hp hA inf_le_right hr
  have e : autOrderIn (B ⊓ Subgroup.normalizer (K : Set X)) K = autOrderIn B K := by
    unfold autOrderIn
    rw [inf_assoc, inf_idem]
  rwa [e] at h

@[expose] def NNFactsZ (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) → P X K →
      (Subgroup.normalizer (K : Set X)).relIndex B = 3 ∧ autOrderIn B K ≤ 3 ^ 2 ∧
        IsElemAbelian 3 (bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)) ∧
        Nat.card ↥(bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)) ≤ 9

theorem nnFactsZ_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : NNFactsZ P := by
  intro X _ _ hXK K B hH hNN _
  obtain ⟨-, hidx, hrank, hZJ, -⟩ := i112f_core T TL TT hXK hH.prime hH.odd hH.core hH.scp.2.1
    hH.rank_local hH.comp hNN
  exact ⟨hidx, autOrderIn_le_pow_of_pRank' Nat.prime_three hH.scp.2.1 hrank, hZJ.1, hZJ.2⟩

theorem nnFacts_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : NNFacts P := fun X _ _ hXK K B hH hNN hP => by
  obtain ⟨h1, h2, -⟩ := nnFactsZ_of_tables T TL TT P X hXK K B hH hNN hP
  exact ⟨h1, h2⟩

end Facts

section Exc

@[expose] def NNExcZ (P : ∀ (X : Type) [Group X], Subgroup X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ K B : Subgroup X,
    I271Hyp 3 K B → ¬ B ≤ Subgroup.normalizer (K : Set X) →
      (Subgroup.normalizer (K : Set X)).relIndex B = 3 → CFSG.Open.pRank 3 B = 4 →
      autOrderIn B K = 3 ^ 2 →
      IsElemAbelian 3 (bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)) →
      Nat.card ↥(bClosure B K ⊓ Subgroup.centralizer (bClosure B K : Set X)) ≤ 9 → P X K →
        I271CaseA 3 K B ∨ IsStronglyBalancedIn 3 B K ∨ I271CaseC K B

theorem nnFor_of_excZ (P : ∀ (X : Type) [Group X], Subgroup X → Prop) (hF : NNFactsZ P)
    (hE : NNExcZ P) : NNFor P := by
  intro X _ _ hXK K B hH hNN hP
  obtain ⟨hidx, hAut, hZ1, hZ2⟩ := hF X hXK K B hH hNN hP
  rcases nn_caseA_or_exceptional hH hNN hidx hAut with h | ⟨h4, h9⟩
  · exact Or.inl h
  · exact hE X hXK K B hH hNN hidx h4 h9 hZ1 hZ2 hP

end Exc

theorem nnL2OddPow_holds (T : Tables112) (TL : TableL2)
    (TT : Tables112Types) : NNL2OddPow :=
  nnFor_of_exc (fun _ _ K => IsLTwoOddPow ↥K) (nnFacts_of_tables T TL TT _) nnExc_lTwoOddPow

end CFSG.HardMathSupport.Solomon.Coordinator
