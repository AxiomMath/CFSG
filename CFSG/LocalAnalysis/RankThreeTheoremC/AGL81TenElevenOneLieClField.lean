module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClOuter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClIndex
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.OuterOrder (higher_linear_unitary_outer_order_determinant_bound
  determinantParameter)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer)

namespace LieClAut

@[expose] def FieldExponentThree : TauCeti.LieTypeIndex → Prop
  | .A _ Q => 3 ∣ Q.exponent
  | .twistedA _ Q => 3 ∣ Q.exponent
  | .B _ Q => 3 ∣ Q.exponent
  | _ => True

variable {X : Type} [Group X] [Finite X]

theorem not_three_dvd_outer {d : TauCeti.ValidLieTypeIndex} (hd : IsRankTwoPlus d.1)
    (hlist : RankTwoList d.1 ∨ RankThreeList d.1) (hA2 : ∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q)
    (hF : ¬ FieldExponentThree d.1) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨d, hv⟩ := d
  intro h3
  have key : ∀ f g : ℕ, ¬ 3 ∣ f → ¬ 3 ∣ g → ¬ 3 ∣ 2 * f * g := fun f g hf hg h => by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
      · omega
      · exact hf h
    · exact hg h
  cases d with
  | A l q =>
    have hp : q.p = 2 := hd.1
    have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hp] at hM
    have hout := (higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
      (by have := hd.2; omega) Nat.prime_two q.exponent_pos hM).1
    refine key q.exponent _ hF ?_ (h3.trans hout)
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    have hl := hd.2
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · omega
    · omega
    · exact hA2 q rfl
    · omega
    · omega
    · simp only [RankTwoList, RankThreeList, false_or] at hlist
      obtain ⟨k, hk⟩ := hlist
      have h : 2 ^ q.exponent % 3 = 2 := by
        rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have := Nat.one_le_two_pow (n := q.exponent)
      omega
    · omega
    · rcases hlist with h | h <;> exact h.elim
  | twistedA l q =>
    have hp : q.p = 2 := hd.1
    have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA l q hv e
    rw [hp] at hM
    have hout := (higher_linear_unitary_outer_order_determinant_bound (Or.inr rfl)
      (by have := hd.2; omega) Nat.prime_two q.exponent_pos hM).1
    refine key q.exponent _ hF ?_ (h3.trans hout)
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    have hl := hd.2
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · omega
    · omega
    · omega
    · omega
    · omega
    · simp only [RankTwoList, RankThreeList, false_or] at hlist
      obtain ⟨k, hk⟩ := hlist
      have h : 2 ^ q.exponent % 3 = 1 := by
        rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      omega
    · omega
    · rcases hlist with h | h <;> exact h.elim
  | B l q =>
    have hp : q.p = 2 := hd.1
    have hM : StatedClassicalModel X .PSp l q.p q.exponent := by
      rcases l with _ | _ | _ | _ | l
      · exact absurd hd.2 (by omega)
      · exact absurd hd.2 (by omega)
      · exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hp le_rfl e
      · rcases hlist with h | h <;> exact h.elim
    have hout := (CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound
      X l q.p q.exponent hM).2.1
    refine key q.exponent _ hF ?_ (h3.trans hout)
    intro hg
    have := Nat.le_of_dvd (by norm_num) (hg.trans (Nat.gcd_dvd_left 2 _))
    omega
  | _ => exact hF trivial

end LieClAut

@[expose] def KFactTenElevenOneLieAutField : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
    (RankTwoList d.1 ∨ RankThreeList d.1) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    LieClAut.FieldExponentThree d.1 →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ u : Y, (∃ k : ℕ, u ^ 3 ^ k = 1) ∧ u ∉ L ⊔ Subgroup.centralizer (L : Set Y)) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) → False

theorem kFactTenElevenOneLieAutOuter_of_field (hF : KFactTenElevenOneLieAutField) :
    KFactTenElevenOneLieAutOuter := by
  intro Y _ _ L hLn hq hO2 d hd hlist hA2 he hu hJ hC3 hrk hE hN
  by_cases h3 : LieClAut.FieldExponentThree d.1
  · exact hF Y L hLn hq hO2 d hd hlist hA2 h3 he hu hJ hC3 hrk hE hN
  · haveI := hLn
    obtain ⟨e⟩ := he
    exact LieClAut.false_of_autThreePowInner_of_index hq hC3
      (autThreePowInner_of_not_three_dvd_outer
        (LieClAut.not_three_dvd_outer hd hlist hA2 h3 e)) hN

theorem kFactTenElevenOneLieAutRes_of_field (hF : KFactTenElevenOneLieAutField) :
    KFactTenElevenOneLieAutRes :=
  kFactTenElevenOneLieAutRes_of_outer (kFactTenElevenOneLieAutOuter_of_field hF)

end CFSG.LocalAnalysis.RankThreeTheoremC
