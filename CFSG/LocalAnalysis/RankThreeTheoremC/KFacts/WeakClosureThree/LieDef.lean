module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDefSmall
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartOne.CTP.StrongPCharPU
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.SectionRank
open CFSG.ComponentClassification.CatLeaf (lieSylowExponent)
open CFSG.RankThree.PartOne.StrongP

section Order


theorem dichLieDef_PSL : DichLieDefAt .PSL := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ h3
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstated := hmodel.statedClassicalModel (by decide)
  obtain ⟨-, hf, hrank⟩ := classical_model_rank (by norm_num) hstated
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSL n 3 f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)
  · exact dichThreeLieAt_of_four_le_pRank h4
  rcases hrank with ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · refine dichThreeLieAt_of_factorization_le_pRank ?_
    rw [hord]
    simp only [lieSylowExponent]
    omega
  · have hf1 : f = 1 := by omega
    subst hf1
    obtain ⟨e⟩ :=
      CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 3 3 1 hstated
    refine dichThreeLieAt_of_pair_of_le ?_ ((hasNoncommPair_psl 3 3 (K := GaloisField 3 1) le_rfl
      le_rfl).map e.symm.toMonoidHom e.symm.injective)
    rw [hord]
    simp [lieSylowExponent]
  · exact absurd h h4
  · cases h
  · cases h
  · exact absurd h h4

theorem dichLieDef_PSU : DichLieDefAt .PSU := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ h3
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstated := hmodel.statedClassicalModel (by decide)
  obtain ⟨-, hf, hrank⟩ := classical_model_rank (by norm_num) hstated
  have hord := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .PSU n 3 f
    hadm hmodel).2.2
  by_cases h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)
  · exact dichThreeLieAt_of_four_le_pRank h4
  rcases hrank with ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | ⟨h, -⟩ | h
  · cases h
  · have hf1 : f = 1 := by omega
    subst hf1
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hstated
    haveI hcp : CharP F 3 := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 1 * 2)
        (by rw [← Nat.card_eq_fintype_card, hF, pow_mul])
    obtain ⟨a', ha'⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_ne hF
    have hpair : HasNoncommPair 3 (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (3 ^ 1) F)) :=
      NoncentralPair.hasNoncommPair (noncentralPair_statedSU hF 3
        (noncentralPair_su3 _ (fun c => CFSG.LieType.BorelTits.unitaryInvolution_involutive hF c)
          le_rfl (fun a ha => CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hF ha) ha'))
    refine dichThreeLieAt_of_pair_of_le ?_ (hpair.map e.symm.toMonoidHom e.symm.injective)
    rw [hord]
    simp [lieSylowExponent]
  · exact absurd h h4
  · cases h
  · exact absurd h h4

end Order

private theorem dichLieDef_of_orthogonal (t : StatedLieTag) (ht : t ∈ classicalTags)
    (h1 : t ≠ .PSL) (h2 : t ≠ .PSU) (h3 : t ≠ .PSp) : DichLieDefAt t := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ _
  subst hℓ
  obtain ⟨-, -, hrank⟩ := classical_model_rank (by norm_num) (hmodel.statedClassicalModel ht)
  apply dichThreeLieAt_of_four_le_pRank
  rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  · exact absurd h h1
  · exact absurd h h2
  · exact absurd h h3
  · exact h

theorem dichLieDef_POmegaOdd : DichLieDefAt .POmegaOdd :=
  dichLieDef_of_orthogonal .POmegaOdd (by decide) (by decide) (by decide) (by decide)

theorem dichLieDef_POmegaPlus : DichLieDefAt .POmegaPlus :=
  dichLieDef_of_orthogonal .POmegaPlus (by decide) (by decide) (by decide) (by decide)

theorem dichLieDef_POmegaMinus : DichLieDefAt .POmegaMinus :=
  dichLieDef_of_orthogonal .POmegaMinus (by decide) (by decide) (by decide) (by decide)

section Rank


theorem dichLieDef_PSp : DichLieDefAt .PSp := by
  intro K _ _ hs hnab n ℓ f hadm hmodel hℓ h3
  subst hℓ
  obtain ⟨-, hf, hrank⟩ := classical_model_rank (by norm_num)
    (hmodel.statedClassicalModel (by decide))
  by_cases h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)
  · exact dichThreeLieAt_of_four_le_pRank h4
  rcases hrank with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨rfl, h⟩ | h⟩ | h
  · cases h
  · cases h
  · have hf1 : f = 1 := by omega
    subst hf1
    exact dichThreeLieAt_psp4_three K hmodel
  · exact absurd h h4
  · exact absurd h h4

theorem dichLieDef_F4 : DichLieDefAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm
  exact dichThreeLieAt_of_four_le_pRank (by omega)

theorem dichLieDef_E6 : DichLieDefAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm
  exact dichThreeLieAt_of_four_le_pRank (by omega)

theorem dichLieDef_E7 : DichLieDefAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inl rfl))) hm
  exact dichThreeLieAt_of_four_le_pRank (by omega)

theorem dichLieDef_E8 : DichLieDefAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h4 := four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inr (Or.inr rfl))) hm
  exact dichThreeLieAt_of_four_le_pRank (by omega)

theorem dichLieDef_twistedE6 : DichLieDefAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank (four_le_pRank_of_twistedE6Model hf hm)

theorem dichLieDef_trialityD4 : DichLieDefAt .trialityD4 := by
  intro K _ _ _ _ n ℓ f _ hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank (four_le_pRank_of_trialityD4Model hf hm)

theorem dichLieDef_G2 : DichLieDefAt .G2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ _
  subst hℓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨_, hf, _⟩, hm⟩ :=
    hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  have h3 := three_mul_le_pRank_of_G2Model hm
  by_cases hf1 : f = 1
  · subst hf1
    obtain ⟨_, _, hn0, _⟩ := hadm
    subst hn0
    exact dichThreeLieAt_G2_three K hmodel
  · exact dichThreeLieAt_of_four_le_pRank (by omega)

theorem dichLieDef_twistedG2 : DichLieDefAt .twistedG2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ _
  subst hℓ
  have hn0 : n = 0 := hadm.2.2.1
  subst hn0
  exact dichThreeLieAt_ree K f hmodel

end Rank

theorem dichLieDef_twistedB2 : DichLieDefAt .twistedB2 := by
  intro K _ _ _ _ n ℓ f hadm _ hℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem dichLieDef_twistedF4 : DichLieDefAt .twistedF4 := by
  intro K _ _ _ _ n ℓ f hadm _ hℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

theorem dichLieDef_Tits : DichLieDefAt .Tits := by
  intro K _ _ _ _ n ℓ f hadm _ hℓ _
  obtain ⟨_, _, _, h2, _⟩ := hadm
  omega

section All


theorem dichLieDef_all : ∀ t, DichLieDefAt t := by
  intro t
  cases t
  · exact dichLieDef_PSL
  · exact dichLieDef_PSU
  · exact dichLieDef_PSp
  · exact dichLieDef_POmegaOdd
  · exact dichLieDef_POmegaPlus
  · exact dichLieDef_POmegaMinus
  · exact dichLieDef_G2
  · exact dichLieDef_F4
  · exact dichLieDef_E6
  · exact dichLieDef_E7
  · exact dichLieDef_E8
  · exact dichLieDef_twistedE6
  · exact dichLieDef_trialityD4
  · exact dichLieDef_twistedB2
  · exact dichLieDef_twistedG2
  · exact dichLieDef_twistedF4
  · exact dichLieDef_Tits

end All

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
