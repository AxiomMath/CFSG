module

public import CFSG.LocalAnalysis.GL83PartI.I713.Chain
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

theorem outClauseFor_of_isCyclic_outer {K : Type*} [Group K] [Finite K] (h : IsCyclic (Outer K)) :
    OutClauseFor K := by
  intro p hp _ _
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (Outer K))
  have hle := card_le_of_isElemAbelian_of_isCyclic hp hE inferInstance
  rw [hcard] at hle
  by_contra hlt
  have h2 : p ^ 2 ≤ p ^ pRank p (⊤ : Subgroup (Outer K)) :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have h3 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

theorem outClauseFor_suzuki {S : Type} [Group S] [Finite S]
    {p f : ℕ} (h : CFSG.Blueprint.SuzukiModel S p f) : OutClauseFor S := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  subst hf
  obtain ⟨-, -, -, -, hcyc, -, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  haveI := Finite.of_equiv S e.toEquiv
  exact OutClauseFor.of_mulEquiv e (outClauseFor_of_isCyclic_outer hcyc)

theorem outClauseFor_reeTits {S : Type} [Group S] [Finite S]
    {t : CFSG.Open.StatedLieTag} {p f : ℕ} (ht : t ∈ CFSG.Blueprint.reeTitsTags)
    (h : CFSG.Blueprint.ReeTitsModel S t p f) : OutClauseFor S := by
  simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  ·
    obtain ⟨-, -, hp3, ⟨a₀, ha₀, hfa₀⟩, hiso⟩ :=
      CFSG.LieType.Ree.small_Ree_model_Schreier S p f h
    obtain ⟨-, a, hfa, K, _, _, hK, ⟨e⟩⟩ := h
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK, hp3]
      rfl)
    obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
    have ha : 1 ≤ a := by omega
    have hK' : Nat.card K = 3 ^ (2 * a + 1) := by rw [hK, hp3, hfa]
    haveI := Finite.of_equiv S E.toEquiv
    exact OutClauseFor.of_mulEquiv E (outClauseFor_of_isCyclic_outer
      (CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic ha hK').1)
  ·
    obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_model_field_outer_group_and_inner_involutions S p f h
    exact outClauseFor_of_isCyclic_outer hcyc
  ·
    obtain ⟨E⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S p f h
    haveI := Finite.of_equiv S E.toEquiv
    have hT := CFSG.Sporadic.Schreier.Tits.card_outer_titsD
    exact OutClauseFor.of_mulEquiv E (outClauseFor_of_card_outer_le_four (by rw [hT]; norm_num))

end GL83.I713
