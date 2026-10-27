module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieExc
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.HardMathSupport.Lang.E6Descent (G2_form_even G2_form_three G2_form_odd
  exists_conj_eq_entrywiseAdjointAut_of_form)

section


theorem pRank_adjoint_le_fixed_entrywise_anychar {p : ℕ} (hp1 : 1 < p) (τ : Tag) {M : Type}
    [Field M] [Finite M] (σ : M ≃+* M) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) ≤
      CFSG.Open.pRank p (fixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  have hJΓ : fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ := fixedFieldImage_le
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ M := hJΓ.trans inf_le_left
  set J : Subgroup ↥(adjointGroup τ M) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ M)
  have hmemJ : ∀ x : ↥(adjointGroup τ M), x ∈ J ↔ (x : ModGL τ M) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixedSubgroup (entrywiseAdjointAut τ σ) := fun x hx => by
    refine Subtype.ext ?_
    change ((entrywiseAdjointAut τ σ x : ↥(adjointGroup τ M)) : ModGL τ M) = (x : ModGL τ M)
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ).symm
  have h2 : CFSG.Open.pRank p J = CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top J
  have h3 := CFSG.SectionRank.pRank_mono (p := p) hp1 hJC
  omega

theorem descent_fixed_adjoint_G2 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hne : ℓ ≠ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (hK3 : 3 ≤ ℓ ^ f) (α : MulAut (adjointGroup Tag.G2 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.G2 k)) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  have hform : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hf2 : 2 ≤ f := by
        by_contra h
        have : f = 1 := by omega
        subst this
        omega
      exact G2_form_even hf2 K hK hp α hαord hα
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      have : CharP K 3 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
      exact G2_form_three hf K hK hp (by omega) α hαord hα
    · exact G2_form_odd hℓ hℓ2 hℓ3 hf K hK hp α hαord hα
  obtain ⟨x, σ, hσp, hασ⟩ := hform
  obtain ⟨δ, hδ⟩ :=
    exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ hσp hασ
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ
  rw [hσp] at hdvd hcard
  have h1 := pRank_adjoint_le_fixed_entrywise_anychar hp.one_lt Tag.G2 σ
  have h2 := pRank_fixed_le_of_intertwine hp.one_lt δ α (entrywiseAdjointAut Tag.G2 σ)
    (intertwine_of_conj hδ)
  exact ⟨hdvd, fixSubfield σ, inferInstance, inferInstance, hcard, le_trans h1 h2⟩

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
