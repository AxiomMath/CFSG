module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieExc
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedF4
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section


theorem pRank_adjoint_le_fixed_entrywise_anychar_F4 {p : ℕ} (hp1 : 1 < p) {M : Type} [Field M]
    [Finite M] (σ : M ≃+* M) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.F4 (fixSubfield σ))) ≤
      CFSG.Open.pRank p (fixedSubgroup (entrywiseAdjointAut Tag.F4 σ)) := by
  classical
  obtain ⟨-, -, -, hJΓ, -, -, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.F4 M σ
  have hJA : fixedFieldImage Tag.F4 σ ≤ adjointGroup Tag.F4 M := hJΓ.trans inf_le_left
  set J : Subgroup ↥(adjointGroup Tag.F4 M) :=
    (fixedFieldImage Tag.F4 σ).subgroupOf (adjointGroup Tag.F4 M) with hJ
  have hmemJ : ∀ x : ↥(adjointGroup Tag.F4 M),
      x ∈ J ↔ (x : ModGL Tag.F4 M) ∈ fixedFieldImage Tag.F4 σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixedSubgroup (entrywiseAdjointAut Tag.F4 σ) := fun x hx => by
    refine Subtype.ext ?_
    change ((entrywiseAdjointAut Tag.F4 σ x : ↥(adjointGroup Tag.F4 M)) : ModGL Tag.F4 M) =
      (x : ModGL Tag.F4 M)
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  let eJ : ↥J ≃* adjointGroup Tag.F4 (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv (τ := Tag.F4) σ).symm
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.F4 (fixSubfield σ))) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ).symm
  have h2 : CFSG.Open.pRank p J = CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top J
  have h3 := CFSG.SectionRank.pRank_mono (p := p) hp1 hJC
  omega

theorem descent_fixed_adjoint_F4 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hne : ℓ ≠ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.F4 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) :
    p ∣ f ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = ℓ ^ (f / p) ∧
      CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup Tag.F4 k)) ≤
        CFSG.Open.pRank p (fixedSubgroup α) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.F4 K)).one_mem)
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  obtain ⟨σ, δ, hσp, hδ⟩ : ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup Tag.F4 K)),
      orderOf σ = p ∧ δ * α * δ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      obtain ⟨σ, ψ, hσp, hψ⟩ :=
        CFSG.HardMathSupport.Lang.E6Descent.even_F4_odd_prime_field_descent hf K hK hp (by omega)
          α hαord hα
      exact ⟨σ, ψ, hσp, hψ⟩
    · obtain ⟨-, σ, δ, hσp, -, hδ, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαord hα
      exact ⟨σ, δ, hσp, hδ⟩
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ
  rw [hσp] at hdvd hcard
  refine ⟨hdvd, ↥(fixSubfield σ), inferInstance, inferInstance, hcard, ?_⟩
  have h1 := pRank_adjoint_le_fixed_entrywise_anychar_F4 hp.one_lt σ
  have h2 := pRank_fixed_le_of_intertwine hp.one_lt δ α (entrywiseAdjointAut Tag.F4 σ)
    (intertwine_of_conj hδ)
  exact h1.trans h2

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
