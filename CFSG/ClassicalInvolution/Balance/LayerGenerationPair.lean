module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimpleParam
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.Models.Transfer.Basic

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Statement

@[expose] def PairFrame {K : Type*} [Group K] (𝒯 : Subgroup K) (𝓡 : Set (Subgroup K)) : Prop :=
  ∀ R₁ ∈ 𝓡, ∀ R₂ ∈ 𝓡, ∀ c₁ ∈ R₁, ∀ c₂ ∈ R₂, (∀ r ∈ R₁, c₁ * r = r * c₁) →
    (∀ r ∈ R₂, c₂ * r = r * c₂) → (∀ r ∈ R₁, c₂ * r = r * c₂) → (∀ r ∈ R₂, c₁ * r = r * c₁) →
      ∃ g : K, g⁻¹ * c₁ * g ∈ 𝒯 ∧ g⁻¹ * c₂ * g ∈ 𝒯

@[expose] def LayerGenerationPairAt (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv t n p e hp).K →* X),
    ψ.ker ≤ Subgroup.center (modelUniv t n p e hp).K → CFSG.IsComponent ψ.range →
    ∀ R₁ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ R₂ ∈ fundamentalSubgroups t (modelUniv t n p e hp).D,
      ∀ z₁ ∈ R₁.map ψ, ∀ z₂ ∈ R₂.map ψ, (∀ y ∈ R₁.map ψ, z₁ * y = y * z₁) →
        (∀ y ∈ R₂.map ψ, z₂ * y = y * z₂) → (∀ y ∈ R₁.map ψ, z₂ * y = y * z₂) →
        (∀ y ∈ R₂.map ψ, z₁ * y = y * z₁) →
        ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
          F ≤ Subgroup.normalizer (ψ.range : Set X) →
          (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
          ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ≠ 1 → f₂ ≠ 1 → f₁ ≠ f₂ →
            (∀ y ∈ ψ.range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹) →
            (∀ y ∈ ψ.range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) →
              ψ.range ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f

@[expose] def LayerGenerationPair : Prop :=
  ∀ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), IsFundTag t → StatedLieAdmissible t n p e →
    p ≠ 2 → 5 ≤ p ^ e → LayerGenerationPairAt t n p e hp

theorem layerGenerationPair_of_model (h : LayerGenerationModel) : LayerGenerationPair := by
  intro t n p e hp hfund hadm hp2 h5 X _ _ ψ hker hcomp R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂
    hc₂₁ F h4 h2 hN hf f₁ hf₁ f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  by_cases hsl : t = .PSL ∧ n = 2
  · exfalso
    have htop : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp).D, R.map ψ = ψ.range := by
      intro R hR
      rw [fundamentalWholeA1 t n p e hp hfund hadm hsl R hR, Subgroup.map_top]
    have hz₁c : ∀ y ∈ ψ.range, z₁ * y = y * z₁ := fun y hy => hc₁ y (by rwa [htop R₁ hR₁])
    refine hf f₁ hf₁ hf₁1 fun y hy => ?_
    have h1 : f₁ * y * f₁⁻¹ = y := by
      rw [hact₁ y hy, hz₁c y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hK := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n p e hp hfund hadm
  have hn : t = .PSL → 3 ≤ n := fun ht => by
    have h2n : 2 ≤ n := by
      subst ht
      exact hadm.2.2.1
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · exact absurd ⟨ht, by omega⟩ hsl
    · exact h3
  have hLq : CFSG.Open.IsQuasisimple ↥ψ.range := ((CFSG.isComponent_iff_open _).mp hcomp).2.2
  have hψ1 : ∃ x, ψ.rangeRestrict x ≠ 1 := by
    have : Nontrivial (↥ψ.range ⧸ Subgroup.center ↥ψ.range) := hLq.2.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥ψ.range ⧸ Subgroup.center ↥ψ.range)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := ψ.rangeRestrict_surjective u
    refine ⟨x, fun h1 => hy ?_⟩
    rw [h1]
    rfl
  have hbig : IsOddLieComponentBig ψ.range :=
    isOddLieComponentBig_of_surjective hK.1 ψ.rangeRestrict ψ.rangeRestrict_surjective hψ1 hp2 h5 hn
      (isFundTag_mem_tags hfund) hK.2
  exact h X ψ.range hcomp hbig F h4 h2 hN hf

end Statement

section Assembly

theorem eq_one_or_eq_or_eq_mul_of_card_four {G : Type*} [Group G] {F : Subgroup G}
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1) {f₁ f₂ : G} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (h1 : f₁ ≠ 1) (h2 : f₂ ≠ 1) (h12 : f₁ ≠ f₂) :
    ∀ f ∈ F, f = 1 ∨ f = f₁ ∨ f = f₂ ∨ f = f₁ * f₂ := by
  classical
  intro f hf
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hcon
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have hinv2 : f₂⁻¹ = f₂ := inv_eq_of_mul_eq_one_right (hF2 f₂ hf₂)
  have e1 : f₁ * f₂ ≠ 1 := fun h => h12 (by
    have := mul_eq_one_iff_eq_inv.mp h
    rw [hinv2] at this
    exact this)
  have e2 : f₁ * f₂ ≠ f₁ := fun h => h2 (by simpa using h)
  have e3 : f₁ * f₂ ≠ f₂ := fun h => h1 (by simpa using h)
  let a : F := ⟨f₁, hf₁⟩
  let b : F := ⟨f₂, hf₂⟩
  let c : F := ⟨f₁ * f₂, F.mul_mem hf₁ hf₂⟩
  let d : F := ⟨f, hf⟩
  have hS : ({1, a, b, c, d} : Finset F).card = 5 := by
    have n1 : (1 : F) ∉ ({a, b, c, d} : Finset F) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> [exact h1 (congrArg Subtype.val h).symm;
        exact h2 (congrArg Subtype.val h).symm; exact e1 (congrArg Subtype.val h).symm;
        exact hc1 (congrArg Subtype.val h).symm]
    have n2 : a ∉ ({b, c, d} : Finset F) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> [exact h12 (congrArg Subtype.val h);
        exact e2 (congrArg Subtype.val h).symm; exact hc2 (congrArg Subtype.val h).symm]
    have n3 : b ∉ ({c, d} : Finset F) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_⟩ <;> intro h <;> [exact e3 (congrArg Subtype.val h).symm;
        exact hc3 (congrArg Subtype.val h).symm]
    have n4 : c ∉ ({d} : Finset F) := by
      simp only [Finset.mem_singleton]
      intro h
      exact hc4 (congrArg Subtype.val h).symm
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_insert_of_notMem n4, Finset.card_singleton]
  have := Finset.card_le_univ ({1, a, b, c, d} : Finset F)
  rw [hS, ← Nat.card_eq_fintype_card, hF4] at this
  omega

theorem layerGenerationPairAt_of_toral {t : StatedLieTag} {n p e : ℕ} [Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    {x : (Fin (modelUniv t n p e Fact.out).D.rank → ℤ) → GaloisField p e →
      (modelUniv t n p e Fact.out).K}
    (hP : SimpleParam (modelUniv t n p e Fact.out).D (GaloisField p e) x)
    (𝒯 : Subgroup (modelUniv t n p e Fact.out).K)
    (hshort : ToralShortRootFact (modelUniv t n p e Fact.out).D x
      (𝒯 : Set (modelUniv t n p e Fact.out).K))
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (modelUniv t n p e Fact.out).D)) :
    LayerGenerationPairAt t n p e Fact.out := by
  intro X _ _ ψ hker hcomp R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ F hF4 hF2 hFN hfaith f₁ hf₁
    f₂ hf₂ hf₁1 hf₂1 hf₁₂ hact₁ hact₂
  have hperf := CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund hadm
    (by omega)
  have hperf' : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ⁅R, R⁆ = R :=
    fun R hR => le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)) (hperf R hR)
  have cent : ∀ {R : Subgroup (modelUniv t n p e Fact.out).K}
      {c : (modelUniv t n p e Fact.out).K},
      ⁅R, R⁆ = R → (∀ y ∈ R.map ψ, ψ c * y = y * ψ c) → ∀ r ∈ R, c * r = r * c := by
    intro R c hR hc r hr
    have h := Models.Transfer.mem_centralizer_of_map (θ := ψ) hker hR (g := c)
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hc y hy).symm)
    exact (Subgroup.mem_centralizer_iff.mp h r hr).symm
  obtain ⟨c₁, hc₁R, rfl⟩ := hz₁
  obtain ⟨c₂, hc₂R, rfl⟩ := hz₂
  obtain ⟨g, hg₁, hg₂⟩ := hframe R₁ hR₁ R₂ hR₂ c₁ hc₁R c₂ hc₂R (cent (hperf' R₁ hR₁) hc₁)
    (cent (hperf' R₂ hR₂) hc₂) (cent (hperf' R₁ hR₁) hc₁₂) (cent (hperf' R₂ hR₂) hc₂₁)
  have h₁ : ∀ y : (modelUniv t n p e Fact.out).K, f₁ * ψ y * f₁⁻¹ = ψ (c₁ * y * c₁⁻¹) := fun y => by
    rw [hact₁ _ ⟨y, rfl⟩]
    simp only [map_mul, map_inv]
  have h₂ : ∀ y : (modelUniv t n p e Fact.out).K, f₂ * ψ y * f₂⁻¹ = ψ (c₂ * y * c₂⁻¹) := fun y => by
    rw [hact₂ _ ⟨y, rfl⟩]
    simp only [map_mul, map_inv]
  have hconj : ∀ f ∈ F, ∃ s ∈ 𝒯, ∀ y : (modelUniv t n p e Fact.out).K,
      f * ψ y * f⁻¹ = ψ (g * s * g⁻¹ * y * (g * s * g⁻¹)⁻¹) := by
    intro f hf
    rcases eq_one_or_eq_or_eq_mul_of_card_four hF4 hF2 hf₁ hf₂ hf₁1 hf₂1 hf₁₂ f hf with
      rfl | rfl | rfl | rfl
    · exact ⟨1, 𝒯.one_mem, fun y => by simp⟩
    · refine ⟨g⁻¹ * c₁ * g, hg₁, fun y => ?_⟩
      have e1 : g * (g⁻¹ * c₁ * g) * g⁻¹ = c₁ := by group
      rw [e1, h₁]
    · refine ⟨g⁻¹ * c₂ * g, hg₂, fun y => ?_⟩
      have e1 : g * (g⁻¹ * c₂ * g) * g⁻¹ = c₂ := by group
      rw [e1, h₂]
    · refine ⟨(g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g), 𝒯.mul_mem hg₁ hg₂, fun y => ?_⟩
      have e1 : g * ((g⁻¹ * c₁ * g) * (g⁻¹ * c₂ * g)) * g⁻¹ = c₁ * c₂ := by group
      have e2 : f₁ * f₂ * ψ y * (f₁ * f₂)⁻¹ = f₁ * (f₂ * ψ y * f₂⁻¹) * f₁⁻¹ := by group
      rw [e1, e2, h₂, h₁]
      simp only [map_mul, map_inv]
      group
  have hdiag : ∀ f ∈ F, ∀ i : Fin (modelUniv t n p e Fact.out).D.rank,
      ∃ b : (GaloisField p e)ˣ, ActsDiagonallyOnSimple x ψ g i f b := by
    intro f hf i
    obtain ⟨s, hs, hfs⟩ := hconj f hf
    obtain ⟨b, hb⟩ := (hshort s hs).1 i
    exact ⟨b, actsDiagonallyOnSimple_of_actsAsConj ψ g f hfs hb⟩
  have hidx : ∀ i : Fin (modelUniv t n p e Fact.out).D.rank,
      IndexTwoCentralizes F (rankOneImage (modelUniv t n p e Fact.out).D ψ g (Pi.single i 1)) :=
    fun i => hP.indexTwoCentralizes_rankOneImage_simple hker g i hF2 fun f hf => hdiag f hf i
  have hsub := ((CFSG.isComponent_iff_open _).mp hcomp).2.1
  rw [← iSup_rankOneImage_simple_eq_range t n p e Fact.out hfund hadm ψ g]
  refine iSup_le fun i => ?_
  obtain ⟨y, hy, hy1, hyc⟩ := exists_ne_one_centralizes_of_indexTwo hF2 le_rfl hF4 (hidx i)
  obtain ⟨s, hs, hys⟩ := hconj y hy
  obtain ⟨b, hb⟩ := (hshort s hs).1 i
  have hbψ : ActsDiagonallyOnSimple x ψ g i y b :=
    actsDiagonallyOnSimple_of_actsAsConj ψ g y hys hb
  have hb1 : b = 1 := hP.eq_one_of_centralizes_actsDiagonallyOnSimple hker g i hbψ hyc
  have hin := inComponentOfCentralizer_of_toralShortRootFact hshort hker g hs hys hb hb1
  exact (hin.le_centralizerLayer hsub).trans (le_iSup₂_of_le y hy (le_iSup_of_le hy1 le_rfl))

end Assembly

end CFSG.ClassicalInvolution.Balance.Bootstrap
