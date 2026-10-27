module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenQPlusTorus
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.EvenG2 CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2
  CFSG.Timmesfeld.ExceptionalOrders CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


theorem isQuasisimple_of_simple_perfect {G : Type*} [Group G] (hs : IsSimpleGroup G)
    (hperf : Group.IsPerfect G) (hnc : ∃ x y : G, x * y ≠ y * x) : CFSG.IsQuasisimple G := by
  have hc : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      have : y ∈ Subgroup.center G := h ▸ Subgroup.mem_top y
      exact hxy ((Subgroup.mem_center_iff.1 this x))
  let e : (G ⧸ Subgroup.center G) ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hperf, MulEquiv.isSimpleGroup e, ?_⟩
  obtain ⟨x, y, hxy⟩ := hnc
  exact ⟨e.symm x, e.symm y, fun h => hxy (by
    have := congrArg e h
    simpa using this)⟩

theorem even_lang_setup {X K₂ : Type} [Field X] [Finite X] [CharP X 2] [Field K₂] [Algebra X K₂]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card X + 1)
    (hdeg : Module.finrank X K₂ = 2) (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card X) :
    ∃ (P : SL2 K₂) (g : ModGL Tag.G2 K₂),
      g = rootSL2 .G2 K₂ g2a P⁻¹ * rootSL2 .G2 K₂ g2v P⁻¹ ∧
      (∃ S : Sylow p ↥(conjEntrywiseImage X g), (S : Subgroup ↥(conjEntrywiseImage X g)) ≤
        (torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g).subgroupOf (conjEntrywiseImage X g)) ∧
      (∀ x ∈ torusGroup .G2 K₂, ∀ y ∈ torusGroup .G2 K₂, x * y = y * x) ∧
      (∃ E : Subgroup (ModGL .G2 K₂), (∀ h, h ∈ E ↔ h ∈ torusGroup .G2 K₂ ∧ h ^ p = 1) ∧
        E ≤ torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g ∧ Nat.card E = p ^ 2) ∧
      (∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P' : GL (Fin 2) K₂,
        (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage X g).comap (rootSL2 .G2 K₂ α) =
          (Matrix.SpecialLinearGroup.map (algebraMap X K₂)).range.map (conjSL P') ∧
        CFSG.IsQuasisimple ↥(rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage X g)) ∧
      (∀ a : Fin Tag.G2.rank → K₂ˣ,
        rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g →
        orderOf (rootDiagUnit .G2 a) = p →
        (rootCharKernel a = ∅ →
          conjEntrywiseImage X g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
            torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g) ∧
        (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
          rootCharKernel a = {α, -α} ∧
          ⁅conjEntrywiseImage X g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
              conjEntrywiseImage X g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
            rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage X g)) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap X K₂).injective 2
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card X := Nat.card_pos
  have hdvd₂ : Nat.card X + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card X - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card X := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  obtain ⟨hinv, ω, hσω⟩ := exists_frobenius_eq_add_one hdeg σ hσ
  have hPn := evenQuadraticP_mul_nSL σ hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (evenQuadraticP ω)⁻¹ *
      rootSL2 .G2 K₂ g2v (evenQuadraticP ω)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a 1 * rootWeylSL2 .G2 K₂ g2v 1 := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hT := torusGroup_inf_eq_torusTorsion hzN hw (σ : K₂ →+* K₂) hσ hΓ
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 K₂).1
  have hTΓ : torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g ≤ conjEntrywiseImage X g := inf_le_right
  have hcardΓ : Nat.card (conjEntrywiseImage X g) = CFSG.Open.ordG2 (Nat.card X) := by
    rw [natCard_conjEntrywiseImage, card_adjointGroup_G2]
  have hcardT : Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g :
      Subgroup (ModGL .G2 K₂)) = (Nat.card X + 1) ^ 2 := by
    rw [hT]
    exact natCard_torusTorsion hdvd₂
  have hidx : ¬ p ∣ ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage X g).subgroupOf
      (conjEntrywiseImage X g)).index := by
    refine not_dvd_of_sq_mul_eq_ordG2 hq1 hp hp3 hpq ?_
    rw [← hcardΓ, ← hcardT, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv]
    exact Subgroup.card_mul_index _
  refine ⟨evenQuadraticP ω, g, hgdef, exists_sylow_le_of_not_dvd_index hidx, hHcomm, ?_,
    fun α hα => ?_, fun a hadT ha => ?_⟩
  · have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨torusTorsion K₂ p, fun h => mem_torusTorsion_iff, ?_, natCard_torusTorsion
      (hpq.trans hdvd₂)⟩
    rw [hT]
    exact torusTorsion_mono hpq
  · obtain ⟨P, hP, -⟩ := rootSL2_comap_fixed_eq_of_charTwo hdeg σ hσ hg hzdef hzN hw hα
    obtain ⟨hs, hperf, hnc⟩ := isSimpleGroup_of_rootSL2_comap_eq hq4 inf_le_left hP
    exact ⟨P, hP, isQuasisimple_of_simple_perfect hs hperf hnc⟩
  · obtain ⟨h1, h2⟩ := qplus_prime_element_centralizer_of_charTwo hp hp3 hpq hdeg σ hσ hg hzdef
      hzN hw a ha
    refine ⟨h1, fun hker => ?_⟩
    obtain ⟨α, hα, hk, hc, -⟩ := h2 hker
    exact ⟨α, hα, hk, hc⟩

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
