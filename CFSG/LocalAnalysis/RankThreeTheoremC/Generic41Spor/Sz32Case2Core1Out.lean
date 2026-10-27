module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Cyc

theorem szh1_pRank_le_one_of_cyclic_sylow {L : Type} [Group L] [Finite L] (S : Sylow 5 L)
    (hS : IsCyclic (S : Subgroup L)) : CFSG.Open.pRank 5 (⊤ : Subgroup L) ≤ 1 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fintype (S : Subgroup L) := Fintype.ofFinite _
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E _ hE
  have hEp : IsPGroup 5 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨S', hES'⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L S' S
  have hmem : ∀ x ∈ E, g * x * g⁻¹ ∈ (S : Subgroup L) := by
    intro x hx
    have h3 : (S : Set L) = MulAut.conj g • (S' : Set L) := by
      rw [← hg]
      exact Sylow.coe_smul (p := 5) (G := L) (g := g) (P := S')
    have h4 : (MulAut.conj g) • x ∈ (MulAut.conj g) • (S' : Set L) :=
      Set.smul_mem_smul_set (hES' hx)
    rw [← h3] at h4
    exact h4
  let f : E → {a : (S : Subgroup L) // a ^ 5 = 1} := fun x =>
    ⟨⟨g * x * g⁻¹, hmem x x.2⟩, by
      apply Subtype.ext
      change (g * (x : L) * g⁻¹) ^ 5 = 1
      rw [conj_pow, hE.2 x x.2]
      simp⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : g * (x : L) * g⁻¹ = g * (y : L) * g⁻¹ := congrArg (fun a => (a.1 : L)) hxy
    apply Subtype.ext
    simpa using h1
  have h5 : Nat.card {a : (S : Subgroup L) // a ^ 5 = 1} ≤ 5 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (by norm_num)
  have h6 : Nat.card E ≤ 5 ^ 1 := by
    rw [pow_one]
    exact (Nat.card_le_card_of_injective f hf).trans h5
  exact h6

end Cyc

section Hom

theorem szh1o_exists_hom {Y : Type} [Group Y] {H L : Subgroup Y}
    (hHL : H ≤ Subgroup.normalizer (L : Set Y)) :
    ∃ ψ : H →* Outer ↥L, ∀ g : H,
      ψ g = 1 ↔ ∃ l ∈ L, ∀ x ∈ L, (g : Y) * x * (g : Y)⁻¹ = l * x * l⁻¹ := by
  let φ : H →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hHL)
  have hφ : ∀ (g : H) (x : ↥L), ((φ g x : ↥L) : Y) = (g : Y) * x * (g : Y)⁻¹ := fun g x => rfl
  refine ⟨(QuotientGroup.mk' (Inn ↥L)).comp φ, fun g => ?_⟩
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range]
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨l, l.2, fun x hx => ?_⟩
    have := congrArg (fun f : MulAut ↥L => ((f ⟨x, hx⟩ : ↥L) : Y)) hl
    simpa [hφ, MulAut.conj_apply] using this.symm
  · rintro ⟨l, hl, h⟩
    refine ⟨⟨l, hl⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hφ]
    simpa [MulAut.conj_apply] using (h x x.2).symm

end Hom

section Out

variable {Y : Type} [Group Y] [Finite Y]

theorem szh1_simple_data (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hz : Subgroup.center ↥L = ⊥) :
    IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ IsCatalogGroup ↥L := by
  obtain ⟨-, -, hperf, hq⟩ := hL
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq
  haveI hsimple : IsSimpleGroup ↥L := e.symm.isSimpleGroup
  have hnon : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    push_neg at hcon
    have hbot : commutator ↥L ≤ ⊥ := by
      show ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ ⊥
      refine Subgroup.commutator_le.2 ?_
      intro g₁ _ g₂ _
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcon g₁ g₂)
    rw [hperf] at hbot
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥L)
    exact ha (Subgroup.mem_bot.1 (hbot (Subgroup.mem_top a)))
  refine ⟨hsimple, hnon, ?_⟩
  let e' : ↥L ≃* ↥L ⧸ (⊥ : Subgroup ↥L) := (QuotientGroup.quotientBot (G := ↥L)).symm
  haveI hs' : IsSimpleGroup (↥L ⧸ (⊥ : Subgroup ↥L)) := e'.symm.isSimpleGroup
  have hn' : ∃ a b : ↥L ⧸ (⊥ : Subgroup ↥L), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnon
    refine ⟨e' a, e' b, fun h => hab (e'.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e' (hcat L ⊥ inferInstance hs' hn')

theorem szh1_inner_of_mem_O5 (hI713 : KFactI713Out) {H L A : Subgroup Y}
    (hHL : H ≤ Subgroup.normalizer (L : Set Y)) (hAH : A ≤ H)
    (hA : ∀ g ∈ A, ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹)
    (hs : IsSimpleGroup ↥L) (hn : ∃ a b : ↥L, a * b ≠ b * a) (hc : IsCatalogGroup ↥L)
    (hr : CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ 1)
    {y : Y} (hy : y ∈ H) (y5 : y ^ 5 = 1)
    (hyW : y ∈ Subgroup.closure {g : Y | g ∈ H ∧ Nat.Coprime (orderOf g) 5} ⊔ A) :
    ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ = l * x * l⁻¹ := by
  obtain ⟨ψ, hψ⟩ := szh1o_exists_hom hHL
  obtain ⟨-, N, hN, hN5, k, hk⟩ := hI713 5 (by norm_num) (by norm_num) ↥L hs hn hc hr
  haveI := hN
  let Θ : H →* Outer ↥L ⧸ N := (QuotientGroup.mk' N).comp ψ
  have hcop : ∀ g : H, Nat.Coprime (orderOf (g : Y)) 5 → Θ g = 1 := by
    intro g hg
    have h1 : orderOf (Θ g) ∣ 5 ^ k := by
      have := orderOf_dvd_natCard (Θ g)
      rwa [← Subgroup.index_eq_card, hk] at this
    have h2 : orderOf (Θ g) ∣ orderOf (g : Y) := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd Θ g
    have h3 : Nat.Coprime (orderOf (Θ g)) 5 := Nat.Coprime.coprime_dvd_left h2 hg
    exact orderOf_eq_one_iff.1 ((h3.pow_right k).eq_one_of_dvd h1)
  have hA1 : ∀ g : H, (g : Y) ∈ A → Θ g = 1 := by
    intro g hg
    have : ψ g = 1 := (hψ g).2 (hA g hg)
    simp [Θ, this]
  let K : Subgroup Y := Θ.ker.map H.subtype
  have hK1 : Subgroup.closure {g : Y | g ∈ H ∧ Nat.Coprime (orderOf g) 5} ≤ K := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgH, hgc⟩
    exact ⟨⟨g, hgH⟩, hcop ⟨g, hgH⟩ hgc, rfl⟩
  have hK2 : A ≤ K := fun g hg => ⟨⟨g, hAH hg⟩, hA1 ⟨g, hAH hg⟩ hg, rfl⟩
  obtain ⟨z, hz, hzy⟩ := (sup_le hK1 hK2) hyW
  have hz' : z = ⟨y, hy⟩ := Subtype.ext hzy
  rw [hz'] at hz
  have hΘ : Θ ⟨y, hy⟩ = 1 := hz
  have hyN : ψ ⟨y, hy⟩ ∈ N := (QuotientGroup.eq_one_iff _).1 hΘ
  refine (hψ ⟨y, hy⟩).1 ?_
  have hu5 : (ψ ⟨y, hy⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : H) ^ 5 = 1 := Subtype.ext y5
    rw [this, map_one]
  have h1 : orderOf (ψ ⟨y, hy⟩) ∣ 5 := orderOf_dvd_of_pow_eq_one hu5
  have h2 : orderOf (ψ ⟨y, hy⟩) ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨ψ ⟨y, hy⟩, hyN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  rcases (Nat.dvd_prime Nat.prime_five).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h2
    exact absurd h2 hN5

theorem szh1_inner_of_five_elt (hI713 : KFactI713Out) {H L : Subgroup Y}
    (hHL : H ≤ Subgroup.normalizer (L : Set Y))
    (hs : IsSimpleGroup ↥L) (hn : ∃ a b : ↥L, a * b ≠ b * a) (hc : IsCatalogGroup ↥L)
    (hr : CFSG.Open.pRank 5 (⊤ : Subgroup ↥L) ≤ 1)
    (hS : ∀ S : Sylow 5 ↥L, Nat.card (S : Subgroup ↥L) = 5)
    {y : Y} (hy : y ∈ H) {k : ℕ} (hk : y ^ (5 ^ k) = 1) :
    ∃ l ∈ L, ∀ x ∈ L, y * x * y⁻¹ = l * x * l⁻¹ := by
  obtain ⟨ψ, hψ⟩ := szh1o_exists_hom hHL
  have hnd : ¬ 5 ∣ Nat.card (Outer ↥L) :=
    (hI713 5 (by norm_num) (by norm_num) ↥L hs hn hc hr).1 hS
  refine (hψ ⟨y, hy⟩).1 ?_
  have hpow : (ψ ⟨y, hy⟩) ^ (5 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : H) ^ (5 ^ k) = 1 := Subtype.ext hk
    rw [this, map_one]
  have h1 : orderOf (ψ ⟨y, hy⟩) ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have h2 : ¬ 5 ∣ orderOf (ψ ⟨y, hy⟩) := fun h => hnd (h.trans (orderOf_dvd_natCard _))
  have hcop : Nat.Coprime (orderOf (ψ ⟨y, hy⟩)) 5 :=
    Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h2)
  exact orderOf_eq_one_iff.1 ((hcop.pow_right k).eq_one_of_dvd h1)

end Out

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
