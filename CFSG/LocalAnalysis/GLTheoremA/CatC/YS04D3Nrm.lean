module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Comp
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBarLayer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

theorem d3_conj_normalizes_of_rank {G : Type} [Group G] [Finite G] (T112 : Tables112) (TL2 : TableL2)
    (TT : Tables112Types) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    {X B J : Subgroup G} (hB : IsElemAbelian 3 B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B) (hJ : GLAPComponent 3 X J)
    (hrk : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J)))) :
    B ≤ Subgroup.normalizer (J : Set G) := by
  by_contra hn
  obtain ⟨-, -, -, h3, -⟩ := i112c_full T112 TL2 TT hsimple hKP Nat.prime_three (by norm_num) hB hBX
    hr hJ hn
  omega

theorem d3_exists_invariant_two_subgroup {G : Type} [Group G] [Finite G] (T112 : Tables112)
    (TL2 : TableL2) (TT : Tables112Types) (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G)
    {B J : Subgroup G} {x : G} (hB : GLAIsBmax 3 B) (hx : IsEssential 3 B x)
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) J)
    (hrk : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J)))) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      T ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hxB, -, T₀, hT₀x, hT₀2, hBT₀, hcomm, -⟩ := hx
  set X := Subgroup.centralizer ({x} : Set G) with hX
  have hBX : B ≤ X := isElemAbelian_le_centralizer hB.1 hxB
  have hp : Nat.Prime 3 := Nat.prime_three
  have hconj : ∀ s ∈ X, ∀ b ∈ B, s * b * s⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
    intro s hs b hb
    set B' : Subgroup G := B.map (MulAut.conj s).toMonoidHom with hB'
    have hB'el : IsElemAbelian 3 B' := isElemAbelian_map_equiv (MulAut.conj s) hB.1
    have hB'X : B' ≤ X := by
      rintro _ ⟨c, hc, rfl⟩
      exact X.mul_mem (X.mul_mem hs (hBX hc)) (X.inv_mem hs)
    have hB'card : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective (MulAut.conj s).injective
    have hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B' := by
      have h1 : GLATwoLocalRank 3 ↥X ≤ GLATwoLocalRank 3 G := glaTwoLocalRank_subgroup_le hp X
      have h2 : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B' :=
        CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'el (by rw [hB'card, hB.2.1])
      exact h1.trans h2
    have := d3_conj_normalizes_of_rank T112 TL2 TT hsimple hKP hB'el hB'X hr hJ hrk
    exact this ⟨b, hb, rfl⟩
  have hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (J : Set G) := fun b hb => by
    simpa using hconj 1 X.one_mem b hb
  have hle : ⁅T₀, B⁆ ≤ T₀ := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    rw [commutatorElement_def]
    have h1 : k * h⁻¹ * k⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.1 (hBT₀ hk) h⁻¹).1 (T₀.inv_mem hh)
    simpa [mul_assoc] using T₀.mul_mem hh h1
  have hinv : ∀ b ∈ B, ∀ y ∈ ⁅T₀, B⁆, b * y * b⁻¹ ∈ ⁅T₀, B⁆ := by
    intro b hb y hy
    have hle' : (⁅T₀, B⁆).map (MulAut.conj b).toMonoidHom ≤ ⁅T₀, B⁆ := by
      rw [Subgroup.map_commutator]
      apply Subgroup.commutator_mono
      · rintro _ ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 (hBT₀ hb) z).1 hz
      · rintro _ ⟨z, hz, rfl⟩
        exact B.mul_mem (B.mul_mem hb hz) (B.inv_mem hb)
    exact hle' ⟨y, hy, rfl⟩
  refine ⟨⁅T₀, B⁆, hcomm, hT₀2.to_le hle, fun b hb => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hinv b hb y, fun hy => ?_⟩
    simpa [mul_assoc] using hinv b⁻¹ (B.inv_mem hb) _ hy
  · rw [Subgroup.commutator_le]
    intro h hh k hk
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hconj h (hT₀x hh) k hk) (Subgroup.inv_mem _ (hBN k hk))

end CFSG.LocalAnalysis.GLTheoremA
