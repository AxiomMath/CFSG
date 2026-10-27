module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.AltHeartModel
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle.NaturalSection
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutatorFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AbstractGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Cooperstein
open scoped commutatorElement

variable {G : Type} [Group G]

theorem coprime_three_card_ker [Finite G] {S L : Subgroup G} (hS : IsPGroup 2 ↥S) {Γ : Type} [Group Γ]
    (φ : ↥L →* Γ) (hφ : ∀ l : ↥L, φ l = 1 → (l : G) ∈ S) :
    Nat.Coprime 3 (Nat.card φ.ker) := by
  have h2 : IsPGroup 2 φ.ker := by
    let g : φ.ker → ↥S := fun l => ⟨((l : ↥L) : G), hφ l l.2⟩
    have hg : Function.Injective g := fun a b hab => by
      have h : ((g a : ↥S) : G) = ((g b : ↥S) : G) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    exact IsPGroup.of_injective hS
      { toFun := g
        map_one' := rfl
        map_mul' := fun _ _ => rfl } hg
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem exists_bigVector_of_alt' [Finite G]
    (h86 : Asc81bEightSix) (h85 : Coordinator.GF2EightFive)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {N : ℕ}
    (hN : 12 ≤ N) (e : ↥(barM M L) ≃* alternatingGroup (Fin N)) :
    ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      3 ≤ Open.pRank 3 (L ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  set V := blockV S L with hV
  set U : Subgroup G := ⁅V, L⁆ with hU
  obtain ⟨hSLn, -⟩ := hpr.weakSBlock_asc81bHyp h86 hL
  have hfacts := hpr.blockV_facts h86 hL
  have hVe : IsElemAbelian 2 V := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hΩV : Quasithin.omegaOneCenterOf S ≤ V := hfacts.2.2.1.le.trans inf_le_left
  have hVS : V ≤ S :=
    (QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hfacts.2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := fun l hl =>
    Coordinator.sup_le_normalizer_blockV S L (Subgroup.mem_sup_left hl)
  have hSV : S ≤ Subgroup.normalizer (V : Set G) := Proving.le_normalizer_blockV S L
  have hUV : U ≤ V := commutator_le_of_le_normalizer hLV
  have hSU : S ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of_normalizes hSV hSLn
  have hLU : L ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_forall_conj_mem fun ℓ hℓ y hy => conj_mem_commutator hLV hy hℓ
  have hmov : ¬ L ≤ Subgroup.centralizer (Quasithin.omegaOneCenterOf S : Set G) := fun h =>
    hL.not_le_normalizer (by
      have hH : L ≤ H := by
        rw [← hpr.normalizer_thompsonJ_eq.2]
        exact h.trans (Subgroup.centralizer_le_normalizer _)
      rw [← hpr.normalizer_twoCore_H] at hH
      exact hH)
  have hU1 : U ≠ ⊥ := by
    intro h
    apply hmov
    have h1 : V ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have := Subgroup.mem_centralizer_iff.mp (h1 (hΩV hv)) l hl
    exact this.symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxU, hx1, hxS⟩ :=
    TightPairAndPureRank.exists_ne_one_mem_centralizer_of_pGroup
      (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
      (hUV.trans hVS) hSU hU1
  have hx2 : x ^ 2 = 1 := hVe.2 x (hUV hxU)
  have hxΩ : x ∈ Quasithin.omegaOneCenterOf S :=
    Subgroup.subset_closure ⟨⟨hVS (hUV hxU), hxS⟩, hx2⟩
  refine ⟨x, hxΩ, hx1, ?_⟩
  obtain ⟨φ, ι, hφs, hφk, hadd, hker, hequiv, -⟩ :=
    altNaturalSection_blockV h85 hpr.isKGroup.1 hpr.asc81bHyp hL (by omega) e
  have : Finite (alternatingGroup (Fin N)) := inferInstance
  have hrd := rankDropModel_of_altPermSubImage (by omega) (isAltPermSubImage_altHeart N)
  have hU2 : ∀ y ∈ U, y ^ 2 = 1 := fun y hy => hVe.2 y (hUV hy)
  have hcop := coprime_three_card_ker (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H)
    φ hφk
  have h1 := pRank_le_pRank_centralizer_add_one_of_model hLU hU2 φ hφs hcop ι hadd hker hequiv hrd
    x hxU
  have h4 : 4 ≤ Open.pRank 3 L := by
    have hle := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup hN
    have := CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e
    have hb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
        (by norm_num) M L hL.le]
    omega
  omega

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AltSocle

end
