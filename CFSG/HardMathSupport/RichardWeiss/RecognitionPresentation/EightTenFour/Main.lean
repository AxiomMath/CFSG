module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.PushUp
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.Centre
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.BlockU
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShortClauses
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeLS

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM NineThreeFive blockV Asc81bEightFive
  IsTwoPrimeComponent HasIrreducibleCommutatorQuotient)
open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub barMHomSub_surjective ker_barMHomSub
  barMEquiv)
open scoped commutatorElement

def A7ExceptionalData {G : Type} [Group G] (S L : Subgroup G) : Prop :=
  (∀ s ∈ S, ∃ l ∈ L, ∀ v ∈ blockV S L, s * v * s⁻¹ = l * v * l⁻¹) ∧
    Nat.card ↥⁅blockV S L, L⁆ = 2 ^ 4

def EightTenFourOutcome : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin 7)) →
    A7ExceptionalData S L →
      NineThreeFive (L ⊔ S) L ∧ IsA7FourType L

theorem eightTenFourOutcome_of (hclass : A7PerfectSylow)
    (h85 : Asc81bEightFive) : EightTenFourOutcome := by
  intro G _ _ X S L hX hA hL hSL he hD
  obtain ⟨hact, h16⟩ := hD
  classical
  set M : Subgroup G := L ⊔ S with hM
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set V : Subgroup G := blockV S L with hV
  have hLs : IsTwoPrimeComponent M L :=
    Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp M S := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hLM : L ≤ M := le_sup_left
  have hQS : Q ≤ S := hA'.twoCore_le
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := sup_le_normalizer_blockV S L
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLM.trans hMV
  have hVQ : V ≤ Q := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hVL : V ≤ Subgroup.normalizer (L : Set G) := hVQ.trans (hQS.trans hSL)
  have hQV := commutator_pCore_le_blockV_a7 hclass h85 hX hA hL hact he
  have hVel : CFSG.Open.IsElemAbelian 2 V := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _
  have hidx : (Subgroup.center ↥(barM M L)).index = 2520 := by
    obtain ⟨e⟩ := he
    show Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) = 2520
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) :=
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.odd_card_center_barM_sup hA' hSL
  have hZ : Subgroup.center ↥(barM M L) = ⊥ :=
    center_barM_eq_bot hLs hidx hodd hVel hLV hVL h16 hA'.charTwo hQV
  have hirr := hasIrr_of_card_sixteen hLs hidx.ge hVel hLV hVL h16
  have hcenX : Subgroup.center ↥(barM X L) = ⊥ := by
    let eXM := barMEquiv hL.le hLM (inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL)
    rw [eq_bot_iff]
    intro z hz
    have h1 : eXM z ∈ Subgroup.center ↥(barM M L) := by
      rw [← Subgroup.map_center_eq eXM]
      exact ⟨z, hz, rfl⟩
    rw [hZ, Subgroup.mem_bot] at h1
    have : z = 1 := eXM.injective (by rw [h1, map_one])
    rw [this]; exact Subgroup.one_mem _
  have hshort : IsShort2 L :=
    StructureLie.isShort2_of_hQV_of_center_eq_bot hX hA hL hirr.2 hQV hcenX
  have hU : blockU L = ⁅V, L⁆ := blockU_eq_commutator hLs hVQ hVL hLV hQV
  have e' : Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := he
    exact ⟨(QuotientGroup.quotientBot (G := ↥(barM M L))).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)⟩
  refine ⟨⟨hshort, e', by rw [hU]; exact h16⟩, ?_⟩
  obtain ⟨e⟩ := e'
  have hψs := barMHomSub_surjective hLM
  refine ⟨⟨e.toMonoidHom.comp (barMHomSub hLM), e.surjective.comp hψs, ?_⟩, ?_⟩
  · ext l
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, ← MonoidHom.mem_ker, ker_barMHomSub hLM,
      Subgroup.mem_subgroupOf]
    have h1 : (l : G) ∈ Q ↔ (l : G) ∈ pCoreOf 2 L := by
      rw [← hLs.inf_twoCore, Subgroup.mem_inf]
      exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
    rw [h1]
    exact ⟨fun h => mem_pCore_of_coe_mem h, fun h => coe_mem_pCoreOf h⟩
  ·
    have hZL : blockZ L = ⊥ := by
      have : blockZ L = ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
        rw [← hU]; rfl
      rw [this]; exact hirr.1
    have hsub : (blockZ L).subgroupOf (blockU L) = ⊥ := by rw [hZL, Subgroup.bot_subgroupOf]
    let eU : tildeU L ≃* ↥(blockU L) :=
      (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
    have hUV : blockU L ≤ V := by
      rw [hU]
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have h1 : l * v⁻¹ * l⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLV hl) v⁻¹).mp (V.inv_mem hv)
      have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
      rw [this]; exact V.mul_mem hv h1
    rw [pRank_congr_mulEquiv Nat.prime_two.one_lt eU]
    refine pRank_two_of_card_sixteen (fun a b => Subtype.ext
      (elemAbelian_comm' hVel a (hUV a.2) b (hUV b.2))) (fun a => Subtype.ext
      (hVel.2 a (hUV a.2))) (by rw [hU]; exact h16)

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  (EightTenOutcomes NaturalSectionLSL Asc81bEightTenPrinted)

@[expose] def EightTenNaturalOnly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
    Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
    ∀ m : ℕ, (m = 7 ∨ 8 < m) →
    Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
      alternatingGroup (Fin m)) → NaturalSectionLSL S L m → EightTenOutcomes X S L

theorem asc81bEightTenPrinted_of_natural_and_four
    (h85 : GF2EightFive) (h94 : GF2NoFFTripleA7) (hnat : EightTenNaturalOnly)
    (h4 : EightTenFourOutcome) : Asc81bEightTenPrinted := by
  intro G _ _ X S L hX hA hL hSL m hm he
  rcases gf2NaturalSection_of hX hA hL hSL hm he h85 h94 with h | ⟨h7, hS, hc⟩
  · exact hnat G X S L hX hA hL hSL m hm he h
  · subst h7
    exact Or.inr (Or.inl (h4 G X S L hX hA hL hSL he ⟨hS, hc⟩))

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
