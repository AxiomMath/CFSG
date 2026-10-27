module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Rows
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.HardMathSupport.Timmesfeld.LieRank.G2Spec
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.Sporadic.Bridge.J2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4

namespace Conv76

theorem exists_tauCeti_u33 {S : Type} [Group S]
    (e : S ≃* CFSG.Assembly.RankThreeEven.projSU 3 3 1) :
    ∃ q : TauCeti.PrimePower, ∃ hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid, q.card = 3 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have : Fact q.p.Prime := ⟨Nat.prime_three⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨le_rfl, fun _ => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 3 ^ 1
    norm_num
  refine ⟨q, hv, by rw [TauCeti.PrimePower.card_def]; rfl, ⟨?_⟩⟩
  exact e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv).symm

end Conv76

section Conv


namespace Conv76

theorem exists_tauCeti_g2_of_model {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 p f) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = p ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  let q : TauCeti.PrimePower := ⟨p, f, hadm.1, hadm.2.1⟩
  have hq : q.card = p ^ f := TauCeti.PrimePower.card_def q
  have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
    refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · simpa [TauCeti.LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
    · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeAll_of
    CFSG.TauCetiBridge.untwistedBridge_G2 CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv K
    (by rw [hK, hq])
  exact ⟨q, hv, rfl, ⟨e.trans b⟩⟩

open CFSG.Blueprint.Chevalley in
theorem four_le_pRank_of_g2_three {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 3 f) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨hadm, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
  have : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hadm.2.1 hK
  let : Algebra (ZMod 3) K := ZMod.algebra K 3
  have : Finite (ModGL .G2 K) := by
    have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
    infer_instance
  obtain ⟨ι, hι⟩ : ∃ ι : adjointGroup .G2 (ZMod 3) →* adjointGroup .G2 K,
      Function.Injective ι := by
    refine ⟨(CFSG.RankThree.PartOne.KE.adjEmb .G2 (ZMod 3) K).codRestrict _
      fun y => CFSG.RankThree.PartOne.KE.adjEmb_mem y, ?_⟩
    intro a b hab
    apply CFSG.RankThree.PartOne.KE.adjEmb_injective (τ := .G2) (K := ZMod 3) (L := K)
    exact congrArg Subtype.val hab
  obtain ⟨e₃⟩ :
      Nonempty (adjointGroup .G2 (ZMod 3) ≃* CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
    ⟨Subgroup.equivMapOfInjective _ (CFSG.Quasithin.G2U.glHom (RingEquiv.refl (ZMod 3)))
      (CFSG.Quasithin.G2U.glHom_injective _)⟩
  have h3 : 1 < 3 := by norm_num
  have hn : CFSG.HardMathSupport.Timmesfeld.LieRank.specA.n = 4 := rfl
  have a1 : CFSG.HardMathSupport.Timmesfeld.LieRank.specA.n ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
    CFSG.AGLEmbedding.ModuleSpec.n_le_pRank Nat.prime_three
      CFSG.HardMathSupport.Timmesfeld.LieRank.specA
  have a2 : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .G2 (ZMod 3))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3 e₃
  have a3 : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .G2 (ZMod 3))) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .G2 K)) :=
    CFSG.SectionRank.pRank_top_le_of_injective h3 ι hι
  have a4 : CFSG.Open.pRank 3 (⊤ : Subgroup (adjointGroup .G2 K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.AdjointQuotient .G2 K)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
        QuotientGroup.quotientBot).symm
  have a5 : CFSG.Open.pRank 3 (⊤ : Subgroup X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Blueprint.AdjointQuotient .G2 K)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv h3 e
  omega

theorem listRow76_of_listRow {S : Type} [Group S] [Finite S] (hcov : RankThreeCover S)
    (h : RonanK432.ListRow S) : ListRow76 S := by
  intro z hz hwc
  rcases h z hz hwc with h1 | ⟨hG, hR, hN⟩ | ⟨⟨e⟩, hR, hN⟩
  · exact Or.inl h1
  · refine Or.inr ⟨?_, hR, hN⟩
    rcases hG with ⟨p, f, hm⟩ | ⟨⟨e⟩⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exfalso
        obtain ⟨L, _, _, hq, hZ3, ⟨eL⟩, hr3⟩ := hcov
        have hZ : Subgroup.center L = ⊥ := hN L hq hZ3 ⟨eL⟩
        have h4 := four_le_pRank_of_g2_three
          (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
            (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
              eL) hm)
        omega
      · obtain ⟨q, hv, hqp, he⟩ := exists_tauCeti_g2_of_model hm
        exact Or.inl ⟨q, hv, by rw [hqp]; exact hp3, he⟩
    · exact Or.inr (Or.inl (exists_tauCeti_u33 e))
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    exact Or.inr ⟨Or.inr (Or.inr ⟨e.trans b⟩), hR, hN⟩

end Conv76

theorem row76_of_goodRow {S : Type} [Group S] [Finite S] (hcov : RankThreeCover S)
    (h : RonanK432.GoodRow S) : Row76 S :=
  ⟨Conv76.listRow76_of_listRow hcov h.1, fun h3 σ hσ hout _ => h.2 h3 σ hσ hout⟩

end Conv

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
