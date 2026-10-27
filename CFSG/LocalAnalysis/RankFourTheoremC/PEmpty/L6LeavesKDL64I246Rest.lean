module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64TypeRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Main
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.Blueprint Subgroup
open scoped MatrixGroups

@[expose] def KDL64I246Rest : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z], CatalogSimpleSections Z →
    primeComplementCore (G := Z) p = ⊥ →
    ∀ L : Subgroup Z, IsComponentOf L ⊤ →
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), p ∣ Nat.card K - 1 ∧
          Nonempty ((↥L ⧸ center ↥L) ≃* StatedProj (StatedSL p K))) ∨
        (∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ p ∣ q + 1 ∧
          Nonempty ((↥L ⧸ center ↥L) ≃* StatedProj (StatedSU p q K))) ∨
        (p = 5 ∧ NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .Co1)) →
      ∀ P : Subgroup Z, P ≤ L → IsPGroup p P → ¬ p ∣ (P.subgroupOf L).index →
        3 ≤ Open.pRank p P →
        ∀ Y : Subgroup Z,
          (∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) →
          (∀ E : Subgroup Z, E ≤ P → IsElemAbelian p E → Nat.card E = p ^ 3 →
            ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) →
          L ≤ Y

theorem kdL64I246_genericOrders_G2 (p : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .G2 0 p 1 = (1, 1) := rfl

theorem kdL64I246_exceptionalOrders_G2 (p : ℕ) (hp : 5 ≤ p) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .G2 0 p 1 = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | rfl | (exfalso; omega) | simp_all

theorem kdL64I246_card_center_dvd_two {G X : Type} [Group G] [Finite G] [Group X]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hq : CFSG.Open.IsQuasisimple G)
    (e : G ⧸ Subgroup.center G ≃* X) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel X t n p f)
    (h2 : (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) ∣ 2) :
    Nat.card (Subgroup.center G) ∣ 2 := by
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hq.1
  have h1 := CFSG.ComponentClassification.CatFactsSp4.card_center_dvd_hopfMultiplier e
  rw [(CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.finite_and_card_hopf hGA hm).2] at h1
  exact h1.trans h2

theorem kdL64I246_center_eq_bot {Z : Type} [Group Z] [Finite Z] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hO : primeComplementCore (G := Z) p = ⊥) {L : Subgroup Z}
    (hL : IsComponentOf L ⊤) (h2 : Nat.card (Subgroup.center ↥L) ∣ 2) :
    Subgroup.center ↥L = ⊥ := by
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h' := Nat.le_of_dvd (by norm_num) (h.trans h2)
    omega
  have hcore : Subgroup.center ↥L ≤ primeComplementCore (G := ↥L) p :=
    normal_coprime_le_primeComplementCore p _ inferInstance hcop
  have hsub := cfsg_subnormal_primeComplementCoreOf_le p hL.2.1
  rw [primeComplementCoreOf_top_eq_primeComplementCore, hO] at hsub
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : Z) ∈ primeComplementCoreOf p L :=
    Subgroup.mem_map_of_mem L.subtype (hcore hx)
  have h1 : (x : Z) ∈ (⊥ : Subgroup Z) := hsub hx'
  rw [Subgroup.mem_bot] at h1 ⊢
  exact Subtype.ext h1

theorem kdL64I246_valid_B2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (TauCeti.LieTypeIndex.B 2 (⟨p, 1, hp, Nat.one_pos⟩ : TauCeti.PrimePower)).Valid := by
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def, pow_one]
  omega

theorem kdL64I246_valid_G2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (TauCeti.LieTypeIndex.G2 (⟨p, 1, hp, Nat.one_pos⟩ : TauCeti.PrimePower)).Valid := by
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def, pow_one,
    not_false_eq_true, and_true]
  omega

theorem kdL64I246_not_rankOne_B2 (q : TauCeti.PrimePower) :
    ¬ CFSG.AGLEmbedding.IsRankOneLieIndex (TauCeti.LieTypeIndex.B 2 q) := by
  rintro (⟨q', h⟩ | ⟨q', h⟩ | ⟨m, h⟩) <;> cases h

theorem kdL64I246_not_rankOne_G2 (q : TauCeti.PrimePower) :
    ¬ CFSG.AGLEmbedding.IsRankOneLieIndex (TauCeti.LieTypeIndex.G2 q) := by
  rintro (⟨q', h⟩ | ⟨q', h⟩ | ⟨m, h⟩) <;> cases h

theorem kdL64I246_nonempty_typeB2 {X : Type} [Group X] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card) (θ : X ≃* StatedProj (StatedSp 2 K)) :
    Nonempty (X ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩) := by
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
  have hF : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩) =
      q.card := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩]
    exact TauCeti.LieTypeIndex.fieldOrder_B 2 q
  let φ : K ≃+* ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩) :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hK.trans hF.symm)
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 2 ⊕ Fin 2) φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨(θ.trans e1).trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv).symm⟩

theorem kdL64I246_le_of_catGroup
    {Z : Type} [Group Z] [Finite Z] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup Z} (hs : IsSimpleGroup ↥L) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥L ≃* CFSG.AGLEmbedding.CatGroup d) (hchar : p = d.1.characteristic)
    (hrank : ¬ CFSG.AGLEmbedding.IsRankOneLieIndex d.1)
    {P : Subgroup Z} (hPL : P ≤ L) (hP : IsPGroup p P) (hidx : ¬ p ∣ (P.subgroupOf L).index)
    {Y : Subgroup Z}
    (hY : ∀ S : Subgroup Z, S ≤ P → 2 ≤ CFSG.Open.pRank p S → normalizer (S : Set Z) ≤ Y) :
    L ≤ Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPsub : IsPGroup p ↥(P.subgroupOf L) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  let Q : Sylow p ↥L := IsPGroup.toSylow hPsub hidx
  have htop : CFSG.Open.GLBCore p 2 (Q : Subgroup ↥L) = ⊤ :=
    Fact2314.charPGen2 ↥L hs d ⟨e⟩ p hp hp2 hchar hrank Q
  have hQ : (Q : Subgroup ↥L).map L.subtype = P := by
    show (P.subgroupOf L).map L.subtype = P
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
  exact Bridge2314.le_of_glbCore_two_eq_top hp hQ
    (fun S₀ hS hr => inf_le_left.trans (hY S₀ hS hr)) htop

theorem kdL64I246_of_rest
    (h : KDL64I246Rest) : KDL64I246 := by
  intro p hp hp5 Z _ _ hCS hO L hL hI P hPL hP hidx hrank Y hY1 hY2
  have hp2 : p ≠ 2 := by omega
  unfold P64IsI246Type at hI
  rcases hI with h1 | h2 | h3 | h4 | h5
  · exact h p hp hp5 Z hCS hO L hL (Or.inl h1) P hPL hP hidx hrank Y hY1 hY2
  · exact h p hp hp5 Z hCS hO L hL (Or.inr (Or.inl h2)) P hPL hP hidx hrank Y hY1 hY2
  · exact h p hp hp5 Z hCS hO L hL (Or.inr (Or.inr h3)) P hPL hP hidx hrank Y hY1 hY2
  ·
    have hmod : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 p 1 :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_of_classical h4
    have hdvd : Nat.card (Subgroup.center ↥L) ∣ 2 :=
      kdL64I246_card_center_dvd_two
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hL.2.2
        (MulEquiv.refl _) hmod (by
          rw [genericOrders_PSp_fst, genericOrders_PSp_snd, exceptionalOrders_PSp_two]
          simp only [mul_one, pow_one]
          exact Nat.gcd_dvd_left 2 (p - 1))
    have hcen := kdL64I246_center_eq_bot hp hp5 hO hL hdvd
    have hq0 : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have hs : IsSimpleGroup ↥L := hq0.isSimpleGroup_congr.mp hL.2.2.2
    obtain ⟨-, K, hKf, hKfin, hK, ⟨θ⟩⟩ := h4
    let q : TauCeti.PrimePower := ⟨p, 1, hp, Nat.one_pos⟩
    have hKq : Nat.card K = q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact hK
    have hv : (TauCeti.LieTypeIndex.B 2 q).Valid := kdL64I246_valid_B2 hp hp5
    have hch : (TauCeti.LieTypeIndex.B 2 q).characteristic = p :=
      TauCeti.LieTypeIndex.characteristic_B 2 q
    obtain ⟨ψ⟩ := kdL64I246_nonempty_typeB2 q hv hKq θ
    exact kdL64I246_le_of_catGroup hp hp2 hs ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩
      (hq0.symm.trans ψ) hch.symm (kdL64I246_not_rankOne_B2 q) hPL hP hidx hY1
  ·
    obtain ⟨hadm, K, hKf, hKfin, hK, ⟨θ⟩⟩ := h5
    let q : TauCeti.PrimePower := ⟨p, 1, hp, Nat.one_pos⟩
    have hKq : Nat.card K = q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact hK
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := kdL64I246_valid_G2 hp hp5
    have hch : (TauCeti.LieTypeIndex.G2 q).characteristic = p :=
      TauCeti.LieTypeIndex.characteristic_G2 q
    obtain ⟨ψ⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 q hv hp2 K hKq
    have hmod : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 p 1 :=
      ⟨hadm, Or.inr ⟨rfl, ⟨TauCeti.LieTypeIndex.G2 q, hv⟩, ⟨rfl, rfl⟩, ⟨θ.trans ψ⟩⟩⟩
    have hdvd : Nat.card (Subgroup.center ↥L) ∣ 2 :=
      kdL64I246_card_center_dvd_two
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hL.2.2
        (MulEquiv.refl _) hmod (by
          rw [kdL64I246_genericOrders_G2, kdL64I246_exceptionalOrders_G2 p hp5]
          simp)
    have hcen := kdL64I246_center_eq_bot hp hp5 hO hL hdvd
    have hq0 : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    have hs : IsSimpleGroup ↥L := hq0.isSimpleGroup_congr.mp hL.2.2.2
    exact kdL64I246_le_of_catGroup hp hp2 hs ⟨TauCeti.LieTypeIndex.G2 q, hv⟩
      (hq0.symm.trans (θ.trans ψ)) hch.symm (kdL64I246_not_rankOne_G2 q) hPL hP hidx hY1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
