module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockTargets
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimUnitaryLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.LieModelSimple
public import CFSG.Models.Blueprint
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem pair_sp62_facts {q : TauCeti.PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 1)
    {dK dJ : TauCeti.ValidLieTypeIndex} (hdK : dK.1 = .B 3 q) (hdJ : dJ.1 = .twistedA 3 q) :
    center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK) := by
  obtain ⟨hcardJ, hsimpleJ⟩ :=
    LeviBlock.catGroup_u42_facts (d := dJ) ⟨q, hqp, hqe, hdJ⟩
  haveI : IsSimpleGroup (CatGroup dJ) := hsimpleJ
  have hcardK : Nat.card (CatGroup dK) = 1451520 := by
    rw [card_catGroup_B_even (d := dK) (r := 3) (q := q) (by norm_num) hqp hdK, hqe]
    decide
  have hnc : ¬ IsMulCommutative (CatGroup dJ) := by
    intro hcomm
    haveI : IsMulCommutative (CatGroup dJ) := hcomm
    have hp : (Nat.card (CatGroup dJ)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardJ] at hp
    exact absurd hp (by norm_num)
  refine ⟨TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  rw [hcardJ, hcardK]
  norm_num

theorem pair_g28_facts
    {q : TauCeti.PrimePower} (hqp : q.p = 2) (hqe : q.exponent = 3)
    {dK dJ : TauCeti.ValidLieTypeIndex} (hdK : dK.1 = .G2 q) (hdJ : dJ.1 = .twistedA 2 q) :
    center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK) := by
  have hcardJ : Nat.card (CatGroup dJ) = 5515776 :=
    LeviBlock.card_catGroup_u38 (d := dJ) ⟨q, hqp, hqe, hdJ⟩
  haveI : IsSimpleGroup (CatGroup dJ) := unitaryTarget_isSimpleGroup ⟨q, hqp, hdJ⟩
  have hcardK : Nat.card (CatGroup dK) = 4329310519296 := by
    rw [card_catGroup_G2_even (d := dK) (q := q) hqp hdK, hqe]
    norm_num [ordG2]
  have hnc : ¬ IsMulCommutative (CatGroup dJ) := by
    intro hcomm
    haveI : IsMulCommutative (CatGroup dJ) := hcomm
    have hp : (Nat.card (CatGroup dJ)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardJ] at hp
    exact absurd hp (by norm_num)
  refine ⟨TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  rw [hcardJ, hcardK]
  norm_num

theorem pair_tits_facts
    {q : TauCeti.PrimePower} (hqp : q.p = 3) (hqe : q.exponent = 1)
    {dK dJ : TauCeti.ValidLieTypeIndex} (hdK : dK.1 = .tits) (hdJ : dJ.1 = .A 2 q) :
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK) := by
  obtain ⟨x, hv⟩ := dJ
  obtain rfl : x = .A 2 q := hdJ
  have hmodel : CFSG.Blueprint.LieModel (CatGroup ⟨.A 2 q, hv⟩) .PSL 3 3 1 := by
    have hL := CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _)
    rw [hqp, hqe] at hL
    exact CFSG.Models.LieModel.toBlueprint (by decide) hL
  have hsimple : IsSimpleGroup (CatGroup ⟨.A 2 q, hv⟩) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  haveI := hsimple
  have hcardJ : Nat.card (CatGroup ⟨.A 2 q, hv⟩) = 5616 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hmodel]
    decide
  have hcardK : Nat.card (CatGroup dK) = 17971200 :=
    CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isTitsGroup
      (K := CatGroup dK) ⟨dK, hdK, ⟨MulEquiv.refl _⟩⟩
  have hnc : ¬ IsMulCommutative (CatGroup ⟨.A 2 q, hv⟩) := by
    intro hcomm
    haveI : IsMulCommutative (CatGroup ⟨.A 2 q, hv⟩) := hcomm
    have hp : (Nat.card (CatGroup ⟨.A 2 q, hv⟩)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardJ] at hp
    exact absurd hp (by norm_num)
  refine ⟨hsimple, ?_, TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  · rw [hcardJ]
    exact Or.inl rfl
  · rw [hcardJ, hcardK]
    norm_num

theorem pair_hs_facts
    {q : TauCeti.PrimePower} (hqp : q.p = 5) (hqe : q.exponent = 1)
    {dJ : TauCeti.ValidLieTypeIndex} (hdJ : dJ.1 = .twistedA 2 q) :
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧
      ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .HS).Group := by
  have hsimple : IsSimpleGroup (CatGroup dJ) := unitaryTarget_isSimpleGroup ⟨q, hqp, hdJ⟩
  haveI := hsimple
  have hcardJ : Nat.card (CatGroup dJ) = 126000 := by
    rw [card_catGroup_twistedA (r := 2) hdJ, hqp, hqe]
    unfold ordTwistedA
    decide
  have hcardHS : Nat.card (TauCeti.CFSGIndex.sporadic .HS).Group = 44352000 := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  have hnc : ¬ IsMulCommutative (CatGroup dJ) := by
    intro hcomm
    haveI : IsMulCommutative (CatGroup dJ) := hcomm
    have hp : (Nat.card (CatGroup dJ)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardJ] at hp
    exact absurd hp (by norm_num)
  refine ⟨hsimple, ?_, TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  · rw [hcardJ]
    exact Or.inr (Or.inl rfl)
  · rw [hcardJ, hcardHS]
    norm_num

theorem pair_onan_facts
    {q : TauCeti.PrimePower} (hqp : q.p = 7) (hqe : q.exponent = 1)
    {dJ : TauCeti.ValidLieTypeIndex} (hdJ : dJ.1 = .A 2 q) :
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧
      ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group := by
  obtain ⟨x, hv⟩ := dJ
  obtain rfl : x = .A 2 q := hdJ
  have hmodel : CFSG.Blueprint.LieModel (CatGroup ⟨.A 2 q, hv⟩) .PSL 3 7 1 := by
    have hL := CFSG.Models.lieModel_A 2 q hv (MulEquiv.refl _)
    rw [hqp, hqe] at hL
    exact CFSG.Models.LieModel.toBlueprint (by decide) hL
  have hsimple : IsSimpleGroup (CatGroup ⟨.A 2 q, hv⟩) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hmodel
  haveI := hsimple
  have hcardJ : Nat.card (CatGroup ⟨.A 2 q, hv⟩) = 1876896 := by
    rw [CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hmodel]
    decide
  have hcardON : Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group = 460815505920 := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.ON.card_ON
  have hnc : ¬ IsMulCommutative (CatGroup ⟨.A 2 q, hv⟩) := by
    intro hcomm
    haveI : IsMulCommutative (CatGroup ⟨.A 2 q, hv⟩) := hcomm
    have hp : (Nat.card (CatGroup ⟨.A 2 q, hv⟩)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardJ] at hp
    exact absurd hp (by norm_num)
  refine ⟨hsimple, ?_, TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  · rw [hcardJ]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [hcardJ, hcardON]
    norm_num

theorem pair_fi24_facts :
    IsSimpleGroup (TauCeti.CFSGIndex.sporadic .He).Group ∧
      IsL33U35L37HeOrder (Nat.card (TauCeti.CFSGIndex.sporadic .He).Group) ∧
      center (TauCeti.CFSGIndex.sporadic .He).Group = ⊥ ∧
      ¬ Nat.card (TauCeti.CFSGIndex.sporadic .He).Group ^ 2 ∣
        Nat.card (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := by
  have hcardHe : Nat.card (TauCeti.CFSGIndex.sporadic .He).Group = 4030387200 := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.He.card_He
  have hcardFi : Nat.card (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group =
      1255205709190661721292800 := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Fi24.card_Fi24prime
  have hsimpleHe : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .He).Group := by
    obtain ⟨e⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
    exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  haveI := hsimpleHe
  have hnc : ¬ IsMulCommutative (TauCeti.CFSGIndex.sporadic .He).Group := by
    intro hcomm
    haveI : IsMulCommutative (TauCeti.CFSGIndex.sporadic .He).Group := hcomm
    have hp : (Nat.card (TauCeti.CFSGIndex.sporadic .He).Group).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [hcardHe] at hp
    exact absurd hp (by norm_num)
  refine ⟨hsimpleHe, ?_, TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc, ?_⟩
  · rw [hcardHe]
    exact Or.inr (Or.inr (Or.inr rfl))
  · rw [hcardHe, hcardFi]
    norm_num

@[expose] def KFactThreeFourPairOrders : Prop :=
  (∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 1 →
    dK.1 = .B 3 q → dJ.1 = .twistedA 3 q →
    center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK)) ∧
  (∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 3 →
    dK.1 = .G2 q → dJ.1 = .twistedA 2 q →
    center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK)) ∧
  (∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 3 → q.exponent = 1 →
    dK.1 = .tits → dJ.1 = .A 2 q →
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧ ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (CatGroup dK)) ∧
  (∀ (q : TauCeti.PrimePower) (dJ : TauCeti.ValidLieTypeIndex), q.p = 5 → q.exponent = 1 →
    dJ.1 = .twistedA 2 q →
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧
      ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .HS).Group) ∧
  (∀ (q : TauCeti.PrimePower) (dJ : TauCeti.ValidLieTypeIndex), q.p = 7 → q.exponent = 1 →
    dJ.1 = .A 2 q →
    IsSimpleGroup (CatGroup dJ) ∧ IsL33U35L37HeOrder (Nat.card (CatGroup dJ)) ∧
      center (CatGroup dJ) = ⊥ ∧
      ¬ Nat.card (CatGroup dJ) ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .ONan).Group) ∧
  (IsSimpleGroup (TauCeti.CFSGIndex.sporadic .He).Group ∧
    IsL33U35L37HeOrder (Nat.card (TauCeti.CFSGIndex.sporadic .He).Group) ∧
    center (TauCeti.CFSGIndex.sporadic .He).Group = ⊥ ∧
    ¬ Nat.card (TauCeti.CFSGIndex.sporadic .He).Group ^ 2 ∣
      Nat.card (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)

theorem kFactThreeFourPairOrders_holds :
    KFactThreeFourPairOrders :=
  ⟨fun _ _ _ hqp hqe hdK hdJ => pair_sp62_facts hqp hqe hdK hdJ,
   fun _ _ _ hqp hqe hdK hdJ => pair_g28_facts hqp hqe hdK hdJ,
   fun _ _ _ hqp hqe hdK hdJ => pair_tits_facts hqp hqe hdK hdJ,
   fun _ _ hqp hqe hdJ => pair_hs_facts hqp hqe hdJ,
   fun _ _ hqp hqe hdJ => pair_onan_facts hqp hqe hdJ,
   pair_fi24_facts⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
