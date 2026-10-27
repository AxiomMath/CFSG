module

public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.Adapters.GlaubermanZJ
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonSubgroup_le_self (S : Subgroup G) : Open.thompsonSubgroup S ≤ S :=
  CFSG.ambientMaxCardThompson_le S

omit [Finite G] in
theorem normalizer_le_normalizer_thompsonSubgroup (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (Open.thompsonSubgroup S : Set G) :=
  CFSG.normalizer_le_normalizer_ambientMaxCardThompson S

theorem thompsonSubgroup_ne_bot {S : Subgroup G} (hS : S ≠ ⊥) : Open.thompsonSubgroup S ≠ ⊥ := by
  obtain ⟨A, hA⟩ := thompsonAbelianSubgroups_nonempty (G := G) S
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS
  have hcard := hA.2.2 (Subgroup.zpowers (x : G)) (Subgroup.zpowers_le.mpr x.2) inferInstance
  intro hbot
  have hAJ : A ≤ CFSG.thompsonSubgroup S := le_sSup hA
  rw [← Adapters.leanEval_thompsonSubgroup_eq, hbot, le_bot_iff] at hAJ
  rw [hAJ, Subgroup.card_bot, Nat.card_zpowers] at hcard
  exact hx1 (Subtype.ext (orderOf_eq_one_iff.mp (le_antisymm hcard (orderOf_pos _))))

omit [Finite G] in
theorem characteristic_map_center (S : Subgroup G) :
    (((Subgroup.center S).map S.subtype).subgroupOf S).Characteristic := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  infer_instance

theorem map_center_ne_bot {S : Subgroup G} (hS : IsPGroup 2 S) (hS1 : S ≠ ⊥) :
    (Subgroup.center S).map S.subtype ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot _).mpr hS1
  have hcnt : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective]
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hcnt

namespace TwoLocalPair

variable {M H : Subgroup G}

theorem thompsonJ_twoCore_ne (h : TwoLocalPair M H) :
    Quasithin.thompsonJ (pCoreOf 2 H) ≠ Quasithin.thompsonJ (pCoreOf 2 M) :=
  h.ne_of_char (Quasithin.B6.thompsonJ_le _)
    (QuasithinUnique.Setup.thompsonJ_ne_bot (pCoreOf_isPGroup 2 H) h.twoCore_H_ne_bot)
    (QuasithinUnique.Setup.characteristic_thompsonJ _) (Quasithin.B6.thompsonJ_le _)
    (QuasithinUnique.Setup.characteristic_thompsonJ _)

theorem thompsonSubgroup_twoCore_ne (h : TwoLocalPair M H) :
    Open.thompsonSubgroup (pCoreOf 2 H) ≠ Open.thompsonSubgroup (pCoreOf 2 M) :=
  h.ne_of_le_normalizer (thompsonSubgroup_ne_bot h.twoCore_H_ne_bot)
    ((pCoreOf_isPGroup 2 H).to_le (thompsonSubgroup_le_self _))
    ((localGroup_le_normalizer_pCoreOf 2 H).trans (normalizer_le_normalizer_thompsonSubgroup _))
    ((localGroup_le_normalizer_pCoreOf 2 M).trans (normalizer_le_normalizer_thompsonSubgroup _))

theorem center_twoCore_ne (h : TwoLocalPair M H) :
    (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype ≠
      (Subgroup.center (pCoreOf 2 M)).map (pCoreOf 2 M).subtype :=
  h.ne_of_char (Subgroup.map_subtype_le _)
    (map_center_ne_bot (pCoreOf_isPGroup 2 H) h.twoCore_H_ne_bot) (characteristic_map_center _)
    (Subgroup.map_subtype_le _) (characteristic_map_center _)

theorem omegaOneCenter_twoCore_ne (h : TwoLocalPair M H) :
    Quasithin.omegaOneCenterOf (pCoreOf 2 H) ≠ Quasithin.omegaOneCenterOf (pCoreOf 2 M) :=
  h.ne_of_char (QuasithinUnique.Setup.omegaOneCenterOf_le _)
    (QuasithinUnique.Setup.omegaOneCenterOf_ne_bot (pCoreOf_isPGroup 2 H) h.twoCore_H_ne_bot)
    (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
    (QuasithinUnique.Setup.omegaOneCenterOf_le _)
    (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)

theorem not_thompsonJ_le_twoCore_M (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ Quasithin.thompsonJ (pCoreOf 2 H) ≤ pCoreOf 2 M := fun hle =>
  h.thompsonJ_twoCore_ne (Quasithin.B6.thompsonJ_eq_of_le hle (h.twoCore_M_le hS)).symm

theorem exists_isMaxElemAbelian_not_le (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ∃ A : Subgroup G, Quasithin.IsMaxElemAbelian (pCoreOf 2 H) A ∧ ¬ A ≤ pCoreOf 2 M := by
  by_contra hcon
  refine h.not_thompsonJ_le_twoCore_M hS (iSup₂_le fun A hA => ?_)
  by_contra hAQ
  exact hcon ⟨A, hA, hAQ⟩

theorem not_thompsonSubgroup_le_twoCore_M (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ Open.thompsonSubgroup (pCoreOf 2 H) ≤ pCoreOf 2 M := by
  intro hle
  apply h.thompsonSubgroup_twoCore_ne
  rw [Adapters.leanEval_thompsonSubgroup_eq] at hle
  rw [Adapters.leanEval_thompsonSubgroup_eq, Adapters.leanEval_thompsonSubgroup_eq]
  exact (CFSG.thompsonSubgroup_eq_of_le (h.twoCore_M_le hS) hle).symm

end TwoLocalPair

namespace D1Escape

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem not_le_normalizer_of_le_normalizer (h : D1Escape p P M H R) {C : Subgroup G}
    (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    ¬ M ≤ Subgroup.normalizer (C : Set G) :=
  h.toTwoLocalPair.not_le_normalizer_of_le_normalizer hC1 hC2 hHC

theorem not_le_normalizer_of_char (h : D1Escape p P M H R) {C : Subgroup G}
    (hCS : C ≤ pCoreOf 2 H) (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic) :
    ¬ M ≤ Subgroup.normalizer (C : Set G) :=
  h.toTwoLocalPair.not_le_normalizer_of_char hCS hC1 hchar

theorem ne_of_le_normalizer (h : D1Escape p P M H R) {C D : Subgroup G} (hC1 : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G))
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) : C ≠ D :=
  h.toTwoLocalPair.ne_of_le_normalizer hC1 hC2 hHC hMD

theorem ne_of_char (h : D1Escape p P M H R) {C D : Subgroup G} (hCS : C ≤ pCoreOf 2 H)
    (hC1 : C ≠ ⊥) (hCchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic)
    (hDQ : D ≤ pCoreOf 2 M) (hDchar : (D.subgroupOf (pCoreOf 2 M)).Characteristic) : C ≠ D :=
  h.toTwoLocalPair.ne_of_char hCS hC1 hCchar hDQ hDchar

theorem twoCore_H_ne_bot (h : D1Escape p P M H R) : pCoreOf 2 H ≠ ⊥ :=
  h.toTwoLocalPair.twoCore_H_ne_bot

theorem thompsonJ_twoCore_ne (h : D1Escape p P M H R) :
    Quasithin.thompsonJ (pCoreOf 2 H) ≠ Quasithin.thompsonJ (pCoreOf 2 M) :=
  h.toTwoLocalPair.thompsonJ_twoCore_ne

theorem thompsonSubgroup_twoCore_ne (h : D1Escape p P M H R) :
    Open.thompsonSubgroup (pCoreOf 2 H) ≠ Open.thompsonSubgroup (pCoreOf 2 M) :=
  h.toTwoLocalPair.thompsonSubgroup_twoCore_ne

theorem center_twoCore_ne (h : D1Escape p P M H R) :
    (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype ≠
      (Subgroup.center (pCoreOf 2 M)).map (pCoreOf 2 M).subtype :=
  h.toTwoLocalPair.center_twoCore_ne

theorem omegaOneCenter_twoCore_ne (h : D1Escape p P M H R) :
    Quasithin.omegaOneCenterOf (pCoreOf 2 H) ≠ Quasithin.omegaOneCenterOf (pCoreOf 2 M) :=
  h.toTwoLocalPair.omegaOneCenter_twoCore_ne

theorem not_thompsonJ_le_twoCore_M (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ Quasithin.thompsonJ (pCoreOf 2 H) ≤ pCoreOf 2 M :=
  h.toTwoLocalPair.not_thompsonJ_le_twoCore_M hS

theorem exists_isMaxElemAbelian_not_le (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ∃ A : Subgroup G, Quasithin.IsMaxElemAbelian (pCoreOf 2 H) A ∧ ¬ A ≤ pCoreOf 2 M :=
  h.toTwoLocalPair.exists_isMaxElemAbelian_not_le hS

theorem not_thompsonSubgroup_le_twoCore_M (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ Open.thompsonSubgroup (pCoreOf 2 H) ≤ pCoreOf 2 M :=
  h.toTwoLocalPair.not_thompsonSubgroup_le_twoCore_M hS

theorem center_twoCore_lt_center_twoCore_M (h : D1Escape p P M H R) (hchar : IsCharTwoType G)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (Subgroup.center (pCoreOf 2 H)).map (pCoreOf 2 H).subtype <
      (Subgroup.center (pCoreOf 2 M)).map (pCoreOf 2 M).subtype :=
  lt_of_le_of_ne (h.center_twoCore_le_center_twoCore_M hchar hS) h.center_twoCore_ne

end D1Escape

theorem le_two_of_elemAbelian_le_normalizer {Q E : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQ4 : ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = Q)
    (hEN : E ≤ Subgroup.normalizer (Q : Set G)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsElemAbelian p E) (hcore : ∀ x ∈ E, (∀ q ∈ Q, q * x = x * q) → x ∈ Q) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ 2 := by
  obtain ⟨s, hs4, hs⟩ := hQ4
  have hrank : Group.rank Q ≤ 4 := by
    rw [← hs]
    exact (Subgroup.rank_closure_finset_le_card s).trans hs4
  obtain ⟨ψ, hψ⟩ := RankThree.PartOne.SectionalRank.exists_injective_hom_mulAut_frattini_quotient
    hQ hEN hp hp2 hE.2 hcore
  have hdvd := Subgroup.card_dvd_of_injective ψ hψ
  rw [hk] at hdvd
  exact RankThree.PartOne.SectionalRank.le_two_of_prime_pow_dvd_20160 hp hp2
    (hdvd.trans (RankThree.PartOne.SectionalRank.card_mulAut_frattini_quotient_dvd hQ hrank))

theorem pRank_le_two_of_sectional_four (hchar : IsCharTwoType G)
    (hsec : ∀ T : Subgroup G, IsPGroup 2 T →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = T)
    {L : Subgroup G} (hL : IsTwoLocal L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Open.pRank p L ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨E, hEL, hE, hk⟩
  have hQ := pCoreOf_isPGroup 2 L
  exact le_two_of_elemAbelian_le_normalizer hQ (hsec _ hQ)
    (hEL.trans (localGroup_le_normalizer_pCoreOf 2 L)) hp hp2 hE
    (fun x hx hc => hchar L hL ⟨hEL hx, Subgroup.mem_centralizer_iff.mpr hc⟩) hk

theorem evenRank_le_two_of_sectional_four (hchar : IsCharTwoType G)
    (hsec : ∀ T : Subgroup G, IsPGroup 2 T →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = T) :
    Open.evenRank G ≤ 2 := by
  refine csSup_le' ?_
  rintro k ⟨p, L, hp, hp2, hL, rfl⟩
  exact pRank_le_two_of_sectional_four hchar hsec hL hp hp2

theorem D1Escape.not_sectional_four {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1Escape p P M H R) (hchar : IsCharTwoType G) :
    ¬ ∀ T : Subgroup G, IsPGroup 2 T →
      ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = T := fun hsec => by
  have h2 := pRank_le_two_of_sectional_four hchar hsec h.maxTwoLocal_H.1 h.prime h.ne_two
  have h3 := h.three_le_pRank.trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p h.prime h.le_H)
  omega

end CFSG.AGLEmbedding
