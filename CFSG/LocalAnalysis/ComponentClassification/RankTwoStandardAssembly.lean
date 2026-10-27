module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardRouting
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeCatalog
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint

theorem quasisimple_quotient_catalog (G : Type) [Group G] (hK : Assembly.KProper Catalog G)
    (L : Subgroup G) (hLG : L < ⊤) (hL : Assembly.IsQuasisimple L) :
    Catalog (L ⧸ Subgroup.center L) := by
  have hNc : ((Subgroup.center L).map L.subtype).subgroupOf L = Subgroup.center L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have : (((Subgroup.center L).map L.subtype).subgroupOf L).Normal := by
    rw [hNc]
    infer_instance
  let e : (L ⧸ Subgroup.center L) ≃* (L ⧸ ((Subgroup.center L).map L.subtype).subgroupOf L) :=
    QuotientGroup.quotientMulEquivOfEq hNc.symm
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  obtain ⟨a, b, hab⟩ := StandardRecognition.exists_mul_ne_mul_of_isQuasisimple hL
  refine SectionRank.catalog_of_mulEquiv e (hK L _ hLG.ne (Subgroup.map_subtype_le _)
    e.symm.isSimpleGroup ⟨e a, e b, ?_⟩)
  rwa [← map_mul, ← map_mul, ne_eq, e.injective.eq_iff]

theorem isSporadic_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {s : TauCeti.SporadicName} (h : NativeSporadic.IsSporadic Y s) :
    NativeSporadic.IsSporadic X s :=
  Nonempty.map (e.trans ·) h

theorem ct_rank_two_standard_recognition_of_children (h1 : RankTwoAlternatingStandard)
    (h2 : RankTwoBenderStandard) (h3 : RankTwoOddLieStandard) (h4 : RankTwoL3EvenStandard)
    (h5 : RankTwoExceptionalEvenStandard) (h6 : RankTwoClassicalEvenStandard)
    (h7 : RankTwoSporadicStandard)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Catalog G) (L : Subgroup G) (hL : Open.standardComponentIsStandard L)
    (hrank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (L : Set G))) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (NativeSporadic.IsSporadic G .J2 ∨ NativeSporadic.IsSporadic G .Suz ∨
        NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Ru ∨
        NativeSporadic.IsSporadic G .Co1) := by
  have hZ := StandardRecognition.center_eq_bot_of_isSimpleGroup hnonab
  have heven : Even (Nat.card (Subgroup.centralizer (L : Set G))) := hL.2.1
  have hLtop : L ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.coe_top, Subgroup.centralizer_univ, hZ, Subgroup.card_bot] at heven
    exact Nat.not_even_one heven
  have hLbot : L ≠ ⊥ := by
    rintro rfl
    have hs : IsSimpleGroup (↥(⊥ : Subgroup G) ⧸ Subgroup.center ↥(⊥ : Subgroup G)) := hL.1.2
    exact not_nontrivial _ hs.toNontrivial
  have hnn : ¬ L.Normal := fun hN => by
    have := hN
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal L).elim hLbot hLtop
  have hodd : Open.standardComponentOddCore G = ⊥ := by
    refine sSup_eq_bot.2 fun N hN => ?_
    have := hN.1
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_right fun htop => ?_
    have hGodd : Odd (Nat.card G) := by
      rw [← Subgroup.card_top (G := G), ← htop]
      exact hN.2
    have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (L : Set G))
    exact Nat.not_even_iff_odd.2 hGodd ((even_iff_two_dvd.1 heven).trans hdvd |> even_iff_two_dvd.2)
  have hX : rankTwoX L = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (rankTwoX L)).resolve_left
      fun hbot => hLbot (le_bot_iff.1 ?_)
    rw [← hbot]
    exact Subgroup.le_normalClosure
  have hXG : rankTwoX L ≃* G := (MulEquiv.subgroupCongr hX).trans Subgroup.topEquiv
  have hH : RankTwoHyp G L := ⟨hK, hL, hnn, hrank⟩
  have hQ : Catalog (rankTwoQuot L) :=
    quasisimple_quotient_catalog G hK L (lt_top_iff_ne_top.2 hLtop) hL.1
  have hQnab : ∃ a b : rankTwoQuot L, a * b ≠ b * a :=
    StandardRecognition.exists_mul_ne_mul_of_isQuasisimple hL.1
  rcases rankTwo_route _ hQ hQnab with ⟨n, hn, hiso⟩ | hB | hO | ⟨m, hm, hL3⟩ | hE | hC | hS
  ·
    rcases h1 G L hH hodd n hn hiso with he | ⟨-, he⟩ | ⟨-, -, hne⟩
    · exact Or.inl ⟨n + 4, by omega, he.map (hXG.symm.trans ·)⟩
    · exact Or.inr (Or.inl (isSporadic_of_mulEquiv hXG.symm he))
    · exact absurd hX hne
  ·
    obtain ⟨-, he⟩ := h2 G L hH hodd hB
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isSporadic_of_mulEquiv hXG.symm he)))))
  ·
    exact absurd hO (h3 G L hH hodd)
  ·
    obtain ⟨-, -, hpart⟩ := h4 G L hH m hm hL3
    rcases hpart hodd with he | ⟨-, he⟩
    · exact Or.inr (Or.inr (Or.inl (isSporadic_of_mulEquiv hXG.symm he)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (isSporadic_of_mulEquiv hXG.symm he))))
  ·
    obtain ⟨-, he⟩ := h5 G L hH hodd hE
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (isSporadic_of_mulEquiv hXG.symm he)))))
  ·
    exact absurd hC (h6 G L hH hodd)
  ·
    exact absurd hS (h7 G L hH)

end CFSG.ComponentClassification.RankTwoStandard
