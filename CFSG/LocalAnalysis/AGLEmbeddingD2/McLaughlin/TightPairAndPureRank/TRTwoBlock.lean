module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicEngine

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def GNBound (T : Subgroup X) : Prop :=
  ∀ T' : Subgroup X, T' ≠ ⊥ → T' ≤ T → (T'.subgroupOf T).Characteristic →
    Open.pRank 3 (Subgroup.normalizer (T' : Set X)) ≤ 2 ∧
    (2 ≤ Open.pRank 3 (Subgroup.normalizer (T' : Set X)) →
      ∀ J : Subgroup X, J ≤ Subgroup.normalizer (T' : Set X) → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J)

section Engine

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem perfect_of_isComponentOf {L : Subgroup Q} (hL : IsComponentOf L ⊤) : ⁅L, L⁆ = L := by
  have h : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  exact Subgroup.isPerfect_iff.mp h

omit [Finite Q] in
theorem exists_three_dvd_of_not_pElement_le {A Z : Subgroup Q} (h : ¬ pElementSubgroup 3 A ≤ Z) :
    ∃ D : Subgroup Q, D ≤ A ∧ 3 ∣ Nat.card D := by
  by_contra hcon
  push Not at hcon
  apply h
  refine (Subgroup.closure_le Z).mpr ?_
  rintro x ⟨hxA, k, hk⟩
  by_cases hk0 : k = 0
  · subst hk0
    simp only [pow_zero, orderOf_eq_one_iff] at hk
    rw [hk]
    exact Z.one_mem
  · exfalso
    apply hcon (Subgroup.zpowers x) ((Subgroup.zpowers_le).mpr hxA)
    rw [Nat.card_zpowers, hk]
    exact dvd_pow_self 3 hk0

theorem rank_ge_two_of_partner {N A D : Subgroup Q} (hAN : A ≤ N) (hDN : D ≤ N)
    (hA : 3 ∣ Nat.card A) (hD : 3 ∣ Nat.card D)
    (hc : ∀ a ∈ A, ∀ b ∈ D, a * b = b * a) (hi : Nat.Coprime 3 (Nat.card (A ⊓ D : Subgroup Q))) :
    2 ≤ Open.pRank 3 N := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h1 := pRank_add_le_pRank_sup_of_coprime h3 hc hi
  have h2 : Open.pRank 3 (A ⊔ D) ≤ Open.pRank 3 N :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 (sup_le hAN hDN)
  have h4 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3 hA
  have h5 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3 hD
  omega

@[expose] def NBound (N : Subgroup Q) : Prop :=
  Open.pRank 3 N ≤ 2 ∧
    (2 ≤ Open.pRank 3 N → ∀ J : Subgroup Q, J ≤ N → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J)

theorem false_of_partner {N A D : Subgroup Q} (hN : NBound N) (hAN : A ≤ N) (hDN : D ≤ N)
    (hAp : ⁅A, A⁆ = A) (hA : 3 ∣ Nat.card A) (hD : 3 ∣ Nat.card D)
    (hc : ∀ a ∈ A, ∀ b ∈ D, a * b = b * a) (hi : Nat.Coprime 3 (Nat.card (A ⊓ D : Subgroup Q))) :
    False :=
  hN.2 (rank_ge_two_of_partner hAN hDN hA hD hc hi) A hAN hAp hA

theorem pRank_le_one_of_perfect {N A : Subgroup Q} (hN : NBound N) (hAN : A ≤ N)
    (hAp : ⁅A, A⁆ = A) (hA : 3 ∣ Nat.card A) : Open.pRank 3 N ≤ 1 := by
  by_contra h
  push Not at h
  exact hN.2 (by omega) A hAN hAp hA

theorem coverHyp_of_partner {N A D : Subgroup Q} (hN : NBound N) (hAN : A ≤ N) (hDN : D ≤ N)
    (hA : 3 ∣ Nat.card A) (hD : 3 ∣ Nat.card D)
    (hc : ∀ a ∈ A, ∀ b ∈ D, a * b = b * a) (hi : Nat.Coprime 3 (Nat.card (A ⊓ D : Subgroup Q))) :
    3 ∣ Nat.card A ∧ Open.pRank 3 A ≤ 1 ∧ CFSG.HallHigman.IsPSolvable 3 ↥A := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h1 := pRank_add_le_pRank_sup_of_coprime h3 hc hi
  have h2 : Open.pRank 3 (A ⊔ D) ≤ Open.pRank 3 N :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 h3 (sup_le hAN hDN)
  have h4 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3 hD
  have h5 := hN.1
  have h6 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd h3 hA
  refine ⟨hA, by omega, isPSolvable_three_of_no_perfect A fun J hJ hJp => ?_⟩
  exact hN.2 (rank_ge_two_of_partner hAN hDN hA hD hc hi) J (hJ.trans hAN) hJp

end Engine

section Main

@[expose] def gnN (T T' : Subgroup X) : Subgroup (X ⧸ gnC T) :=
  gnImg T (Subgroup.normalizer (T' : Set X))

theorem nBound_gnN (T : Subgroup X) (hC : ¬ 3 ∣ Nat.card (gnC T)) (hD : GNBound T)
    {T' : Subgroup X} (h1 : T' ≠ ⊥) (h2 : T' ≤ T) (h3 : (T'.subgroupOf T).Characteristic) :
    NBound (gnN T T') := by
  obtain ⟨hr, hp⟩ := hD T' h1 h2 h3
  have hle : Open.pRank 3 (gnN T T') ≤ Open.pRank 3 (Subgroup.normalizer (T' : Set X)) :=
    pRank_gnImg_le T hC _
  refine ⟨hle.trans hr, fun h2' => ?_⟩
  have h2le : 2 ≤ Open.pRank 3 (Subgroup.normalizer (T' : Set X)) := h2'.trans hle
  exact no_perfect_gnImg T _ (hp h2le)

theorem comm_inf_of_ne {T : Subgroup X} {L₁ L₂ : Subgroup (X ⧸ gnC T)} (hL₁ : IsComponentOf L₁ ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L₁)) {D₁ D₂ : Subgroup (X ⧸ gnC T)}
    (h₁ : D₁ ≤ L₁) (h₂ : D₂ ≤ L₂) :
    (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ Nat.Coprime 3 (Nat.card (D₁ ⊓ D₂ : Subgroup _)) := by
  have hcomp : ⁅L₁, L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL₁ hL₂ hne
  have hL₂C : L₂ ≤ Subgroup.centralizer (L₁ : Set (X ⧸ gnC T)) := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mp ?_
    rw [Subgroup.commutator_comm]
    exact hcomp
  refine ⟨fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hL₂C (h₂ hb)) a (h₁ ha), ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  apply hZ₁
  rw [← card_inf_centralizer_eq_card_center]
  exact hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨h₁ hu.1, hL₂C (h₂ hu.2)⟩)

theorem isDoublingList_of_gn_two (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverDoubling)
    {T : Subgroup X} (hX : GNSetting X T) (hC : ¬ 3 ∣ Nat.card (gnC T)) (hD : GNBound T)
    {L₁ L₂ : Subgroup (X ⧸ gnC T)} (hL₁ : IsComponentOf L₁ ⊤) (hL₂ : IsComponentOf L₂ ⊤)
    (hne : L₁ ≠ L₂)
    (hcl₁ : IsClassicalTwoOrG2 (↥L₁ ⧸ Subgroup.center ↥L₁))
    (hcl₂ : IsClassicalTwoOrG2 (↥L₂ ⧸ Subgroup.center ↥L₂))
    (hS₁ : IsSylowTwoOf (gnImg T T ⊓ L₁) L₁) (hS₂ : IsSylowTwoOf (gnImg T T ⊓ L₂) L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L₁)) (hZ₂ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L₂))
    (h3₁ : 3 ∣ Nat.card L₁) (h3₂ : 3 ∣ Nat.card L₂)
    (hrank : 2 < Open.pRank 3 L₁ + Open.pRank 3 L₂) :
    IsDoublingList (↥L₁ ⧸ Subgroup.center ↥L₁) ∧ IsDoublingList (↥L₂ ⧸ Subgroup.center ↥L₂) := by
  obtain ⟨T₁, T₂, hpair, hpar, hthree, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL₁)
  have hT₁ : T₁ ≤ T := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hN₁ : NBound (gnN T T₁) := nBound_gnN T hC hD hpair.ne_bot₁ hT₁ hpair.char₁
  have hN₂ : NBound (gnN T T₂) := nBound_gnN T hC hD hpair.ne_bot₂ hpair.le₂ hpair.char₂
  have hp₁ := perfect_of_isComponentOf hL₁
  have hp₂ := perfect_of_isComponentOf hL₂
  have hnotY : ∀ {L : Subgroup (X ⧸ gnC T)}, IsComponentOf L ⊤ →
      ¬ GNYComponent T T₁ T₂ L → L ≤ gnN T T₁ ∨ L ≤ gnN T T₂ := by
    intro L hL hY
    by_contra hcon
    push Not at hcon
    apply hY
    refine ⟨hL, fun hle => hcon.1 (hle.trans (Subgroup.map_mono
      (Subgroup.centralizer_le_normalizer _))), fun hle => hcon.2 hle⟩
  have hpart : ∀ {L : Subgroup (X ⧸ gnC T)}, GNYComponent T T₁ T₂ L →
      IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
      (∃ D : Subgroup (X ⧸ gnC T), D ≤ gnA T T₁ L ∧ 3 ∣ Nat.card D) ∧
      (∃ D : Subgroup (X ⧸ gnC T), D ≤ gnA T T₂ L ∧ 3 ∣ Nat.card D) := by
    intro L hL hcl
    obtain ⟨h1, h2⟩ := hthree L hL
    exact ⟨exists_three_dvd_of_not_pElement_le h1,
      exists_three_dvd_of_not_pElement_le (h2 (Or.inl hcl))⟩
  have hAle : ∀ (L : Subgroup (X ⧸ gnC T)) (Ti : Subgroup X), gnA T Ti L ≤ gnN T Ti ∧
      gnA T Ti L ≤ L := fun L Ti => ⟨inf_le_left, inf_le_right⟩
  have hcov : ∀ {L : Subgroup (X ⧸ gnC T)}, IsComponentOf L ⊤ →
      IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
      CoveredByTwo L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) := by
    intro L hL hcl P hP
    rcases hpar L hL (isChevTwo_of_classicalTwoOrG2 hcl) P hP with h | h
    · left
      refine le_inf ?_ ((pElementSubgroup_le P).trans hP.1)
      exact h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))
    · right
      exact le_inf h ((pElementSubgroup_le P).trans hP.1)
  have hboth : GNYComponent T T₁ T₂ L₁ → GNYComponent T T₁ T₂ L₂ →
      IsDoublingList (↥L₁ ⧸ Subgroup.center ↥L₁) ∧ IsDoublingList (↥L₂ ⧸ Subgroup.center ↥L₂) := by
    intro hY₁ hY₂
    obtain ⟨⟨D₁₁, hD₁₁, hd₁₁⟩, ⟨D₁₂, hD₁₂, hd₁₂⟩⟩ := hpart hY₁ hcl₁
    obtain ⟨⟨D₂₁, hD₂₁, hd₂₁⟩, ⟨D₂₂, hD₂₂, hd₂₂⟩⟩ := hpart hY₂ hcl₂
    have key : ∀ (Ti : Subgroup X) (hN : NBound (gnN T Ti))
        {La Lb : Subgroup (X ⧸ gnC T)} (hLa : IsComponentOf La ⊤) (hLb : IsComponentOf Lb ⊤)
        (hne' : La ≠ Lb) (hZa : ¬ 3 ∣ Nat.card (Subgroup.center ↥La))
        (Da Db : Subgroup (X ⧸ gnC T)) (hDa : Da ≤ gnA T Ti La) (hDb : Db ≤ gnA T Ti Lb)
        (hda : 3 ∣ Nat.card Da) (hdb : 3 ∣ Nat.card Db),
        3 ∣ Nat.card (gnA T Ti La) ∧ Open.pRank 3 (gnA T Ti La) ≤ 1 ∧
          CFSG.HallHigman.IsPSolvable 3 ↥(gnA T Ti La) := by
      intro Ti hN La Lb hLa hLb hne' hZa Da Db hDa hDb hda hdb
      have hc := comm_inf_of_ne hLa hLb hne' hZa (inf_le_right : gnA T Ti La ≤ La)
        (hDb.trans (inf_le_right : gnA T Ti Lb ≤ Lb))
      exact coverHyp_of_partner hN inf_le_left (hDb.trans inf_le_left)
        (hda.trans (Subgroup.card_dvd_of_le hDa)) hdb hc.1 hc.2
    have hD₁ := hD₁₁
    have b1 := key T₁ hN₁ hL₁ hL₂ hne hZ₁ D₁₁ D₂₁ hD₁₁ hD₂₁ hd₁₁ hd₂₁
    have b2 := key T₂ hN₂ hL₁ hL₂ hne hZ₁ D₁₂ D₂₂ hD₁₂ hD₂₂ hd₁₂ hd₂₂
    have c1 := key T₁ hN₁ hL₂ hL₁ hne.symm hZ₂ D₂₁ D₁₁ hD₂₁ hD₁₁ hd₂₁ hd₁₁
    have c2 := key T₂ hN₂ hL₂ hL₁ hne.symm hZ₂ D₂₂ D₁₂ hD₂₂ hD₁₂ hd₂₂ hd₁₂
    exact ⟨hCov (X ⧸ gnC T) L₁ (gnImg T T ⊓ L₁) (gnA T T₁ L₁) (gnA T T₂ L₁) hL₁.2.2 hcl₁ hS₁
        (hcov hL₁ hcl₁) b1 b2,
      hCov (X ⧸ gnC T) L₂ (gnImg T T ⊓ L₂) (gnA T T₁ L₂) (gnA T T₂ L₂) hL₂.2.2 hcl₂ hS₂
        (hcov hL₂ hcl₂) c1 c2⟩
  by_cases hY₁ : GNYComponent T T₁ T₂ L₁ <;> by_cases hY₂ : GNYComponent T T₁ T₂ L₂
  · exact hboth hY₁ hY₂
  · exfalso
    rcases hnotY hL₂ hY₂ with h | h
    · obtain ⟨⟨D, hD, hd⟩, -⟩ := hpart hY₁ hcl₁
      have hc := comm_inf_of_ne hL₂ hL₁ hne.symm hZ₂ (le_refl L₂) (hD.trans inf_le_right)
      exact false_of_partner hN₁ h (hD.trans inf_le_left) hp₂ h3₂ hd hc.1 hc.2
    · obtain ⟨-, ⟨D, hD, hd⟩⟩ := hpart hY₁ hcl₁
      have hc := comm_inf_of_ne hL₂ hL₁ hne.symm hZ₂ (le_refl L₂) (hD.trans inf_le_right)
      exact false_of_partner hN₂ h (hD.trans inf_le_left) hp₂ h3₂ hd hc.1 hc.2
  · exfalso
    rcases hnotY hL₁ hY₁ with h | h
    · obtain ⟨⟨D, hD, hd⟩, -⟩ := hpart hY₂ hcl₂
      have hc := comm_inf_of_ne hL₁ hL₂ hne hZ₁ (le_refl L₁) (hD.trans inf_le_right)
      exact false_of_partner hN₁ h (hD.trans inf_le_left) hp₁ h3₁ hd hc.1 hc.2
    · obtain ⟨-, ⟨D, hD, hd⟩⟩ := hpart hY₂ hcl₂
      have hc := comm_inf_of_ne hL₁ hL₂ hne hZ₁ (le_refl L₁) (hD.trans inf_le_right)
      exact false_of_partner hN₂ h (hD.trans inf_le_left) hp₁ h3₁ hd hc.1 hc.2
  · exfalso
    have hc := comm_inf_of_ne hL₁ hL₂ hne hZ₁ (le_refl L₁) (le_refl L₂)
    rcases hnotY hL₁ hY₁ with h₁ | h₁ <;> rcases hnotY hL₂ hY₂ with h₂ | h₂
    · exact false_of_partner hN₁ h₁ h₂ hp₁ h3₁ h3₂ hc.1 hc.2
    · have r₁ := pRank_le_one_of_perfect hN₁ h₁ hp₁ h3₁
      have r₂ := pRank_le_one_of_perfect hN₂ h₂ hp₂ h3₂
      have m₁ := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three h₁
      have m₂ := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three h₂
      omega
    · have r₁ := pRank_le_one_of_perfect hN₂ h₁ hp₁ h3₁
      have r₂ := pRank_le_one_of_perfect hN₁ h₂ hp₂ h3₂
      have m₁ := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three h₁
      have m₂ := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three h₂
      omega
    · exact false_of_partner hN₂ h₁ h₂ hp₁ h3₁ h3₂ hc.1 hc.2

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
