module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PerfectSolv
public import CFSG.RankThree.PartTwo.Sec4.T444.Coprime

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open scoped commutatorElement

section Transfer

variable {X : Type} [Group X] [Finite X]

theorem not_three_dvd_card_of_isPGroup_two {K : Subgroup X} (hK : IsPGroup 2 K) :
    ¬ 3 ∣ Nat.card K := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  omega

theorem pRank_gnImg_le (T : Subgroup X) (hC : ¬ 3 ∣ Nat.card (gnC T)) (Y : Subgroup X) :
    Open.pRank 3 (gnImg T Y) ≤ Open.pRank 3 Y := by
  refine CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three
    (QuotientGroup.mk' (gnC T)) ?_ Y
  rw [QuotientGroup.ker_mk']
  exact hC

theorem no_perfect_gnImg (T : Subgroup X) (N : Subgroup X)
    (h : ∀ J : Subgroup X, J ≤ N → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) :
    ∀ Js : Subgroup (X ⧸ gnC T), Js ≤ gnImg T N → ⁅Js, Js⁆ = Js → ¬ 3 ∣ Nat.card Js := by
  intro Js hJs hJp h3
  set f : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T) with hf
  set Jh : Subgroup X := N ⊓ Js.comap f with hJh
  let ψ : ↥Jh →* ↥Js := (f.comp Jh.subtype).codRestrict Js (fun j => j.2.2)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, hny⟩ := hJs hy
    exact ⟨⟨n, hn, by show f n ∈ Js; rw [hny]; exact hy⟩, Subtype.ext hny⟩
  have hperf : ⁅(⊤ : Subgroup ↥Js), (⊤ : Subgroup ↥Js)⁆ = (⊤ : Subgroup ↥Js) := by
    have : Group.IsPerfect ↥Js := Subgroup.isPerfect_iff.mpr hJp
    exact this.commutator_eq_top
  obtain ⟨K, hKp, hKm⟩ := exists_perfect_map_eq_top hperf (Nat.card ↥Jh) ψ rfl hsurj
  have h3K : 3 ∣ Nat.card K := by
    have hc : Nat.card (K.map ψ) ∣ Nat.card K := Subgroup.card_map_dvd _ _
    rw [hKm, Subgroup.card_top] at hc
    exact h3.trans hc
  refine h (K.map Jh.subtype) ((Subgroup.map_subtype_le K).trans inf_le_left) ?_ ?_
  · rw [← Subgroup.map_commutator, hKp]
  · rw [Subgroup.card_map_of_injective Jh.subtype_injective]
    exact h3K

end Transfer

theorem isChevTwo_of_classicalOverTwo {Y : Type} [Group Y] (h : IsClassicalOverTwo Y) :
    IsChevTwo Y := by
  obtain ⟨d, hd, -, he⟩ := h
  exact Or.inl ⟨d, isChevIndexTwo_of_classical hd, he⟩

theorem isOneImageList_of_gn (hGN : GlaubermanNilesInput) (hCov : KFactParabolicCoverOne)
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    (hC : ¬ 3 ∣ Nat.card (gnC T))
    (hD : ∀ T' : Subgroup X, T' ≠ ⊥ → T' ≤ T → (T'.subgroupOf T).Characteristic →
      Open.pRank 3 (Subgroup.normalizer (T' : Set X)) ≤ 2 ∧
      (2 ≤ Open.pRank 3 (Subgroup.normalizer (T' : Set X)) →
        ∀ J : Subgroup X, J ≤ Subgroup.normalizer (T' : Set X) → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J))
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hcl : IsClassicalOverTwo (↥L ⧸ Subgroup.center ↥L)) (h3 : 3 ≤ Open.pRank 3 L)
    (hS : IsSylowTwoOf (gnImg T T ⊓ L) L) :
    IsOneImageList (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨T₁, T₂, hpair, hpar, -⟩ := hGN X T hX (hX.ne_bot_of_isComponentOf hL)
  have hT₁ : T₁ ≤ T := hpair.le_center.trans (QuasithinUnique.Setup.omegaOneCenterOf_le T)
  have hbound : ∀ Ti : Subgroup X, Ti ≠ ⊥ → Ti ≤ T → (Ti.subgroupOf T).Characteristic →
      Open.pRank 3 (gnA T Ti L) ≤ 2 ∧
        (Open.pRank 3 (gnA T Ti L) = 2 → CFSG.HallHigman.IsPSolvable 3 ↥(gnA T Ti L)) := by
    intro Ti h1 h2 h3'
    obtain ⟨hr, hp⟩ := hD Ti h1 h2 h3'
    have hle : Open.pRank 3 (gnA T Ti L) ≤ Open.pRank 3 (Subgroup.normalizer (Ti : Set X)) :=
      (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans (pRank_gnImg_le T hC _)
    refine ⟨hle.trans hr, fun h2' => ?_⟩
    have h2le : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Ti : Set X)) := h2' ▸ hle
    exact isPSolvable_three_of_no_perfect _ (fun J hJ hJp =>
      no_perfect_gnImg T _ (hp h2le) J (hJ.trans inf_le_left) hJp)
  obtain ⟨b₁, s₁⟩ := hbound T₁ hpair.ne_bot₁ hT₁ hpair.char₁
  obtain ⟨b₂, s₂⟩ := hbound T₂ hpair.ne_bot₂ hpair.le₂ hpair.char₂
  refine hCov (X ⧸ gnC T) L (gnImg T T ⊓ L) (gnA T T₁ L) (gnA T T₂ L) hL.2.2 hcl h3 hS ?_
    ⟨b₁, s₁⟩ ⟨b₂, s₂⟩
  intro P hP
  rcases hpar L hL (isChevTwo_of_classicalOverTwo hcl) P hP with h | h
  · left
    refine le_inf ?_ ((pElementSubgroup_le P).trans hP.1)
    exact h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))
  · right
    exact le_inf h ((pElementSubgroup_le P).trans hP.1)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
