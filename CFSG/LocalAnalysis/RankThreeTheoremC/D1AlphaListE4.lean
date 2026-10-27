module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE3
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverResidual
public import CFSG.RankThree.PartOne.S11d.OutPCyclicThetaClosed
public import CFSG.RankThree.PartOne.S11c.Co1Cover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Assembly TauCeti Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne (ActualCoverETypeRankThreeOnlyE6FieldTwo)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open scoped commutatorElement

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

section OffList

theorem four_le_twoLocalOddRank_of_offList {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) {s : SporadicName}
    (hs : s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group) :
    4 ≤ CFSG.twoLocalOddRank K := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2.1
  have hnonab := hq.2.2
  obtain ⟨c⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group s
  let e2 : K ⧸ Subgroup.center K ≃* Carrier s := e.trans c.symm
  let π : (⊤ : Subgroup K) →* K ⧸ Subgroup.center K :=
    (QuotientGroup.mk' (Subgroup.center K)).comp
      (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom
  have hπs : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv : (⊤ : Subgroup K) ≃* K).surjective
  let ψ : (⊤ : Subgroup K) →* Carrier s := (e2 : K ⧸ Subgroup.center K →* Carrier s).comp π
  have hψs : Function.Surjective ψ := e2.surjective.comp hπs
  let iso : ((⊤ : Subgroup K) ⧸ ψ.ker) ≃* Carrier s :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  have hsec := CFSG.RankThree.PartOne.sporadicSectionCases_closed
  have hev : 4 ≤ CFSG.Assembly.evenRank K → 4 ≤ CFSG.twoLocalOddRank K := fun h => by
    rwa [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · have hker : π.ker ≤ center (⊤ : Subgroup K) := by
      intro x hx
      have hx' : (x : K) ∈ Subgroup.center K := by
        have : QuotientGroup.mk' (Subgroup.center K) (x : K) = 1 := hx
        exact (QuotientGroup.eq_one_iff _).mp this
      rw [Subgroup.mem_center_iff] at hx' ⊢
      intro g
      exact Subtype.ext (hx' g)
    exact CFSG.RankThree.PartOne.co1ActualArbitraryCentralCoversForceTwoLocalRankFour K ⊤
      (K ⧸ Subgroup.center K) π hπs ⟨e2⟩ hker
  · exact hev (hsec.fi22 K ⊤ ψ.ker ⟨iso⟩)
  · exact hev (hsec.fi23 K ⊤ ψ.ker ⟨iso⟩)
  · exact hev (hsec.fi24 K ⊤ ψ.ker ⟨iso⟩)
  · exact hev (hsec.b K ⊤ ψ.ker ⟨iso⟩)
  · exact hev (hsec.m K ⊤ ψ.ker (K ⧸ Subgroup.center K) hnonab ⟨iso.trans e2.symm⟩ ⟨e2⟩)

end OffList

section Sporadic

theorem sporadic_eq_m22_or_onan (hL : KFactAlphaLifts) {K : Type} [Group K] [Finite K]
    (hq : CFSG.IsQuasisimple K) (he : CFSG.twoLocalOddRank K ≤ 3)
    (hm : Open.pRank 3 (⊤ : Subgroup K) ≤ 3) (h3 : 3 ∣ Nat.card (Subgroup.center K))
    {s : SporadicName} (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.sporadic s).Group) :
    s = .M22 ∨ s = .ONan := by
  have htc : IsThreeCenterCover K (CFSGIndex.sporadic s).Group := ⟨hq, h3, ⟨e⟩⟩
  have hexK : 4 ≤ CFSG.twoLocalOddRank K → False := fun h => by omega
  have hnot : (s = .M11 ∨ s = .M12 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .HS ∨
      s = .He ∨ s = .Ru ∨ s = .J4) → False := fun hs => not_isThreeCenterCover_sporadic hs htc
  have hoff : (s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M) → False :=
    fun hs => hexK (four_le_twoLocalOddRank_of_offList hq hs e)
  cases s with
  | M22 => exact Or.inl rfl
  | ONan => exact Or.inr rfl
  | J3 =>
    have h4 := HasLiftableTriple.four_le_pRank_of_cover hL.j3 e h3
    omega
  | McL =>
    have h4 := HasLiftableTriple.four_le_pRank_of_cover hL.mcl e h3
    omega
  | Suz => exact (hexK (tripleCoverSuzRankFour K htc)).elim
  | Ly => exact (hexK (tripleCoverSporadicResidual.ly K htc)).elim
  | Co3 => exact (hexK (tripleCoverSporadicResidual.co3 K htc)).elim
  | Co2 => exact (hexK (tripleCoverSporadicResidual.co2 K htc)).elim
  | HN => exact (hexK (tripleCoverSporadicResidual.hn K htc)).elim
  | Th => exact (hexK (tripleCoverSporadicResidual.th K htc)).elim
  | Co1 => exact (hoff (by simp)).elim
  | Fi22 => exact (hoff (by simp)).elim
  | Fi23 => exact (hoff (by simp)).elim
  | Fi24Prime => exact (hoff (by simp)).elim
  | B => exact (hoff (by simp)).elim
  | M => exact (hoff (by simp)).elim
  | M11 => exact (hnot (by simp)).elim
  | M12 => exact (hnot (by simp)).elim
  | M23 => exact (hnot (by simp)).elim
  | M24 => exact (hnot (by simp)).elim
  | J1 => exact (hnot (by simp)).elim
  | J2 => exact (hnot (by simp)).elim
  | HS => exact (hnot (by simp)).elim
  | He => exact (hnot (by simp)).elim
  | Ru => exact (hnot (by simp)).elim
  | J4 => exact (hnot (by simp)).elim

end Sporadic

section Final

theorem kFactAlphaListM3_of_inputs (hGA : GriessMultipliersAllModels)
    (hE : ActualCoverETypeRankThreeOnlyE6FieldTwo) (hL : KFactAlphaLifts) :
    KFactAlphaListM3 := by
  intro K _ _ hq hK he hcat hZ hZ3 hcyc hrk
  have hq' : CFSG.IsQuasisimple K := isQuasisimple_of_open' hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card (Subgroup.center K) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    rcases k with _ | k
    · exfalso
      apply hZ
      rw [Subgroup.eq_bot_iff_card]
      simpa using hk
    · exact dvd_pow_self 3 (Nat.succ_ne_zero k)
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hq'.2.2
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm (G := Multiplicative (ZMod p)) _ _
  | alternating n hn =>
    rcases tripleCoverAlternating n K hn ⟨hq', h3dvd, ⟨e⟩⟩ with rfl | rfl
    · exact Or.inl ⟨e⟩
    · exact Or.inr (Or.inl ⟨e⟩)
  | sporadic s =>
    rcases sporadic_eq_m22_or_onan hL hq' he hrk h3dvd e with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e⟩)))
  | lie d =>
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d,
      isLinThreeCover3_of_lieCover (tripleCoverLie_of_griess hGA) hE
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll hL hK hq' he hrk hZ3 h3dvd d e, ⟨e⟩⟩)))

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC
