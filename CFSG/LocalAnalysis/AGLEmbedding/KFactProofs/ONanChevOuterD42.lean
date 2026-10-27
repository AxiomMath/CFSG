module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Link
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoRank
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Outer
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterParts
public import Certificates.Certificate9415
import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec19.Step199Proof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

open CFSG.Quasithin CFSG.Open CFSG.AGLEmbedding.D4Two CFSG.RankThree.PartTwo.Sec4.Item434D42
  CFSG.RankThree.PartTwo.Sec4 CFSG.SectionRank

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace CFSG.AGLEmbedding.ChevOuter

local notation "Inn" =>
  CFSG.ComponentClassification.OuterAutomorphisms.inner lineGroup

theorem map_conj_eq_of_normal {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance n hn g
  · intro n hn
    refine ⟨g⁻¹ * n * g, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

set_option linter.unusedSectionVars false


theorem inn_le_weakCore_sylow (hZ : Subgroup.center lineGroup = ⊥)
    (P : Sylow 3 (MulAut lineGroup)) :
    Inn ≤ GLBWeakCore 3 (P : Subgroup (MulAut lineGroup)) := by
  obtain ⟨-, -, hEcard⟩ := d42Group_facts hZ Certificates.certificate9587
  have hE : IsPGroup 3 d42Group := IsPGroup.of_card hEcard
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut lineGroup) Q P
  have hPQ : (P : Subgroup (MulAut lineGroup)) =
      (Q : Subgroup (MulAut lineGroup)).map (MulAut.conj g).toMonoidHom := by
    have h : ((g • Q : Sylow 3 (MulAut lineGroup)) : Subgroup (MulAut lineGroup)) =
        (P : Subgroup (MulAut lineGroup)) :=
      congrArg (fun S : Sylow 3 (MulAut lineGroup) => (S : Subgroup (MulAut lineGroup))) hg
    rw [← h, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have h1 : Inn ≤ GLBWeakCore 3 (Q : Subgroup (MulAut lineGroup)) :=
    inn_le_weakCore hZ hQ
  have h2 := map_glbWeakCore_le Nat.prime_three (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective (Q : Subgroup (MulAut lineGroup))
  rw [← hPQ] at h2
  have h3 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h1
  have := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal lineGroup
  rw [map_conj_eq_of_normal Inn g] at h3
  exact h3.trans h2

theorem chevOuterGenAt_d42 (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.LocalAnalysis.RankThreeTheoremC.IsChevTwoOuter3D42Index d) :
    CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterGenAt d := by
  intro X _ _ K hKn hq ⟨e⟩ hC hodd R hR
  obtain ⟨q, hqp, hq1, hdq⟩ := hd
  have : K.Normal := hKn
  have : Group.IsPerfect K := ⟨hq.1⟩
  obtain ⟨hmod, ⟨eT⟩⟩ := exists_model_equiv d q hqp hq1 hdq e
  have hZ3 : IsPGroup 3 (Subgroup.center K) := by
    let f : Subgroup.center K →* Subgroup.centralizer (K : Set X) :=
      (K.subtype.comp (Subgroup.center K).subtype).codRestrict
        (Subgroup.centralizer (K : Set X)) (fun z => by
          rw [Subgroup.mem_centralizer_iff]
          intro k hk
          have := Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩
          exact congrArg Subtype.val this)
    have hinj : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact hC.of_injective f hinj
  have hZodd : Odd (Nat.card (QuotientGroup.mk' (Subgroup.center K)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ3
    rw [hn]
    exact Odd.pow (by decide)
  have hZK : Subgroup.center K = ⊥ := by
    have := triality_even_perfect_odd_cover_trivial hmod (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hZodd
    rwa [QuotientGroup.ker_mk'] at this
  have hCX : Subgroup.centralizer (K : Set X) = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hC
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hne
      rw [← Subgroup.card_eq_one]
      simpa using hn
    have h3 : 3 ∣ Nat.card (Subgroup.centralizer (K : Set X)) := by
      rw [hn]
      exact dvd_pow_self 3 hn0
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hxo : orderOf (x : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have := hodd x x.2 hxo
    rw [hZK, Subgroup.map_bot, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hxo
    omega
  let eKL : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot).symm
  let eK : K ≃* lineGroup := eKL.trans eT
  have hZL : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ := by
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
    have : Group.IsPerfect (K ⧸ Subgroup.center K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
        (QuotientGroup.mk'_surjective _)
    exact Item434SmallTwoIII.center_eq_bot_of_simple_perfect
  have hZT : Subgroup.center lineGroup = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : eT.symm z ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply eT.injective
      simpa using hz (eT y)
    rw [hZL, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    simpa using congrArg eT hz'
  let ρ : X →* MulAut lineGroup :=
    (MulAut.congr eK).toMonoidHom.comp (MulAut.conjNormal : X →* MulAut K)
  have hρK : ∀ k : K, ρ (k : X) = MulAut.conj (eK k) := by
    intro k
    show MulAut.congr eK (MulAut.conjNormal (k : X)) = _
    rw [MulAut.conjNormal_val]
    refine MulEquiv.ext fun t => ?_
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (MulAut.conjNormal x : MulAut K) = 1 := by
      exact (MulAut.congr eK).injective (by rw [map_one]; exact hx)
    have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun α : MulAut K => ((α ⟨k, hk⟩ : K) : X)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hCX] at hxc
    exact hxc
  have hKne : K ≠ ⊤ := by
    intro hKtop
    have hrank : Open.pRank 3 (R : Subgroup X) ≤ 2 := by
      apply CFSG.SectionRank.pRank_le (by norm_num)
      intro E hER hE
      have hEK : E ≤ K := by rw [hKtop]; exact le_top
      have hE' : IsElemAbelian 3 (E.subgroupOf K) :=
        isElemAbelian_of_equiv_le hE le_rfl (Subgroup.subgroupOfEquivOfLe hEK)
      have hb := d4TwoRankTwo K d q hqp hq1 hdq ⟨eKL.trans e⟩ (E.subgroupOf K) hE'
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv] at hb
    omega
  have hOut : Nat.card (Outer lineGroup) = 3 :=
    Item434SmallTwoIII.card_outer_d42 (chevalleyExceptionalModel_of_mulEquiv eT.symm hmod)
  have hinnCard : Nat.card Inn = Nat.card lineGroup := by
    show Nat.card (MulAut.conj : lineGroup →* MulAut lineGroup).range = _
    rw [← Nat.card_congr (MonoidHom.ofInjective
      (Item434Kit.conj_injective_of_center_eq_bot hZT)).toEquiv]
  have hAutCard : Nat.card (MulAut lineGroup) = 3 * Nat.card lineGroup := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Inn, hinnCard]
    exact congrArg (· * Nat.card lineGroup) hOut
  have hKcard : Nat.card K = Nat.card lineGroup := Nat.card_congr eK.toEquiv
  have hXcard : Nat.card X = Nat.card K * K.index := (Subgroup.card_mul_index K).symm
  have hρcard : Nat.card ρ.range = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hdvd : Nat.card ρ.range ∣ Nat.card (MulAut lineGroup) := Subgroup.card_subgroup_dvd_card _
  have hpos : 0 < Nat.card lineGroup := Nat.card_pos
  have hidx : K.index ∣ 3 := by
    rw [hρcard, hXcard, hKcard, hAutCard] at hdvd
    exact (Nat.mul_dvd_mul_iff_left hpos).1 (by rwa [mul_comm 3] at hdvd)
  have hidx3 : K.index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h | h
    · exact absurd (Subgroup.index_eq_one.1 h) hKne
    · exact h
  have hρtop : ρ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hρcard, hXcard, hKcard, hidx3, hAutCard, mul_comm]
  let ρ' : X ≃* MulAut lineGroup :=
    MulEquiv.ofBijective ρ ⟨hρinj, MonoidHom.range_eq_top.1 hρtop⟩
  have hρ'K : ∀ k : K, ρ' (k : X) = MulAut.conj (eK k) := hρK
  have hsurj : Function.Surjective ρ'.toMonoidHom := ρ'.surjective
  let P : Sylow 3 (MulAut lineGroup) := Sylow.mapSurjective hsurj R
  have h1 := inn_le_weakCore_sylow hZT P
  have h2 := map_glbWeakCore_le Nat.prime_three ρ'.symm.toMonoidHom ρ'.symm.injective
    (P : Subgroup (MulAut lineGroup))
  have hPR : (P : Subgroup (MulAut lineGroup)).map ρ'.symm.toMonoidHom = (R : Subgroup X) := by
    show ((R : Subgroup X).map ρ'.toMonoidHom).map ρ'.symm.toMonoidHom = _
    rw [Subgroup.map_map]
    ext x
    simp
  rw [hPR] at h2
  intro k hk
  have hmem : ρ' k ∈ Inn := ⟨eK ⟨k, hk⟩, (hρ'K ⟨k, hk⟩).symm⟩
  have h3 := h2 (Subgroup.mem_map_of_mem ρ'.symm.toMonoidHom (h1 hmem))
  simpa using h3

theorem kFactChevTwoOuterGen3D42 :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactChevTwoOuterGen3D42 :=
  fun d hd => chevOuterGenAt_d42 d hd

end CFSG.AGLEmbedding.ChevOuter
