module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LargeExtraspecial.OutSixBasic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.Sz32Local (Sz32Data)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (IsSz32Type sz32_data sz32_outer)

private theorem isSz32Type_of_mulEquiv {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {A : Type} [Group A] (e : A ≃* (TauCeti.CFSGIndex.lie d).Group) : IsSz32Type 5 A := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .suzuki 2 := hd
  subst hd'
  exact ⟨rfl, hv, ⟨e⟩⟩

theorem sz32_finite_simple_outer
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2)
    {A : Type} [Group A] (eA : A ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Finite A ∧ IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧ Group.IsSolvable (Outer A) := by
  have hA : IsSz32Type 5 A := isSz32Type_of_mulEquiv hd eA
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hA.2
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  obtain ⟨hfin, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hF'
  haveI : Finite A := Finite.of_equiv _ eF.symm.toEquiv
  haveI hs : IsSimpleGroup A := eF.isSimpleGroup
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨T⟩ : Nonempty (Sylow 5 A) := inferInstance
  have h25 : 5 ^ 2 ∣ Nat.card A := by rw [(sz32_data A hA T).card_group]; norm_num
  refine ⟨inferInstance, hs, CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_five h25,
    ?_⟩
  have hO : Nat.card (Outer A) = 5 := sz32_outer A hA
  haveI : Finite (Outer A) := Nat.finite_of_card_ne_zero (by rw [hO]; norm_num)
  haveI : Group.IsNilpotent (Outer A) :=
    (IsPGroup.of_card (p := 5) (n := 1) (by rw [hO]; norm_num)).isNilpotent
  infer_instance

private theorem sz32_normalizer_le {Y : Type} [Group Y] [Finite Y] {K Y₀ E : Subgroup Y}
    [hKn : K.Normal] (R : Sylow 5 Y) (T' : Sylow 5 K)
    (hT' : (T' : Subgroup K).map K.subtype = (R : Subgroup Y) ⊓ K)
    (D : Sz32Data K (T' : Subgroup K)) (hOut : Nat.card (Outer K) = 5) (hER : E ≤ R)
    (hE : CFSG.Open.IsElemAbelian 5 E) (hEc : Nat.card E = 5 ^ 2)
    (hcore : (if 3 ≤ CFSG.pRank 5 (R : Subgroup Y) then
      CFSG.Open.GLBWeakCore 5 (R : Subgroup Y) else CFSG.Open.GLBCore 5 1 E) ≤ Y₀) :
    normalizer ((T' : Subgroup K) : Set K) ≤ Y₀.subgroupOf K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set T : Subgroup Y := (R : Subgroup Y) ⊓ K with hTdef
  set C : Subgroup Y := centralizer (K : Set Y) with hCdef
  have hKC : K ⊓ C = ⊥ := inf_centralizer_self_eq_bot_of_center D.center_eq_bot
  have hTR : T ≤ R := inf_le_left
  have hTK : T ≤ K := inf_le_right
  have hTcard : Nat.card T = 25 := by
    rw [← hT', Subgroup.card_map_of_injective K.subtype_injective]
    exact D.card_eq
  have hT1 : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hTcard
    omega
  obtain ⟨z, hzT, hz5, hzR⟩ := exists_orderOf_eq_mem_center_of_le_sylow R.isPGroup' hTR
    self_le_normalizer_inf_normal hT1
  have hzK : z ∈ K := hTK hzT
  have hz' : (⟨z, hzK⟩ : K) ∈ (T' : Subgroup K) := by
    rw [← hT'] at hzT
    obtain ⟨w, hw, hwz⟩ := hzT
    have hw' : w = ⟨z, hzK⟩ := Subtype.ext hwz
    rwa [← hw']
  have hnz : ∀ n ∈ normalizer ((T' : Subgroup K) : Set K),
      (n : Y) ∈ normalizer ((zpowers z : Subgroup Y) : Set Y) := by
    intro n hn
    haveI := D.isCyclic
    have h1 := mem_normalizer_zpowers_of_cyclic_normalizer D.isCyclic hz' hn
    have h2 := Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype h1)
    rw [MonoidHom.map_zpowers] at h2
    exact h2
  intro n hn
  rw [Subgroup.mem_subgroupOf]
  by_cases h3 : 3 ≤ CFSG.pRank 5 (R : Subgroup Y)
  · rw [if_pos h3] at hcore
    have h3' : 3 ≤ CFSG.Open.pRank 5 (R : Subgroup Y) := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    have hRC : (R : Subgroup Y) ⊓ C ≠ ⊥ := by
      intro hRC
      set H : Subgroup Y := K ⊔ (R : Subgroup Y) with hHdef
      have hC' := centralizer_subgroupOf_sup_sylow_eq_bot R hKC hRC
      have hidx : (K.subgroupOf H).index ∣ 5 := by
        have := CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv (K.subgroupOf H)
          (by rw [hC']; exact bot_le) (Subgroup.subgroupOfEquivOfLe le_sup_left)
        rwa [hOut] at this
      have hHcard : Nat.card H = Nat.card K * (K.subgroupOf H).index := by
        rw [← Subgroup.card_mul_index (K.subgroupOf H),
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
      obtain ⟨a, ha⟩ := R.isPGroup'.exists_card_eq
      have hdvd : 5 ^ a ∣ 5 ^ 3 * 1301504 := by
        rw [← ha]
        refine (Subgroup.card_dvd_of_le (le_sup_right : (R : Subgroup Y) ≤ H)).trans ?_
        rw [hHcard, D.card_group, show 5 ^ 3 * 1301504 = 32537600 * 5 by norm_num]
        exact Nat.mul_dvd_mul_left _ hidx
      have ha3 : 5 ^ a ∣ 5 ^ 3 :=
        (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 5 1301504)).dvd_of_dvd_mul_right hdvd
      have hR125 : Nat.card (R : Subgroup Y) ≤ 125 := by
        rw [ha]
        exact Nat.le_of_dvd (by norm_num) ha3
      obtain ⟨F, hFR, hF, hFc⟩ :=
        CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (R : Subgroup Y)
      have hF125 : 125 ≤ Nat.card F := by
        rw [hFc]
        calc 125 = 5 ^ 3 := by norm_num
          _ ≤ 5 ^ CFSG.Open.pRank 5 (R : Subgroup Y) := Nat.pow_le_pow_right (by norm_num) h3'
      have hFR' : F = R := Subgroup.eq_of_le_of_card_ge hFR (by omega)
      have hexp : ∀ t ∈ (T' : Subgroup K), t ^ 5 = 1 := by
        intro t ht
        have htR : (t : Y) ∈ F := by
          rw [hFR']
          exact hTR (by rw [← hT']; exact Subgroup.mem_map_of_mem _ ht)
        exact Subtype.ext (by simpa using hF.2 _ htR)
      haveI := D.isCyclic
      have h1 : Monoid.exponent (T' : Subgroup K) ∣ 5 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hexp g g.2)
      rw [IsCyclic.exponent_eq_card, D.card_eq] at h1
      norm_num at h1
    obtain ⟨c, hcRC, hc5, hcR⟩ := exists_orderOf_eq_mem_center_of_le_sylow R.isPGroup'
      inf_le_left (self_le_normalizer_inf_normal (N := C)) hRC
    have hcC : c ∈ C := (Subgroup.mem_inf.mp hcRC).2
    have hcR' : c ∈ (R : Subgroup Y) := (Subgroup.mem_inf.mp hcRC).1
    have hzc : ∀ a ∈ zpowers z, ∀ b ∈ zpowers c, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp ((zpowers_le.mpr hcC) hb) a ((zpowers_le.mpr hzK) ha)
    have hzcbot : zpowers z ⊓ zpowers c = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ K ⊓ C := ⟨(zpowers_le.mpr hzK) hx.1, (zpowers_le.mpr hcC) hx.2⟩
      rwa [hKC] at hx'
    have hXR : zpowers z ⊔ zpowers c ≤ (R : Subgroup Y) :=
      sup_le (zpowers_le.mpr (hTR hzT)) (zpowers_le.mpr hcR')
    have h2X : 1 + 1 ≤ CFSG.Open.pRank 5 (zpowers z ⊔ zpowers c) :=
      le_openPRank_sup_of_commute (by norm_num)
        (CFSG.Open.isElemAbelian_zpowers (hz5 ▸ pow_orderOf_eq_one z))
        (CFSG.Open.isElemAbelian_zpowers (hc5 ▸ pow_orderOf_eq_one c)) hzc hzcbot
        (by rw [Nat.card_zpowers, hz5, pow_one]) (by rw [Nat.card_zpowers, hc5, pow_one]) le_rfl
    have hRX : (R : Subgroup Y) ≤ centralizer ((zpowers z ⊔ zpowers c : Subgroup Y) : Set Y) := by
      rw [← Subgroup.le_centralizer_iff]
      exact sup_le (zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => hzR g hg))
        (zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun g hg => hcR g hg))
    have h3X : 3 ≤ CFSG.Open.pRank 5 ((zpowers z ⊔ zpowers c) ⊔
        ((R : Subgroup Y) ⊓ centralizer ((zpowers z ⊔ zpowers c : Subgroup Y) : Set Y))) := by
      rw [inf_eq_left.mpr hRX]
      exact h3'.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_sup_right)
    have hNX := (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 5 hXR h2X
      h3X).trans hcore
    refine hNX (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hnz n hn, ?_⟩)
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hcC (n : Y) n.2) k).symm.eq
  · rw [if_neg h3] at hcore
    have h2 : CFSG.Open.pRank 5 (R : Subgroup Y) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank]
      omega
    have hzE : z ∈ E :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two
        Nat.prime_five h2 hER hE hEc (hTR hzT) (hz5 ▸ pow_orderOf_eq_one z) hzR
    exact hcore (normalizer_zpowers_le_glbCoreOne (by norm_num) hzE hz5 (hnz n hn))

theorem threeFourTwoNoneAt_sz32
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .suzuki 2) :
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨-, hX1, hX2, hX3⟩ := sz32_finite_simple_outer hd (MulEquiv.refl _)
  refine threeFourTwoNoneAt_of_inf hX1 hX2 hX3 ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ hER hE hEc hcore _ hKY
  haveI := hKn
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hKX
  have hK : IsSz32Type 5 K := isSz32Type_of_mulEquiv hd e
  obtain ⟨T', hT'⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have D : Sz32Data K (T' : Subgroup K) := sz32_data K hK T'
  have hN := sz32_normalizer_le R T' hT' D (sz32_outer K hK) hER hE hEc hcore
  left
  rcases D.maximal hN with h | h
  · have hs : Group.IsSolvable (Y₀.subgroupOf K) := by
      rw [h]
      exact D.isSolvable_normalizer
    exact isSolvable_inf_of_isSolvable_subgroupOf le_rfl hs
  · exact absurd (Subgroup.subgroupOf_eq_top.mp h) hKY

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
