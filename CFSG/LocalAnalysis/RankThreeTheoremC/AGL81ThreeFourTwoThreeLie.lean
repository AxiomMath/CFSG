module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.L34Exclusion
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL34
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoLTwoEight
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34MKlein
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf
import CFSG.LocalAnalysis.StandardType.L34OvergroupInput
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section LThreeFour

variable {q : TauCeti.PrimePower} {d : TauCeti.ValidLieTypeIndex}

private theorem isLinThreeFour_of (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q)
    {L : Type} [Group L] (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : IsLinThreeFour L :=
  ⟨d, ⟨q, hq2, hq4, hd⟩, ⟨e⟩⟩

private theorem isRankThreeL34_of (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q)
    {L : Type} [Group L] (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : IsRankThreeL34 L := by
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  exact ⟨q, hq2, hq4, hv, ⟨e⟩⟩

private theorem card_lThreeFour (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q)
    {L : Type} [Group L] (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) : Nat.card L = 20160 :=
  CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.card_eq_of_isLinThreeFour
    (isLinThreeFour_of hq2 hq4 hd e)

theorem lThreeFour_catalog_facts (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q) :
    IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group ∧
      (∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a) ∧
      Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie d).Group) := by
  have hL := isLinThreeFour_of hq2 hq4 hd (MulEquiv.refl _)
  have hc := card_lThreeFour hq2 hq4 hd (MulEquiv.refl _)
  haveI := CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.isSimpleGroup_of_isLinThreeFour hL
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact ⟨inferInstance, nonabelian_of_simple_of_sq_dvd Nat.prime_three (by rw [hc]; norm_num),
    CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
      (CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.statedModel_of_isLinThreeFour hL)⟩

private theorem lThreeFour_overgroup (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q)
    [Finite (TauCeti.CFSGIndex.lie d).Group] (T : Sylow 3 (TauCeti.CFSGIndex.lie d).Group)
    {H : Subgroup (TauCeti.CFSGIndex.lie d).Group}
    (hTH : normalizer ((T : Subgroup (TauCeti.CFSGIndex.lie d).Group) : Set _) ≤ H)
    (hH : H ≠ ⊤) :
    H ≤ normalizer ((T : Subgroup (TauCeti.CFSGIndex.lie d).Group) : Set _) ∧
      centralizer ((T : Subgroup (TauCeti.CFSGIndex.lie d).Group) : Set _) ⊓ H ≤ T := by
  have hR3 := isRankThreeL34_of hq2 hq4 hd (MulEquiv.refl _)
  have hT9 := l34SylowCard hR3 T
  rcases CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34.normalizer_maximal
      (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index d q hd ⟨hq2, hq4⟩
        (MulEquiv.refl _)) hT9 hTH with h | h
  · refine ⟨h.le, ?_⟩
    have hne : (T : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≠ ⊥ := fun hb => by
      rw [hb, card_bot] at hT9
      omega
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    exact inf_le_left.trans ((centralizer_le (Set.singleton_subset_iff.mpr hu)).trans
      (kFactL34SylowCentralizer _ hR3 T u hu hu1').le)
  · exact absurd h hH

private theorem exists_orderOf_eq_three_of_ne_bot {Y : Type} [Group Y] [Finite Y]
    (R : Sylow 3 Y) {C : Subgroup Y} (hRC : (R : Subgroup Y) ⊓ C ≠ ⊥) :
    ∃ c ∈ (R : Subgroup Y) ⊓ C, orderOf c = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : IsPGroup 3 ((R : Subgroup Y) ⊓ C : Subgroup Y) := R.isPGroup'.to_inf_left
  have h3 : 3 ∣ Nat.card ((R : Subgroup Y) ⊓ C : Subgroup Y) := by
    rcases hp3.card_eq_or_dvd with h1 | h1
    · exact absurd (card_eq_one.mp h1) hRC
    · exact h1
  obtain ⟨⟨c, hc⟩, hco⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact ⟨c, hc, by rwa [orderOf_mk] at hco⟩

private theorem factorization_three_eq_two {n m : ℕ} (hn : n = 3 ^ 2 * m) (hm : ¬ 3 ∣ m) :
    n.factorization 3 = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 3)
  rw [hn, Nat.factorization_def _ Nat.prime_three, padicValNat.mul (by norm_num) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm]

private theorem lThreeFour_normalizer_le
    (hq2 : q.p = 2) (hq4 : q.exponent = 2) (hd : d.1 = .A 2 q)
    {Y : Type} [Group Y] [Finite Y] {K Y₀ E : Subgroup Y} [K.Normal] (R : Sylow 3 Y)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hER : E ≤ R) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2)
    (hcore : (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀)
    (hRY₀ : (R : Subgroup Y) ≤ Y₀) (hKY₀ : ¬ K ≤ Y₀)
    (hsol : ¬ Group.IsSolvable (Y₀.subgroupOf K)) :
    normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : IsLinThreeFour K := isLinThreeFour_of hq2 hq4 hd e
  have hR3 : IsRankThreeL34 K := isRankThreeL34_of hq2 hq4 hd e
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  set T₀ : Subgroup Y := (R : Subgroup Y) ⊓ K with hT₀
  have hT₀c : Nat.card T₀ = 3 ^ 2 := by
    rw [← hT, card_map_of_injective K.subtype_injective, l34SylowCard hR3 T]
    norm_num
  have hT₀e : IsElemAbelian 3 T₀ :=
    hT ▸ CFSG.SectionRank.isElemAbelian_map (l34SylowElemAbelian hR3 T) K.subtype
  have hT₀2 : 2 ≤ CFSG.Open.pRank 3 T₀ :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hT₀e hT₀c
  have hZK : ∀ x ∈ K, x ∈ centralizer (K : Set Y) → x = 1 := by
    intro x hxK hxC
    have hz : (⟨x, hxK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hxC g g.2)
    rw [CFSG.HardMathSupport.Meierfrankenfeld.L34Offender.center_eq_bot_of_isLinThreeFour hL,
      mem_bot] at hz
    exact congrArg Subtype.val hz
  by_cases h3 : 3 ≤ pRank 3 (R : Subgroup Y)
  ·
    rw [if_pos h3] at hcore
    refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 inf_le_left hT₀2
      ?_).trans hcore
    by_cases hRC : (R : Subgroup Y) ⊓ centralizer (K : Set Y) = ⊥
    ·
      exfalso
      haveI : Finite (MulAut K) := MulEquiv.finite_left
      let θ : (R : Subgroup Y) →* MulAut K := MulAut.conjNormal.comp (R : Subgroup Y).subtype
      have hθ : Function.Injective θ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro r hr
        have hrC : (r : Y) ∈ centralizer (K : Set Y) := mem_centralizer_iff.mpr fun m hm => by
          have h1 := congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hr) ⟨m, hm⟩)
          simp only [θ, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply,
            MulAut.one_apply] at h1
          exact (mul_inv_eq_iff_eq_mul.mp h1).symm
        have h2 : (r : Y) ∈ (R : Subgroup Y) ⊓ centralizer (K : Set Y) := ⟨r.2, hrC⟩
        rw [hRC, mem_bot] at h2
        exact mem_bot.mpr (Subtype.ext h2)
      have h1 := CFSG.SectionRank.pRank_top_le_of_injective (by norm_num : 1 < 3) θ hθ
      have h2 := CFSG.LocalAnalysis.GLTheoremB.pRank_mulAut_le_two_of_isLThreeFour
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.isLThreeFour_of_index d q hd ⟨hq2, hq4⟩ e)
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
      omega
    · obtain ⟨c, hcRC, hc3⟩ := exists_orderOf_eq_three_of_ne_bot R hRC
      have hcT : c ∉ T₀ := fun h => by
        have h1 := hZK c h.2 hcRC.2
        rw [h1, orderOf_one] at hc3
        omega
      have hcc : ∀ a ∈ T₀, a * c = c * a := fun a ha => mem_centralizer_iff.mp hcRC.2 a ha.2
      obtain ⟨hF, hFc⟩ := isElemAbelian_sup_zpowers hT₀e hcT hc3 hcc
      have hcR : c ∈ (R : Subgroup Y) ⊓ centralizer (T₀ : Set Y) :=
        mem_inf.mpr ⟨hcRC.1, mem_centralizer_iff.mpr hcc⟩
      have hle : T₀ ⊔ zpowers c ≤ T₀ ⊔ ((R : Subgroup Y) ⊓ centralizer (T₀ : Set Y)) :=
        sup_le_sup_left (zpowers_le.mpr hcR) _
      exact CFSG.SectionRank.le_pRank (by norm_num) hle hF (k := 3) (by rw [hFc, hT₀c]; norm_num)
  ·
    rw [if_neg h3] at hcore
    have hR2 : CFSG.Open.pRank 3 (R : Subgroup Y) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      omega
    set X' : Subgroup K := Y₀.subgroupOf K with hX'
    have hTX' : (T : Subgroup K) ≤ X' := fun t ht => by
      have h1 : (t : Y) ∈ T₀ := hT ▸ mem_map_of_mem K.subtype ht
      exact mem_subgroupOf.mpr (hRY₀ h1.1)
    have hX'top : X' ≠ ⊤ := fun htop =>
      hKY₀ fun k hk => mem_subgroupOf.mp (htop ▸ mem_top (⟨k, hk⟩ : K))
    have hX'3 : ¬ 3 ∣ X'.index := fun h => T.not_dvd_index (h.trans (index_dvd_of_le hTX'))
    obtain hs | ⟨-, ⟨eJ⟩⟩ := CFSG.StandardType.ggSeitzExcLThreeFourOvergroupInput_holds K d q hq2
      hq4 hd ⟨e⟩ X' hX'top hX'3
    · exact absurd hs hsol
    set J₀ : Subgroup Y := ((commutator X').map X'.subtype).map K.subtype with hJ₀
    have hJ₀eq : J₀ = ⁅Y₀ ⊓ K, Y₀ ⊓ K⁆ := by
      rw [hJ₀, map_subtype_commutator, map_commutator, hX', subgroupOf_map_subtype]
    have hJ₀K : J₀ ≤ K := map_subtype_le _
    let φJ : J₀ ≃* alternatingGroup (Fin 6) :=
      ((equivMapOfInjective _ K.subtype K.subtype_injective).symm.trans
        (equivMapOfInjective _ X'.subtype X'.subtype_injective).symm).trans eJ
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup J₀ := φJ.isSimpleGroup
    have hJ₀c : Nat.card J₀ = 360 := by
      rw [Nat.card_congr φJ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have hZJ : center J₀ = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot J₀
      (nonabelian_of_simple_of_sq_dvd Nat.prime_three (by rw [hJ₀c]; norm_num))
    have hRN : (R : Subgroup Y) ≤ normalizer (J₀ : Set Y) := by
      intro r hr
      have hr' : r ∈ normalizer ((Y₀ ⊓ K : Subgroup Y) : Set Y) := by
        rw [mem_normalizer_iff]
        intro h
        constructor
        · rintro ⟨hh0, hhK⟩
          exact ⟨Y₀.mul_mem (Y₀.mul_mem (hRY₀ hr) hh0) (Y₀.inv_mem (hRY₀ hr)),
            ‹K.Normal›.conj_mem h hhK r⟩
        · rintro ⟨hh0, hhK⟩
          refine ⟨?_, ?_⟩
          · have h1 := Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem (hRY₀ hr)) hh0) (hRY₀ hr)
            simpa [mul_assoc] using h1
          · have h1 := ‹K.Normal›.conj_mem _ hhK r⁻¹
            simpa [mul_assoc] using h1
      rw [mem_normalizer_iff_map_conj_eq] at hr' ⊢
      rw [hJ₀eq, map_commutator, hr']
    have hRCJ : (R : Subgroup Y) ⊓ centralizer (J₀ : Set Y) = ⊥ := by
      by_contra hne
      obtain ⟨c, hcRC, hc3⟩ := exists_orderOf_eq_three_of_ne_bot R hne
      obtain ⟨S'⟩ : Nonempty (Sylow 3 J₀) := inferInstance
      set S : Subgroup Y := (S' : Subgroup J₀).map J₀.subtype with hS
      have hSc : Nat.card S = 3 ^ 2 := by
        rw [hS, card_map_of_injective J₀.subtype_injective, Sylow.card_eq_multiplicity,
          factorization_three_eq_two (m := 40) (by rw [hJ₀c]; norm_num) (by norm_num)]
      have hSJ : S ≤ J₀ := map_subtype_le _
      have hSK : S ≤ K := hSJ.trans hJ₀K
      have hSe : IsElemAbelian 3 S := by
        have hcard : Nat.card (S.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
          rw [Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv, hSc,
            factorization_three_eq_two (m := 2240)
              (by rw [card_lThreeFour hq2 hq4 hd e]; norm_num) (by norm_num)]
        have h1 := l34SylowElemAbelian hR3 (Sylow.ofCard (S.subgroupOf K) hcard)
        rw [Sylow.coe_ofCard] at h1
        have h2 := CFSG.SectionRank.isElemAbelian_map h1 K.subtype
        rwa [subgroupOf_map_subtype, inf_eq_left.mpr hSK] at h2
      have hcS : c ∉ S := fun h => by
        have hz : (⟨c, hSJ h⟩ : J₀) ∈ center J₀ :=
          mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hcRC.2 g g.2)
        rw [hZJ, mem_bot] at hz
        have h1 : c = 1 := congrArg Subtype.val hz
        rw [h1, orderOf_one] at hc3
        omega
      have hcc : ∀ a ∈ S, a * c = c * a := fun a ha => mem_centralizer_iff.mp hcRC.2 a (hSJ ha)
      obtain ⟨hF, hFc⟩ := isElemAbelian_sup_zpowers hSe hcS hc3 hcc
      have h1 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
        CFSG.SectionRank.le_pRank (by norm_num) le_top hF (k := 3) (by rw [hFc, hSc]; norm_num)
      rw [← (CFSG.SectionRank.pRank_sylow R).1] at h1
      omega
    have hR9 : Nat.card (R : Subgroup Y) ∣ 9 := by
      let ρ : (R : Subgroup Y) →* MulAut J₀ := J₀.normalizerMonoidHom.comp (inclusion hRN)
      have hρ : Function.Injective ρ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro r hr
        have h1 : inclusion hRN r ∈ J₀.normalizerMonoidHom.ker := hr
        rw [normalizerMonoidHom_ker, mem_subgroupOf, coe_inclusion] at h1
        have h2 : (r : Y) ∈ (R : Subgroup Y) ⊓ centralizer (J₀ : Set Y) := ⟨r.2, h1⟩
        rw [hRCJ, mem_bot] at h2
        exact mem_bot.mpr (Subtype.ext h2)
      have hP : IsPGroup 3 (ρ.range.map (MulAut.congr φJ).toMonoidHom) :=
        (R.isPGroup'.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective).map _
      have h1 := CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_dvd_nine_of_isPGroup hP
      rwa [card_map_of_injective (MulAut.congr φJ).injective,
        ← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv] at h1
    have hRT : T₀ = R := eq_of_le_of_card_ge inf_le_left (by
      have h1 := Nat.le_of_dvd (by norm_num) hR9
      rw [hT₀c]
      omega)
    have hET : E = T₀ := eq_of_le_of_card_ge (hER.trans hRT.ge) (by rw [hT₀c, hEc])
    rw [← hET]
    have hE1 : 1 ≤ CFSG.Open.pRank 3 E :=
      (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE hEc).trans' (by norm_num)
    have hNE : normalizer (E : Set Y) ≤ GLBCore 3 1 E := le_sSup ⟨E, le_rfl, hE1, rfl⟩
    exact hNE.trans hcore

theorem threeFourTwoNoneAt_lThreeFour
    (hq2 : q.p = 2) (hq4 : q.exponent = 2)
    (hd : d.1 = .A 2 q) : ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨hs, hnab, hout⟩ := lThreeFour_catalog_facts hq2 hq4 hd
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group :=
    Nat.finite_of_card_ne_zero (by rw [card_lThreeFour hq2 hq4 hd (MulEquiv.refl _)]; norm_num)
  refine threeFourTwoNoneAt_of_model hs hnab hout ?_
  intro Y _ _ K Y₀ E R hp _ hKn e _ _ _ hER hE hEc hcore hRY₀ hKY₀
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set H : Subgroup (TauCeti.CFSGIndex.lie d).Group := (Y₀.subgroupOf K).map e.toMonoidHom
    with hH
  by_cases hsol : Group.IsSolvable H
  · exact exists_solvable_centralizer_of_isSolvable hsol
  have hsol' : ¬ Group.IsSolvable (Y₀.subgroupOf K) := fun h => hsol (by
    haveI := h
    exact Group.isSolvable_of_surjective
      (f := (equivMapOfInjective (Y₀.subgroupOf K) e.toMonoidHom e.injective).toMonoidHom)
      (equivMapOfInjective (Y₀.subgroupOf K) e.toMonoidHom e.injective).surjective)
  have hN := lThreeFour_normalizer_le hq2 hq4 hd R e hER hE hEc hcore hRY₀ hKY₀ hsol'
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hT₂ : ((T.mapSurjective he : Sylow 3 (TauCeti.CFSGIndex.lie d).Group) :
      Subgroup (TauCeti.CFSGIndex.lie d).Group) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective he T
  have hNH : normalizer (((T.mapSurjective he : Sylow 3 (TauCeti.CFSGIndex.lie d).Group) :
      Subgroup (TauCeti.CFSGIndex.lie d).Group) : Set _) ≤ H := by
    intro x hx
    rw [hT₂, ← map_equiv_normalizer_eq] at hx
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hx
    refine mem_map_of_mem _ (mem_subgroupOf.mpr (hN ?_))
    have h2 := le_normalizer_map K.subtype (mem_map_of_mem K.subtype hk)
    rwa [hT] at h2
  have hHtop : H ≠ ⊤ := by
    intro htop
    refine hKY₀ fun k hk => ?_
    have h1 : e ⟨k, hk⟩ ∈ H := htop ▸ mem_top _
    obtain ⟨k', hk', hkk'⟩ := mem_map.mp h1
    have hk'' : k' = ⟨k, hk⟩ := e.injective hkk'
    rw [hk''] at hk'
    exact mem_subgroupOf.mp hk'
  obtain ⟨hHN, hCN⟩ := lThreeFour_overgroup hq2 hq4 hd _ hNH hHtop
  exact ⟨_, le_normalizer.trans hNH, Sylow.isPGroup' _, hHN,
    isSolvable_centralizer_inf_of_le hp (Sylow.isPGroup' _) hCN⟩

end LThreeFour

theorem threeFourTwoThreeLie_holds :
    ThreeFourTwoThreeLie := by
  rintro q d hq2 (⟨hq3, hd⟩ | ⟨hq4, hd⟩)
  · exact threeFourTwoNoneAt_lTwoEight hq2 hq3 hd
  · exact threeFourTwoNoneAt_lThreeFour hq2 hq4 hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
