module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One12
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Transport
public import CFSG.RankThree.PartOne.KE.E6TwFourData
public import CFSG.RankThree.PartOne.AUTSL.PushShared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule CFSG.SeitzReduction
  CFSG.StandardType CFSG.LieType.Steinberg.Exceptional CFSG.SectionRank
  CFSG.SeitzReduction.F4Pilot CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One

theorem twE6Model165At_one : TwE6Model165At 1 := by
  intro k _ _ _ n p q θ hk hθ hn hp hp2 hrk hq hq2 hqp hqd
  letI : Finite ↥(e6Data_valid.minGroup k) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid k
  intro A hA hSC hmax hrank
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  let H' : Subgroup (e6Data_valid.minGroup (GaloisField 2 (2 * n))) :=
    fixedGroup (GaloisField 2 (2 * n)) (frobQ 2 n)
  let e : ↥(fixedGroup k θ) ≃* ↥H' :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6Transport.fixedGroupMulEquiv_galois
      (by omega) θ hk hθ
  let AG : Subgroup ↥H' := A.map e.toMonoidHom
  have hAG : IsElemAbelian p AG := CFSG.SectionRank.isElemAbelian_map hA e.toMonoidHom
  have hAGrank : CFSG.Open.pRank p AG = CFSG.Open.pRank p A :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_map_eq_of_injective
      hp.one_lt e.toMonoidHom e.injective A
  have htop : CFSG.Open.pRank p (⊤ : Subgroup ↥H') =
      CFSG.Open.pRank p (⊤ : Subgroup ↥(fixedGroup k θ)) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
  have hmaxG : CFSG.Open.pRank p (⊤ : Subgroup ↥H') ≤ CFSG.Open.pRank p AG := by
    rw [htop, hAGrank]
    exact hmax
  have hrankG : 3 ≤ CFSG.Open.pRank p AG := by
    rw [hAGrank]
    exact hrank
  have hSCG : ∀ c ∈ Subgroup.centralizer (AG : Set ↥H'), orderOf c = p → c ∈ AG := by
    intro c hc hcorder
    obtain ⟨d, rfl⟩ := e.surjective c
    have hdorder : orderOf d = p := by
      rw [← hcorder]
      exact (orderOf_injective e.toMonoidHom e.injective d).symm
    have hd : d ∈ Subgroup.centralizer (A : Set ↥(fixedGroup k θ)) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro a ha
      have h := hc (e a) (Subgroup.mem_map_of_mem e.toMonoidHom ha)
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    exact Subgroup.mem_map_of_mem e.toMonoidHom (hSC d hd hdorder)
  let σe : GaloisField 2 (2 * n) ≃+* GaloisField 2 (2 * n) :=
    RingEquiv.ofBijective (frobQ 2 n)
      ⟨Function.LeftInverse.injective
          (fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 n (by omega) c),
        Function.LeftInverse.surjective
          (fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 n (by omega) c)⟩
  have hkk : Nat.card (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe) = 2 ^ n := by
    let ee : ↥(CFSG.RankThree.PartOne.AUTSL.fixSubfield σe) ≃
        {x : GaloisField 2 (2 * n) // σe x = x} :=
      { toFun := fun x =>
          ⟨x.1, (CFSG.RankThree.PartOne.AUTSL.mem_fixSubfield).1 x.2⟩
        invFun := fun x =>
          ⟨x.1, (CFSG.RankThree.PartOne.AUTSL.mem_fixSubfield).2 x.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun x => by ext; rfl }
    rw [Nat.card_congr ee]
    exact CFSG.RankThree.PartOne.KE.card_fixSubfield_twisted Nat.prime_two (by omega)
      (TwE6Toral.card_galoisField_two_mul n (by omega))
      σe (fun c => frobQ_apply 2 n c)
  have hj : ∀ x : (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe),
      frobQ 2 n (algebraMap (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
        (GaloisField 2 (2 * n)) x) =
      algebraMap (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
        (GaloisField 2 (2 * n)) x := by
    intro x
    change frobQ 2 n (x : GaloisField 2 (2 * n)) = (x : GaloisField 2 (2 * n))
    exact (CFSG.RankThree.PartOne.AUTSL.mem_fixSubfield).1 x.2
  let hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
    TwistedE6Pilot.unitaryFieldData_of_card (by omega)
      (TwE6Toral.card_galoisField_two_mul n (by omega))
  have hσ : ∀ c, frobQ 2 n c = c ^ 2 ^ n := fun c => frobQ_apply 2 n c
  have hfin : Finite ↥H' := inferInstance
  have hconclG : Concl165Avoid ↥H' p q AG (Subgroup.center ↥H') := by
    rcases eq_or_ne p 3 with hp3 | hp3
    ·
      subst hp3
      have h3 : ¬ 3 ∣ 2 ^ n + 1 := not_three_dvd_two_pow_add_one_of_rk2Ord_one hrk
      have hSC3 : ∀ c ∈ Subgroup.centralizer
          (AG : Set ↥H'), c ^ 3 = 1 → c ∈ AG := by
        intro c hc hc3
        rcases eq_or_ne c 1 with h1 | h1
        · rw [h1]; exact AG.one_mem
        · exact hSCG c hc (orderOf_eq_prime hc3 h1)
      obtain ⟨ζ, hζ, hζo, g₁, hA₁el, hA₁map⟩ :=
        exists_conj_eq_threeFrame_lift_of_maximal_rank (by omega : 1 ≤ n) h3 hAG hmaxG hSC3
      have hζbar : hU.bar (ζ : GaloisField 2 (2 * n)) = (ζ : GaloisField 2 (2 * n)) := by
        rw [TwistedE6Pilot.bar_apply_eq hU hσ, frobQ_apply]
        simpa using congrArg Units.val (ExcFrames.zeta_pow_frobQ_eq_self hζ h3)
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have h3dvd : 3 ∣ 2 ^ n - 1 :=
        (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_eq_one_iff).mp hrk
      have h3dvd' : 3 ∣ Nat.card (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)ˣ := by
        rw [Nat.card_units, hkk]
        exact h3dvd
      obtain ⟨t, ht⟩ : ∃ t : (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)ˣ,
          orderOf t = 3 := exists_prime_orderOf_dvd_card' 3 h3dvd'
      have hframe : (ExcFrames.twE6ThreeFrameHom (by omega : 1 ≤ n) h3 ζ hζ).range =
          thetaTorusP (f := n) t ⊔
            (R3Levi hU 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf (C0 n) :=
        range_twE6ThreeFrameHom_eq_model (by omega : 1 ≤ n) h3 hkk hU hζ hζo hζbar ht hσ
      have hmodel0 : ∀ (A₁ : Subgroup ↥H'), IsElemAbelian 3 A₁ →
          A₁.map (twistedIsogenyC (by omega : 1 ≤ n)
            (TwE6Toral.card_galoisField_two_mul n (by omega)) (frobQ 2 n)
            (fun c => frobQ_apply 2 n c)) =
            thetaTorusP (f := n) t ⊔
              (R3Levi hU 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf
                (C0 n) →
          Concl165Avoid ↥H' 3 q A₁ (Subgroup.center ↥H') :=
        fun A₁ hA hmap => concl165Avoid_twE6_model (f := n) (p := 3) (q := q)
          (by omega : 1 ≤ n) hkk hj hp hp2 hq hqd hU hζo hζbar ht hA hmap
      have hA₁map' : (CFSG.Quasithin.A1b.conjSub g₁ AG).map
          (twistedIsogenyC (by omega : 1 ≤ n)
            (TwE6Toral.card_galoisField_two_mul n (by omega)) (frobQ 2 n)
            (fun c => frobQ_apply 2 n c)) =
          thetaTorusP (f := n) t ⊔
            (R3Levi hU 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf (C0 n) := by
        rw [hA₁map, hframe]
      have hconcl₁ : Concl165Avoid ↥H' 3 q (CFSG.Quasithin.A1b.conjSub g₁ AG)
          (Subgroup.center ↥H') := hmodel0 _ hA₁el hA₁map'
      exact CFSG.LocalAnalysis.GLTheoremA.Y10F.concl165Avoid_of_conj hp hq
        (Subgroup.instNormalCenter) g₁ (by
          simpa [CFSG.Quasithin.A1b.conjSub] using hconcl₁)
    ·
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with hlt | hge
        · interval_cases p
          · norm_num at hp
          · norm_num at hp
          · exact absurd rfl hp2
          · exact absurd rfl hp3
          · norm_num at hp
        · exact hge
      have hpdvd : p ∣ 2 ^ n - 1 :=
        (CFSG.LocalAnalysis.GLTheoremA.rk2Ord_eq_one_iff).mp hrk
      letI : Fact p.Prime := ⟨hp⟩
      have hpdvd' : p ∣ Nat.card (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)ˣ := by
        rw [Nat.card_units, hkk]
        exact hpdvd
      obtain ⟨t, ht⟩ : ∃ t : (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)ˣ, orderOf t = p :=
        exists_prime_orderOf_dvd_card' p hpdvd'
      let ζ : (GaloisField 2 (2 * n))ˣ :=
        Units.map (algebraMap _ (GaloisField 2 (2 * n))).toMonoidHom t
      haveI : NeZero p := ⟨hp.ne_zero⟩
      have hζ : orderOf ζ = p := by
        rw [show ζ = Units.map (algebraMap
            (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
            (GaloisField 2 (2 * n))).toMonoidHom t from rfl,
          orderOf_injective _ (Units.map_injective
            (algebraMap (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
              (GaloisField 2 (2 * n))).injective) t, ht]
      have hζbar : hU.bar (ζ : GaloisField 2 (2 * n)) = (ζ : GaloisField 2 (2 * n)) := by
        rw [TwistedE6Pilot.bar_apply_eq hU hσ]
        change frobQ 2 n (algebraMap (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
            (GaloisField 2 (2 * n)) t) =
          algebraMap (CFSG.RankThree.PartOne.AUTSL.fixSubfield σe)
            (GaloisField 2 (2 * n)) t
        exact hj t
      obtain ⟨A₁, g₁, hA₁el, hA₁eq, hA₁map, hA₁Z⟩ :=
        exists_conj_eq_model_lift_of_maximal_rank (by omega : 1 ≤ n) hp hp5 hrk hkk
          hU hζ hζbar ht hσ hAG hmaxG
      have hconcl₁ := concl165Avoid_twE6_model (f := n) (p := p) (q := q)
        (by omega : 1 ≤ n) hkk hj hp hp2 hq hqd hU hζ hζbar ht hA₁el hA₁map
      refine CFSG.LocalAnalysis.GLTheoremA.Y10F.concl165Avoid_of_conj hp hq
        (Subgroup.instNormalCenter) g₁ ?_
      rwa [hA₁eq, CFSG.Quasithin.A1b.conjSub] at hconcl₁
  have hconclMap : Concl165Avoid ↥H' p q (A.map e.toMonoidHom)
      ((Subgroup.center ↥(fixedGroup k θ)).map e.toMonoidHom) := by
    rw [show (Subgroup.center ↥(fixedGroup k θ)).map e.toMonoidHom =
      Subgroup.center ↥H' from Subgroup.map_center_eq e]
    exact hconclG
  exact CFSG.LocalAnalysis.GLTheoremA.Y10F.concl165Avoid_of_mulEquiv hp hq e hconclMap

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
