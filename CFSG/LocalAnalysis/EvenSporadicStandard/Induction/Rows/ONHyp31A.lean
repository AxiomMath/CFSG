module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddExt
public import CFSG.Timmesfeld.Final.Simple

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.ONSchreier CFSG.Sporadic.SuzOddCore Cover

theorem upFacts_nil : UpFacts [] where
  fi23 _ h := absurd h List.not_mem_nil
  not_exc _ h := absurd h List.not_mem_nil
  odd _ h := absurd h List.not_mem_nil
  rank _ h := absurd h List.not_mem_nil

theorem onL_cq_lieModel : LieModel (↥onL ⧸ center ↥onL) .PSL 3 2 2 :=
  Or.inl ⟨by decide, lQuot_classicalModel⟩

theorem onL_quasisimple : CFSG.IsQuasisimple ↥onL :=
  isQuasisimple_of_perfect_simple_quotient inferInstance (MulEquiv.refl _)
    (CFSG.Timmesfeld.isSimpleGroup_of_lieModel onL_cq_lieModel)

theorem finite_onL : Finite ↥onL :=
  Nat.finite_of_card_ne_zero (by rw [card_onL]; norm_num)

theorem even_card_center_onL : Even (Nat.card (center ↥onL)) := ⟨2, by rw [card_center_onL]⟩

theorem onL_oddCore_eq_bot : CFSG.oddCore ↥onL = ⊥ := by
  have := finite_onL
  have hle : CFSG.oddCore ↥onL ≤ center ↥onL := oddCore_le_center onL_quasisimple
  have hdvd : Nat.card ↥(CFSG.oddCore ↥onL) ∣ 4 := by
    rw [← card_center_onL]
    exact Subgroup.card_dvd_of_le hle
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥onL)) := odd_card_oddCore' ↥onL
  have h1 : Nat.card ↥(CFSG.oddCore ↥onL) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hodd)) hdvd
  exact Subgroup.card_eq_one.1 h1

theorem isKON_cq_equiv {X : Type} [Group X] (hX : IsKON X) :
    Nonempty ((X ⧸ center X) ≃* (↥onL ⧸ center ↥onL)) :=
  isOddCentralExt_cq hX (IsOddCentralExt.self onL_quasisimple)

theorem lieModel_cq_of_isKON {X : Type} [Group X] (hX : IsKON X) :
    LieModel (X ⧸ center X) .PSL 3 2 2 := by
  obtain ⟨e⟩ := isKON_cq_equiv hX
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm onL_cq_lieModel

theorem even_center_of_isKON_quot {K₁ : Type} [Group K₁] [Finite K₁]
    (hq : CFSG.IsQuasisimple K₁) (hK : IsKON (K₁ ⧸ CFSG.oddCore K₁)) :
    Even (Nat.card (center K₁)) := by
  have hperf : Group.IsPerfect K₁ := hq.1
  have : Finite ↥onL := finite_onL
  have hX : Even (Nat.card (center (K₁ ⧸ CFSG.oddCore K₁))) :=
    IsOddCentralExt.even_center even_card_center_onL hK
  exact even_card_center_of_cover (QuotientGroup.mk' (CFSG.oddCore K₁))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hq) hX

theorem isKON_of_pair {Y : Type} [Group Y] [Finite Y] {N' P : Subgroup Y} (hN : FStarSimple N')
    (hsN : IsSporadic ↥N' .ONan) (hq : CFSG.IsQuasisimple ↥P)
    (hZ : Nonempty (↥(center ↥P) ≃* Multiplicative (ZMod 4)))
    (hQ : LieModel (↥P ⧸ center ↥P) .PSL 3 2 2) (hle : P ≤ N') : IsKON ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNZ : center ↥N' = ⊥ := Hyp.center_eq_bot_of_simple hN.isSimpleGroup hN.nonabelian
  have hcov : OddCover .ONan N' :=
    ⟨isQuasisimple_of_simple_nonabelian hN.isSimpleGroup hN.nonabelian, by
      rw [hNZ]
      simp, by
      obtain ⟨f⟩ := hsN
      exact ⟨((QuotientGroup.quotientMulEquivOfEq hNZ).trans QuotientGroup.quotientBot).trans f⟩⟩
  obtain ⟨e⟩ := hZ
  have hZcard : Nat.card ↥(center ↥P) = 4 := by
    rw [Nat.card_congr e.toEquiv]
    simp
  have hPcard : Nat.card ↥P = 80640 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P)
    rw [card_of_lieModel_psl_three hQ, hZcard] at h1
    rw [h1]
    norm_num [ordA_two]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥P) 2 (by rw [hZcard]; norm_num)
  have hz2 : orderOf (((z : ↥P)) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hz
  have hqinj : Function.Injective (q ↥N') := by
    rw [← MonoidHom.ker_eq_bot_iff]
    unfold q
    rw [QuotientGroup.ker_mk', hNZ]
  have hcard : Nat.card ↥((P.subgroupOf N').map (q ↥N')) = 80640 := by
    rw [Subgroup.card_map_of_injective hqinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hPcard]
  refine on_rowIsK .ONan (List.mem_singleton_self _) Y N' P (((z : ↥P)) : Y) hcov
    ⟨hle (z : ↥P).2, hz2, hle, fun k hk => ?_, hq.1, hcard⟩
  have h1 := Subgroup.mem_center_iff.1 z.2 ⟨k, hk⟩
  exact congrArg Subtype.val h1

structure ONHyp31Inputs : Prop where
  suz_bridge : LieModel ↥suzD .PSL 3 2 2
  outer_j1 : ONOuterFixedJ1
  k2_fixed : ONK2FixedNotLam
  on_eight : SporadicOrderEight .ONan
  on_odd : ONOddCenter
  he_rank : HeCoverRank

theorem on_kEven : KEven IsKON := by
  intro X _ hX
  have : Finite ↥onL := finite_onL
  exact IsOddCentralExt.even_center even_card_center_onL hX

theorem on_loPair (lit : Sol78Lit) : LoPair IsKON [.ONan] [] [.Suz] SOR := by
  intro s hs Y _ _ hUY N' P' hN hidx hK hsN hP hq hR hns hlow
  rcases List.mem_singleton.1 hs with rfl
  have hnON : ¬ IsSporadic (↥P' ⧸ center ↥P') .ONan := fun h => hns ⟨.ONan, by simp, h⟩
  have hsuz : IsSporadic (↥P' ⧸ center ↥P') .Suz → Even (Nat.card ↥(center ↥P')) := fun h => by
    by_contra hne
    exact hlow (Nat.not_even_iff_odd.1 hne) ⟨.Suz, List.mem_singleton_self _, h⟩
  have hL3 := so_pair_suz (lit.thm46 Y hUY) hN hidx hK hP hq (so_hty hR hnON) hsuz hsN
  have hs3 : IsSimpleGroup ↥P' := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL3
  have hcard : Nat.card ↥P' = 20160 := by
    rw [card_of_lieModel_psl_three hL3]
    norm_num [ordA_two]
  have hnc : ∃ a b : ↥P', a * b ≠ b * a :=
    nonabelian_of_isSimpleGroup_of_not_prime (by rw [hcard]; norm_num)
  have hZ : center ↥P' = ⊥ := center_eq_bot_of_isSimpleGroup_nonabelian hnc
  obtain ⟨e⟩ := lieModel_psl_three_four_equiv hL3 onL_cq_lieModel
  refine ⟨⟨↥onL, inferInstance, IsOddCentralExt.self onL_quasisimple,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩⟩, ?_⟩
  rw [hZ, Subgroup.card_bot]
  exact odd_one

theorem onReachRow (lit : Sol78Lit) (inp : ONHyp31Inputs) :
    ReachRow IsKON [.ONan] [] [.Suz] SOR where
  iso := soR_iso
  fi23 s hs := by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact on_fi23
    · exact absurd h List.not_mem_nil
  fi23_lo s hs := by
    rcases List.mem_singleton.1 hs with rfl
    exact suz_fi23
  K_reach X _ hX := Or.inl ⟨2, le_rfl, lieModel_cq_of_isKON hX⟩
  K_quot X _ hX := by
    have := finite_onL
    exact isOddCentralExt_quot onL_oddCore_eq_bot hX
  K_not_sporadic X _ hX s hs hsp := by
    have hc : Nat.card (X ⧸ center X) = 20160 :=
      (IsOddCentralExt.card_quotient hX).trans card_quotient_onL
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      have := on_card_pinned _ hsp
      omega
    · exact absurd h List.not_mem_nil
  K_odd_lo X _ hX _ s hs hsp := by
    have hc : Nat.card (X ⧸ center X) = 20160 :=
      (IsOddCentralExt.card_quotient hX).trans card_quotient_onL
    rcases List.mem_singleton.1 hs with rfl
    have := suz_card_pinned _ hsp
    omega
  lo := Or.inr ⟨on_loPair lit, on_kEven⟩
  K_iso X Y _ _ hX hY hXo hYo := by
    have := finite_onL
    exact isOddCentralExt_iso onL_oddCore_eq_bot hX hY hXo hYo
  K_cq X Y _ _ hX hY := isOddCentralExt_cq hX hY
  not_exc := soR_notExc
  sp_not_exc s hs := by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact on_sp_not_exc
    · exact absurd h List.not_mem_nil
  rank X _ _ hq hR _ :=
    so_rank inp.on_odd inp.he_rank (fun X' _ _ _ hS => suz_cover_rank inp.suz_bridge hS) X hq hR
  up_reach _ hs := absurd hs List.not_mem_nil
  closure Y _ _ hUY N' hN hidx hK P hP hq hR hns hlow _ _ :=
    so_closure_core (lit.thm46 Y hUY) hN hidx hK hP hq hR
      (fun h => hns ⟨.ONan, by simp, h⟩) (fun h => by
      by_contra hne
      exact hlow (Nat.not_even_iff_odd.1 hne) ⟨.Suz, List.mem_singleton_self _, h⟩)
  notR Y _ _ N hN hidx _ := by
    rintro ⟨L, hLL, s, hs, hcov⟩
    rcases List.mem_singleton.1 hs with rfl
    exact so_notR on_card_pinned (by norm_num) inp.on_eight hN hidx hLL hcov
  pair_into Y _ _ hUY N' hN hidx hK P hP hq hR hns hlow _ := by
    rintro ⟨s, hs, hsN⟩
    rcases List.mem_singleton.1 hs with rfl
    have hnON : ¬ IsSporadic (↥P ⧸ center ↥P) .ONan := fun h => hns ⟨.ONan, by simp, h⟩
    have hsuz : IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P)) := fun h => by
      by_contra hne
      exact hlow (Nat.not_even_iff_odd.1 hne) ⟨.Suz, List.mem_singleton_self _, h⟩
    obtain ⟨hZ, hQ, hle⟩ := so_pair_on (lit.thm46 Y hUY) hN hidx hK hP hq (so_hty hR hnON) hsuz hsN
    have hK := isKON_of_pair hN hsN hq hZ hQ hle
    have := finite_onL
    exact isOddCentralExt_quot onL_oddCore_eq_bot hK

end CFSG.EvenSporadicStandard.Induction
