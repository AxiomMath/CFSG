module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SOInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzCoverRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.OddExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzONHyp31

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.Sporadic.SuzOddCore

section SuzD


theorem suzD_quasisimple : CFSG.IsQuasisimple ↥suzD :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2
    (isQuasisimple_of_simple suzD_simple suzD_noncomm)

theorem suzD_center_eq_bot : center ↥suzD = ⊥ := by
  have := suzD_simple
  exact center_eq_bot_of_isSimpleGroup_nonabelian suzD_noncomm

theorem suzD_oddCore_eq_bot : CFSG.oddCore ↥suzD = ⊥ :=
  le_bot_iff.1 (suzD_center_eq_bot ▸ oddCore_le_center suzD_quasisimple)

theorem finite_suzD : Finite ↥suzD :=
  Nat.finite_of_card_ne_zero (by rw [card_suzD]; norm_num)

theorem isKSuz_cq_equiv {X : Type} [Group X] (hX : IsKSuz X) :
    Nonempty ((X ⧸ center X) ≃* ↥suzD) := by
  obtain ⟨e⟩ := isOddCentralExt_cq hX (IsOddCentralExt.self suzD_quasisimple)
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq suzD_center_eq_bot).trans
    QuotientGroup.quotientBot)⟩

theorem lieModel_cq_of_isKSuz (hb : LieModel ↥suzD .PSL 3 2 2) {X : Type} [Group X]
    (hX : IsKSuz X) : LieModel (X ⧸ center X) .PSL 3 2 2 := by
  obtain ⟨e⟩ := isKSuz_cq_equiv hX
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hb

theorem odd_center_of_isKSuz_quot {K₁ : Type} [Group K₁] [Finite K₁]
    (hq : CFSG.IsQuasisimple K₁) (hK : IsKSuz (K₁ ⧸ CFSG.oddCore K₁)) :
    Odd (Nat.card (center K₁)) := by
  have := finite_suzD
  have hperf : Group.IsPerfect K₁ := hq.1
  obtain ⟨hXq, π, hπs, hπc, hπo⟩ := hK
  have hX : Group.IsPerfect (K₁ ⧸ CFSG.oddCore K₁) := hXq.1
  have h1 := card_center_eq_of_cover (QuotientGroup.mk' (CFSG.oddCore K₁))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hq)
  have h2 := card_center_eq_of_cover π hπs hπc
  have hZ : Nat.card (center ↥suzD) = 1 := by rw [suzD_center_eq_bot]; exact Subgroup.card_bot
  rw [QuotientGroup.ker_mk'] at h1
  rw [h1, h2, hZ, mul_one]
  exact (odd_card_oddCore' K₁).mul hπo

theorem cq_equiv_of_isKSuz_quot {K₁ : Type} [Group K₁] [Finite K₁]
    (hq : CFSG.IsQuasisimple K₁) (hK : IsKSuz (K₁ ⧸ CFSG.oddCore K₁)) :
    Nonempty ((K₁ ⧸ center K₁) ≃* ↥suzD) := by
  have hperf : Group.IsPerfect K₁ := hq.1
  obtain ⟨e₁⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore K₁))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hq)
  obtain ⟨e₂⟩ := isKSuz_cq_equiv hK
  exact ⟨e₁.trans e₂⟩

@[expose] def SuzAutCentralizerN0 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H) (N₀ : Subgroup H),
    OddCover .Suz L → SuzQ H L K u → CanLoc K N₀ →
      Group.IsSolvable ↥(autCentralizer L N₀) ∧
        (∀ A : Subgroup ↥(autCentralizer L N₀), IsPGroup 2 A →
          (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ 4) ∧
        (∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g)

@[expose] def SuzOuterNoLink : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H), OddCover .Suz L → K ≤ L →
    CFSG.IsQuasisimple ↥K → IsKSuz (↥K ⧸ CFSG.oddCore ↥K) →
      ∀ σ : MulAut ↥L, σ * σ = 1 → (∀ k : ↥L, (k : H) ∈ K → σ k = k) →
        ∃ g : ↥L, σ = MulAut.conj g

structure SuzHyp31Inputs : Prop where
  bridge : LieModel ↥suzD .PSL 3 2 2
  aut_centralizer : SuzAutCentralizerN0
  outer : SuzOuterNoLink
  k2_fixed : SuzK2FixedNotLam2
  suz_eight : SporadicOrderEight .Suz
  on_odd : ONOddCenter
  he_rank : HeCoverRank
  even : EvenCoverExclHered .Suz

end SuzD

section SuzReach


theorem suzReachRow (lit : Sol78Lit) (inp : SuzHyp31Inputs) :
    ReachRow IsKSuz [.Suz] [.ONan] [] SOR where
  iso := soR_iso
  fi23 s hs := by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact suz_fi23
    · rcases List.mem_singleton.1 h with rfl
      exact on_fi23
  fi23_lo _ hs := absurd hs List.not_mem_nil
  K_reach X _ hX := Or.inl ⟨2, le_rfl, lieModel_cq_of_isKSuz inp.bridge hX⟩
  K_quot X _ hX := by
    have := finite_suzD
    exact isOddCentralExt_quot suzD_oddCore_eq_bot hX
  K_not_sporadic X _ hX s hs hsp := by
    have hc : Nat.card (X ⧸ center X) = 20160 :=
      (IsOddCentralExt.card_quotient hX).trans card_quotient_suzD
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      have := suz_card_pinned _ hsp
      omega
    · rcases List.mem_singleton.1 h with rfl
      have := on_card_pinned _ hsp
      omega
  K_odd_lo _ _ _ _ _ hs := absurd hs List.not_mem_nil
  lo := Or.inl fun _ hs => absurd hs List.not_mem_nil
  K_iso X Y _ _ hX hY hXo hYo := by
    have := finite_suzD
    exact isOddCentralExt_iso suzD_oddCore_eq_bot hX hY hXo hYo
  K_cq X Y _ _ hX hY := isOddCentralExt_cq hX hY
  not_exc := soR_notExc
  sp_not_exc s hs := by
    rcases List.mem_append.1 hs with h | h
    · rcases List.mem_singleton.1 h with rfl
      exact suz_sp_not_exc
    · rcases List.mem_singleton.1 h with rfl
      exact on_sp_not_exc
  rank X _ _ hq hR _ :=
    so_rank inp.on_odd inp.he_rank (fun X' _ _ _ hS => suz_cover_rank inp.bridge hS) X hq hR
  up_reach s hs X _ h := by
    rcases List.mem_singleton.1 hs with rfl
    exact Or.inr (Or.inr (Or.inr h))
  closure Y _ _ hUY N' hN hidx hK P hP hq hR hns _ _ _ :=
    so_closure_core (lit.thm46 Y hUY) hN hidx hK hP hq hR (fun h => hns ⟨.ONan, by simp, h⟩)
      (fun h => (hns ⟨.Suz, by simp, h⟩).elim)
  notR Y _ _ N hN hidx _ := by
    rintro ⟨L, hLL, s, hs, hcov⟩
    rcases List.mem_singleton.1 hs with rfl
    exact so_notR suz_card_pinned (by norm_num) inp.suz_eight hN hidx hLL hcov
  pair_into Y _ _ hUY N' hN hidx hK P hP hq hR hns _ _ := by
    rintro ⟨s, hs, hsN⟩
    rcases List.mem_singleton.1 hs with rfl
    have hnON : ¬ IsSporadic (↥P ⧸ center ↥P) .ONan := fun h => hns ⟨.ONan, by simp, h⟩
    have hL3 := so_pair_suz (lit.thm46 Y hUY) hN hidx hK hP hq (so_hty hR hnON)
      (fun h => (hns ⟨.Suz, by simp, h⟩).elim) hsN
    obtain ⟨e⟩ := lieModel_psl_three_four_equiv hL3 inp.bridge
    have hK : IsKSuz ↥P :=
      IsOddCentralExt.isoInv ↥suzD ↥suzD ↥P e.symm (IsOddCentralExt.self suzD_quasisimple)
    have := finite_suzD
    exact isOddCentralExt_quot suzD_oddCore_eq_bot hK

end SuzReach

end CFSG.EvenSporadicStandard.Induction
