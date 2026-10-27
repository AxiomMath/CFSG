module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Desc2

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

theorem odd_ker_of_isK {A K Y : Type*} [Group A] [Finite A] [Group K] [Group Y] [Finite Y]
    (π : A →* K) (σ : K →* Y) (hπ : Function.Surjective π) (hσ : Function.Surjective σ)
    (hY : CFSG.oddCore Y = ⊥) (hA : Nonempty ((A ⧸ CFSG.oddCore A) ≃* Y)) :
    Odd (Nat.card σ.ker) := by
  obtain ⟨e⟩ := hA
  let τ : A →* Y := σ.comp π
  have hτ : Function.Surjective τ := hσ.comp hπ
  have hOA : Odd (Nat.card (CFSG.oddCore A)) := odd_card_oddCore' A
  have hle : CFSG.oddCore A ≤ τ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hn : (Subgroup.map τ (CFSG.oddCore A)).Normal := Subgroup.Normal.map inferInstance τ hτ
    have hodd : Odd (Nat.card (Subgroup.map τ (CFSG.oddCore A))) :=
      hOA.of_dvd_nat (Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective τ _))
    have := le_oddCore_of_normal_odd hn hodd ⟨x, hx, rfl⟩
    rw [hY, Subgroup.mem_bot] at this
    exact this
  have hcard : Nat.card τ.ker = Nat.card (CFSG.oddCore A) := by
    have h1 : Nat.card τ.ker * Nat.card τ.range = Nat.card A := Subgroup.card_ker_mul_card_range τ
    have h2 : Nat.card τ.range = Nat.card Y := by
      rw [MonoidHom.range_eq_top_of_surjective τ hτ, Subgroup.card_top]
    have h3 : Nat.card (A ⧸ CFSG.oddCore A) * Nat.card (CFSG.oddCore A) = Nat.card A :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore A)).symm
    have h4 : Nat.card (A ⧸ CFSG.oddCore A) = Nat.card Y := Nat.card_congr e.toEquiv
    rw [h2] at h1
    rw [h4] at h3
    have hpos : 0 < Nat.card Y := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, mul_comm, h3])
  have hker : σ.ker = Subgroup.map π τ.ker := by
    ext k
    constructor
    · intro hk
      obtain ⟨a, rfl⟩ := hπ k
      exact ⟨a, hk, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  rw [hker]
  exact (hcard ▸ hOA).of_dvd_nat (Subgroup.card_dvd_of_surjective
    (MonoidHom.subgroupMap_surjective π _))

theorem isK_quot_of_cover (hKiso : IsK.IsoInv)
    (hquot : ∀ (X : Type) [Group X], IsK X → IsK (X ⧸ CFSG.oddCore X))
    (hiso : ∀ (X Y : Type) [Group X] [Group Y], IsK X → IsK Y → CFSG.oddCore X = ⊥ →
      CFSG.oddCore Y = ⊥ → Nonempty (X ≃* Y))
    {A K : Type} [Group A] [Finite A] [Group K] (π : A →* K) (hπ : Function.Surjective π)
    (hA : IsK (A ⧸ CFSG.oddCore A)) {Y : Type} [Group Y] (σ : K →* Y)
    (hσ : Function.Surjective σ) (hY : IsK Y) : IsK (K ⧸ CFSG.oddCore K) := by
  have : Finite Y := Finite.of_surjective (σ.comp π) (hσ.comp hπ)
  have : Finite K := Finite.of_surjective π hπ
  let σ' : K →* Y ⧸ CFSG.oddCore Y := (QuotientGroup.mk' (CFSG.oddCore Y)).comp σ
  have hσ' : Function.Surjective σ' := (QuotientGroup.mk'_surjective _).comp hσ
  have hY' : IsK (Y ⧸ CFSG.oddCore Y) := hquot Y hY
  have hYo : CFSG.oddCore (Y ⧸ CFSG.oddCore Y) = ⊥ := oddCore_quotient_eq_bot
  obtain ⟨eA⟩ := hiso _ _ hA hY' oddCore_quotient_eq_bot hYo
  have hodd := odd_ker_of_isK π σ' hπ hσ' hYo ⟨eA⟩
  obtain ⟨e⟩ := oddQuot_equiv_of_surj σ' hσ' hodd
  have eY : ((Y ⧸ CFSG.oddCore Y) ⧸ CFSG.oddCore (Y ⧸ CFSG.oddCore Y)) ≃*
      (Y ⧸ CFSG.oddCore Y) :=
    (QuotientGroup.quotientMulEquivOfEq hYo).trans QuotientGroup.quotientBot
  exact hKiso _ _ (e.trans eY).symm hY'

structure DescCtx (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK : GroupClass)
    (S Up Lo : List TauCeti.SporadicName) (R : GroupClass) : Prop where
  junction : JunctionStmtAt H
  thm22 : Sol78Thm22Sec H
  ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H
  hUp : NoUp Up H
  rc : ReachFacts IsK S Up Lo R
  hKiso : IsK.IsoInv
  hN : FStarSimple N
  hidx : N.index ≤ 2
  hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H

omit [Finite H] in
theorem inL_of_transGen {A Y : Subgroup H} (h : TransGen Lt A Y) : InL Y := by
  induction h with
  | single h => exact lt_inL_right h
  | tail _ h _ => exact lt_inL_right h

theorem false_of_lo_link5b (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H)
    (hUp : NoUp Up H) (rc : ReachFacts IsK S Up Lo R) (hpair : LoPair IsK S Up Lo R)
    (hKeven : KEven IsK) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) (hL0 : InL (L 0))
    (hreach : ∀ i, i ≤ m → Reached R K₁ (L i)) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (h5b : Sol78Link5b (L i) (L (i - 1)) (s i)) (hodd : Odd (Nat.card ↥(center ↥(L i))))
    (hLo : ∃ s ∈ Lo, IsSporadic (↥(L i) ⧸ center ↥(L i)) s) : False := by
  obtain ⟨hTp, hLc⟩ := hch.comp i him
  obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem i hi him
  obtain ⟨hincl, -⟩ := hch.incl i hi him
  have hLq : CFSG.IsQuasisimple ↥(L i) := hLc.isQuasisimple
  have hPq : CFSG.IsQuasisimple ↥(L (i - 1)) := hLp.isQuasisimple
  have hLL : InL (L i) := chain_inL hch hT hi him
  have hLne : L i ≠ N := inL_ne_of_fStarSimple hN hLL
  have hLk : InL (L (i - 1)) := by
    rcases Nat.eq_zero_or_pos (i - 1) with h | h
    · rw [h]; exact hL0
    · exact chain_inL hch hT h (by omega)
  have hne : L (i - 1) ≠ L i := fun h => by
    have := hch.inj (i - 1) (by omega) i him h
    omega
  have hreachP := hreach (i - 1) (by omega)
  by_cases hsp' : ∃ s' ∈ S ++ Up, IsSporadic (↥(L (i - 1)) ⧸ center ↥(L (i - 1))) s'
  · obtain ⟨s', hs', hsc⟩ := hsp'
    rcases List.mem_append.1 hs' with hS | hU
    · exact false_of_link5b ih hUp hN hidx hkp hLL hLq hLne hPq hne
        (List.mem_append_left _ (List.mem_append_left _ hS)) hsc (rc.fi23 s' hs')
        (rc.evenOut s' hS) hLc hs2 hLp hincl h5b
    · exact hUp _ hLk s' hU hsc
  · obtain ⟨-, hPQ, -, -, -⟩ := link5b_setup hPq hne hLc hs2 hLp hincl h5b
    obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩, π, hπ, hπk,
        hπc⟩ :=
      link5b_section hN hidx hkp hLq hLne hPq hne hLc hs2 hLp hincl h5b
    have hRP' : R (↥P' ⧸ center ↥P') := rc.iso _ _ e hreachP.1
    have hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P' ⧸ center ↥P') s := by
      rintro ⟨s', hs', ⟨f⟩⟩
      exact hsp' ⟨s', hs', ⟨e.trans f⟩⟩
    have hlow : Odd (Nat.card ↥(center ↥P')) → ¬ ∃ s ∈ Lo, IsSporadic (↥P' ⧸ center ↥P') s := by
      rintro hodd' ⟨s'', hs'', hsc⟩
      exact false_of_odd_standard ih hsecY hcard hFS hidx' hkp' hsol hq' hodd'
        (List.mem_append_right _ hs'') hsc (rc.fi23_lo s'' hs'')
    obtain ⟨s', hs', ⟨f⟩⟩ := hLo
    have hNs : IsSporadic ↥N' s' := ⟨g.symm.trans f⟩
    obtain ⟨⟨X, _, hXK, hcq⟩, hodd'⟩ :=
      hpair s' hs' Y (ih.uHered.of_section hsecY) N' P' hFS hidx' hkp' hNs hsol hq' hRP' hns hlow
    have : Group.IsPerfect ↥(L (i - 1)) := hPq.1
    have hkodd : Odd (Nat.card π.ker) := hodd.of_dvd_nat (card_ker_dvd_center hPQ π hπc)
    have hoddP : Odd (Nat.card ↥(center ↥(L (i - 1)))) := by
      rw [card_center_eq_of_cover π hπ hπk]
      exact hkodd.mul hodd'
    obtain ⟨f'⟩ := hcq
    obtain ⟨e₁⟩ := cqEquiv_of_cover π hπ hπk
    have hevenP : Even (Nat.card ↥(center ↥(L (i - 1)))) :=
      even_center_of_reached rc hKeven hK₁L.isQuasisimple hK₁ hPq hreachP hXK ⟨e₁.trans f'⟩
    exact (Nat.not_even_iff_odd.2 hoddP) hevenP

theorem no_lo_odd_above (c : DescCtx H N IsK S Up Lo R) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) (hR : R (↥K₁ ⧸ center ↥K₁)) (hpair : LoPair IsK S Up Lo R)
    (hKeven : KEven IsK) :
    ∀ A, ReflTransGen Lt K₁ A → cqCard K₁ < cqCard A → Odd (Nat.card ↥(center ↥A)) →
      (∃ s ∈ Lo, IsSporadic (↥A ⧸ center ↥A) s) → False := by
  intro A hKA
  induction hKA with
  | refl => exact fun h => absurd h (lt_irrefl _)
  | tail hKB hBA ihB =>
    rename_i B A
    intro hlt hodd hLo
    by_cases hBA' : B = A
    · subst hBA'
      exact ihB hlt hodd hLo
    have hRB := reach_reflTransGen c.junction c.ih c.hUp c.rc c.hN c.hidx c.hkp hK₁L hK₁ hKB hR
    obtain ⟨m, L, T, s, hm, hch, h0, hT, -⟩ :=
      c.junction c.hkp N c.hN B A (lt_inL_left hBA) (lt_inL_right hBA) hBA hBA'
        (c.rc.not_exc _ hRB.1).1 (c.rc.not_exc _ hRB.1).2
    have hL0 : InL (L 0) := by rw [h0]; exact lt_inL_left hBA
    have hRL := reach_chain c.ih c.hUp c.rc c.hN c.hidx c.hkp hch hT hL0 hK₁L hK₁
      (by rw [h0]; exact hRB)
    have hlast : L m = A := hch.last
    have key := chain_down (m := m)
      (fun i => Odd (Nat.card ↥(center ↥(L i))) ∧
        (∃ s ∈ Lo, IsSporadic (↥(L i) ⧸ center ↥(L i)) s) ∧ cqCard K₁ < cqCard (L i))
      (by rw [hlast]; exact ⟨hodd, hLo, hlt⟩) (by
        intro i hi him hΦ
        obtain ⟨hodd', hLo', hlt'⟩ := hΦ
        rcases hch.link i hi him with h5a | h5b
        · obtain ⟨π, hπ, hk⟩ := chain_link5a_cover hch hi him h5a
          have hperf : Group.IsPerfect ↥(L i) := (hch.comp i him).2.isQuasisimple.1
          obtain ⟨e⟩ := h5a.2
          refine ⟨odd_card_center_of_cover π hπ hk hodd', ?_, ?_⟩
          · obtain ⟨s', hs', ⟨f⟩⟩ := hLo'
            exact ⟨s', hs', ⟨e.symm.trans f⟩⟩
          · have := cqCard_eq_of_cover hperf π hπ hk
            omega
        · exact (false_of_lo_link5b c.ih c.hUp c.rc hpair hKeven c.hN c.hidx c.hkp hK₁L hK₁ hch
            hT hL0 hRL hi him h5b hodd' hLo').elim) 0 (Nat.zero_le _)
    rw [h0] at key
    exact ihB key.2.2 key.1 key.2.1

theorem typeL_of_reach (c : DescCtx H N IsK S Up Lo R) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) (hR : R (↥K₁ ⧸ center ↥K₁)) {L₀ : Subgroup H} (hL₀ : InL L₀)
    (hL₀t : ∃ s ∈ S, OddCover s L₀) :
    ∀ A, ReflTransGen Lt K₁ A → cqCard K₁ < cqCard A → ∃ s ∈ S, OddCover s A := by
  have hK₁' := hK₁
  obtain ⟨X, _, σ, hσ, hσk, hXK⟩ := hK₁'
  have : Group.IsPerfect ↥K₁ := hK₁L.isQuasisimple.1
  have hKX : Nonempty ((↥K₁ ⧸ center ↥K₁) ≃* (X ⧸ center X)) := cqEquiv_of_cover σ hσ hσk
  intro A
  induction' hd : Nat.card H - cqCard A using Nat.strong_induction_on with d ihd generalizing A
  intro hKA hlt
  have hAL : InL A := by
    rcases hKA.cases_tail with h | ⟨B, -, hBA⟩
    · rw [h]; exact hK₁L
    · exact lt_inL_right hBA
  by_cases hmax : Maximal A
  · have hLo : Odd (Nat.card ↥(center ↥A)) → ¬ ∃ s ∈ Lo, IsSporadic (↥A ⧸ center ↥A) s := by
      rcases c.rc.lo with hcq | ⟨hpair, hKeven⟩
      · rintro - ⟨s', hs', ⟨f⟩⟩
        obtain ⟨e⟩ := hcq s' hs' (↥A ⧸ center ↥A) X ⟨f⟩ hXK
        obtain ⟨e₀⟩ := hKX
        have : cqCard A = cqCard K₁ := Nat.card_congr (e.trans e₀.symm).toEquiv
        omega
      · rintro hodd ⟨s', hs', hsp⟩
        exact no_lo_odd_above c hK₁L hK₁ hR hpair hKeven A hKA hlt hodd ⟨s', hs', hsp⟩
    have hev : KEven IsK → ∀ (X' : Type) [Group X'], IsK X' →
        Nonempty ((↥A ⧸ center ↥A) ≃* (X' ⧸ center X')) → Odd (Nat.card ↥(center ↥A)) →
          HasEvenCover ↥N := by
      intro _ X' _ hX' hcq _
      exfalso
      obtain ⟨e⟩ := hcq
      obtain ⟨e₂⟩ := c.rc.K_cq X X' hXK hX'
      obtain ⟨e₀⟩ := hKX
      have : cqCard A = cqCard K₁ := Nat.card_congr (e.trans (e₂.symm.trans e₀.symm)).toEquiv
      omega
    have hscope : ClosureScope IsK N A := Or.inr (Or.inr fun X' _ hX' hcq => by
      obtain ⟨e⟩ := hcq
      obtain ⟨e₂⟩ := c.rc.K_cq X X' hXK hX'
      obtain ⟨e₀⟩ := hKX
      have : cqCard A = cqCard K₁ := Nat.card_congr (e.trans (e₂.symm.trans e₀.symm)).toEquiv
      omega)
    exact maximal_isTypeL c.thm22.at c.ih.uHered c.hUp c.rc c.hN c.hidx c.hkp hL₀ hL₀t hmax
      (reach_reflTransGen c.junction c.ih c.hUp c.rc c.hN c.hidx c.hkp hK₁L hK₁ hKA hR).1 hLo hev
      hscope
  · have hex : ∃ Y, TransGen Lt A Y ∧ ¬ Nonempty ((↥A ⧸ center ↥A) ≃* (↥Y ⧸ center ↥Y)) := by
      by_contra hcon
      push Not at hcon
      exact hmax ⟨hAL, hcon⟩
    obtain ⟨Y, hAY, hnot⟩ := hex
    have hKY : ReflTransGen Lt K₁ Y := hKA.trans hAY.to_reflTransGen
    obtain ⟨hle, hcov⟩ := reach_data c.junction c.hkp c.hN hAY.to_reflTransGen (fun B hB =>
      c.rc.not_exc _ (reach_reflTransGen c.junction c.ih c.hUp c.rc c.hN c.hidx c.hkp hK₁L hK₁
        (hKA.trans hB) hR).1)
    have hne : cqCard A ≠ cqCard Y := by
      intro heq
      obtain ⟨π, hπ, hk⟩ := hcov heq
      have : Group.IsPerfect ↥Y := (inL_of_transGen hAY).isQuasisimple.1
      obtain ⟨e⟩ := cqEquiv_of_cover π hπ hk
      exact hnot ⟨e.symm⟩
    have hltY : cqCard A < cqCard Y := lt_of_le_of_ne hle hne
    have hYH := cqCard_le_card Y
    have hTY := ihd (Nat.card H - cqCard Y) (by omega) Y rfl hKY (by omega)
    exact typeL_of_transGen c.junction c.ih c.hUp c.rc c.hKiso c.hN c.hidx c.hkp hK₁L hK₁ hR hAY
      hKA hlt hTY

end CFSG.EvenSporadicStandard.Induction.Hyp
