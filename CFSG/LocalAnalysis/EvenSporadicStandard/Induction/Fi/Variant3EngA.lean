module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Reach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

@[expose] def RV3 : GroupClass := fun X _ => IsSporadic X .Fi23 ∨ IsSporadic X .Fi24Prime

theorem rv3_iso : RV3.IsoInv := by
  intro X Y _ _ e h
  rcases h with h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.symm.trans f⟩

theorem notExc_of_rv3 (pf : FiPinned) {X : Type} [Group X] (h : RV3 X) : NotExc X := by
  rcases h with h | h
  · exact pf.notExc23 X h
  · exact pf.notExc24 X h

theorem fi24_of_link5b (pf : FiPinned) (ih : BelowSec (Sol78PredS fiTypes) H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {P Q : Subgroup H}
    (hQq : CFSG.IsQuasisimple ↥Q) (hQne : Q ≠ N) (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q)
    {T : Subgroup H} {s : H} (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s)
    (hP : IsSporadic (↥P ⧸ center ↥P) .Fi23) : IsSporadic (↥Q ⧸ center ↥Q) .Fi24Prime := by
  obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩, -⟩ :=
    link5b_section hN hidx hkp hQq hQne hPq hPne hQc hsT hPc hincl h5b
  obtain ⟨f⟩ := hP
  have hcq : IsSporadic (↥P' ⧸ center ↥P') .Fi23 := ⟨e.symm.trans f⟩
  have hodd : Odd (Nat.card ↥(center ↥P')) := by
    rw [pf.mult23 ↥P' hq' hcq, Subgroup.card_bot]
    exact odd_one
  obtain ⟨-, ⟨f'⟩⟩ := ih.apply hsecY hcard N' hFS hidx' hkp' P' hsol
    ⟨.Fi23, by simp [fiTypes], ⟨hq', hodd, hcq⟩⟩
  exact ⟨g.trans f'⟩

theorem reachV3_chain (pf : FiPinned) (ih : BelowSec (Sol78PredS fiTypes) H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {M : Subgroup H} {m : ℕ}
    {L T : ℕ → Subgroup H} {s : ℕ → H} (hch : Sol78Chain23 H M m L T s)
    (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) {K₁ : Subgroup H} (h0 : Reached RV3 K₁ (L 0)) :
    ∀ i, i ≤ m → Reached RV3 K₁ (L i) := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ k ihk =>
    intro hk
    have hk' := ihk (by omega)
    have hLq : CFSG.IsQuasisimple ↥(L (k + 1)) := (hch.comp (k + 1) hk).2.isQuasisimple
    have hLL : InL (L (k + 1)) := chain_inL hch hT (by omega) hk
    have hLne : L (k + 1) ≠ N := inL_ne_of_fStarSimple hN hLL
    refine reached_succ hch (by omega) hk hk' ?_
    rcases hch.link (k + 1) (by omega) hk with h5a | h5b
    · obtain ⟨e⟩ := h5a.2
      exact rv3_iso _ _ e.symm hk'.1
    · obtain ⟨-, -, hs2, hLp⟩ := hch.elem (k + 1) (by omega) hk
      obtain ⟨hincl, -⟩ := hch.incl (k + 1) (by omega) hk
      have hPq : CFSG.IsQuasisimple ↥(L k) := hLp.isQuasisimple
      have hne : L k ≠ L (k + 1) := fun h => by
        have := hch.inj k (by omega) (k + 1) hk h
        omega
      rcases hk'.1 with h23 | h24
      · exact Or.inr (fi24_of_link5b pf ih hN hidx hkp hLq hLne hPq hne
          (hch.comp (k + 1) hk).2 hs2 hLp hincl h5b h23)
      · exact (false_of_link5b ih noUp_nil hN hidx hkp hLL hLq hLne hPq hne
          (by simp [fiTypes]) h24 pf.excl24 (fiEvenOut_fi24 pf []) (hch.comp (k + 1) hk).2 hs2
          hLp hincl h5b).elim

theorem reachV3_step (pf : FiPinned) (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K₁ P Q : Subgroup H}
    (hP : Reached RV3 K₁ P) (hLt : Lt P Q) : Reached RV3 K₁ Q := by
  by_cases hPQ : P = Q
  · subst hPQ
    exact hP
  obtain ⟨m, L, T, s, -, hch, hL0, hT, -⟩ :=
    junction hkp N hN P Q (lt_inL_left hLt) (lt_inL_right hLt) hLt hPQ
      (notExc_of_rv3 pf hP.1).1 (notExc_of_rv3 pf hP.1).2
  have hm := reachV3_chain pf ih hN hidx hkp hch hT (by rw [hL0]; exact hP) m le_rfl
  rw [hch.last] at hm
  exact hm

theorem reachV3_reflTransGen (pf : FiPinned) (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K A : Subgroup H}
    (h : ReflTransGen Lt K A) (h0 : RV3 (↥K ⧸ center ↥K)) : Reached RV3 K A := by
  induction h with
  | refl => exact Reached.refl h0
  | tail _ hlt ihr => exact reachV3_step pf junction ih hN hidx hkp ihr hlt

omit [Finite H] in
theorem klike_isSporadic_cq {K₁ : Subgroup H} (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : KLike IsKFi23 K₁) : IsSporadic (↥K₁ ⧸ center ↥K₁) .Fi23 := by
  obtain ⟨Y, _, σ, hσ, hσk, -, -, ⟨f⟩⟩ := hK
  have : Group.IsPerfect ↥K₁ := hq.1
  obtain ⟨e⟩ := cqEquiv_of_cover σ hσ hσk
  exact ⟨e.trans f⟩

theorem isKFi23_quot_of_klike {K₁ : Subgroup H} (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : KLike IsKFi23 K₁) : IsKFi23 (↥K₁ ⧸ CFSG.oddCore ↥K₁) := by
  have hcq := klike_isSporadic_cq hq hK
  have : Group.IsPerfect ↥K₁ := hq.1
  have hker : (QuotientGroup.mk' (CFSG.oddCore ↥K₁)).ker ≤ center ↥K₁ := by
    rw [QuotientGroup.ker_mk']
    exact oddCore_le_center hq
  obtain ⟨e⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
    (QuotientGroup.mk'_surjective _) hker
  obtain ⟨f⟩ := hcq
  exact ⟨inferInstance, isQuasisimple_of_cover hq _ (QuotientGroup.mk'_surjective _) hker,
    ⟨e.symm.trans f⟩⟩

theorem desc_v3 (pf : FiPinned) (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS fiTypes) H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K₁ L₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsKFi23 K₁) (hL₁L : InL L₁) (h : ReflTransGen Lt K₁ L₁) :
    (∃ π : ↥L₁ →* ↥K₁, Function.Surjective π ∧ π.ker ≤ center ↥L₁) ∨
      (IsLS [.Fi24Prime] ↥L₁ ∧ IsKFi23 (↥K₁ ⧸ CFSG.oddCore ↥K₁)) := by
  have hq₁ : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
  have hcq := klike_isSporadic_cq hq₁ hK₁
  have hreach := reachV3_reflTransGen pf junction ih hN hidx hkp h (Or.inl hcq)
  by_cases heq : cqCard K₁ = cqCard L₁
  · exact Or.inl (hreach.2.2 heq)
  · right
    have hq₂ : CFSG.IsQuasisimple ↥L₁ := hL₁L.isQuasisimple
    rcases hreach.1 with h23 | hsp
    · exfalso
      obtain ⟨f⟩ := h23
      obtain ⟨g⟩ := hcq
      exact heq (Nat.card_congr (g.trans f.symm).toEquiv)
    · exact ⟨⟨.Fi24Prime, by simp, hq₂, pf.mult24 ↥L₁ hq₂ hsp, hsp⟩,
        isKFi23_quot_of_klike hq₁ hK₁⟩

end CFSG.EvenSporadicStandard.Induction.Fi.V3
