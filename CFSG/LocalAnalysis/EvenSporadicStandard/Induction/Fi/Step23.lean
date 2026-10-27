module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Defs

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {S Up : List TauCeti.SporadicName}

theorem fiFalse_of_link5b (hsec : Link5bSection) (ih : BelowSec (Sol78PredS S) H)
    (hUp : FiNoUp Up H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {P Q : Subgroup H} (hQL : InL Q) (hQq : CFSG.IsQuasisimple ↥Q) (hQne : Q ≠ N)
    (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q)
    {s' : TauCeti.SporadicName} (hS : s' ∈ S) (hs' : IsSporadic (↥P ⧸ center ↥P) s')
    (hFi : Fi23Excl s' ∨ TauCeti.SporadicName.Fi24Prime ∈ Up)
    (hEven : EvenCoverOutHered Up s')
    {T : Subgroup H} {s : H} (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s) : False := by
  obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩⟩ :=
    hsec H N hN hidx hkp P Q hQq hQne hPq hPne T s hQc hsT hPc hincl h5b
  obtain ⟨f⟩ := hs'
  have hcq : IsSporadic (↥P' ⧸ center ↥P') s' := ⟨e.symm.trans f⟩
  by_cases hodd : Odd (Nat.card ↥(center ↥P'))
  · have hcov : OddCover s' P' := ⟨hq', hodd, hcq⟩
    obtain ⟨hF23, hN24⟩ := ih.apply hsecY hcard N' hFS hidx' hkp' P' hsol ⟨s', hS, hcov⟩
    rcases hFi with hFi | hFi24
    · exact hFi ↥P' hF23 hcq
    · obtain ⟨h24⟩ := hN24
      exact hUp Q hQL .Fi24Prime hFi24 ⟨g.trans h24⟩
  · obtain ⟨s'', hs'', ⟨g'⟩⟩ :=
      hEven Y (ih.uHered.of_section hsecY) N' hFS hidx' hkp' P' hsol hq' hcq hodd
    exact hUp Q hQL s'' hs'' ⟨g.trans g'⟩

theorem fiCentral_type_chain (hsec : Link5bSection) (ih : BelowSec (Sol78PredS S) H)
    (hUp : FiNoUp Up H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {M : Subgroup H} {m : ℕ}
    {L T : ℕ → Subgroup H} {s : ℕ → H} (hch : Sol78Chain23 H M m L T s)
    (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) {s' : TauCeti.SporadicName} (hS : s' ∈ S)
    (hFi : Fi23Excl s' ∨ TauCeti.SporadicName.Fi24Prime ∈ Up)
    (hEven : EvenCoverOutHered Up s') (h0 : IsSporadic (↥(L 0) ⧸ center ↥(L 0)) s') :
    ∀ i, i ≤ m → IsSporadic (↥(L i) ⧸ center ↥(L i)) s' := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ k ihk =>
    intro hk
    have hk' := ihk (by omega)
    have hLq : CFSG.IsQuasisimple ↥(L (k + 1)) := (hch.comp (k + 1) hk).2.isQuasisimple
    have hLL : InL (L (k + 1)) :=
      ⟨T (k + 1), hT (k + 1) (by omega) hk, (hch.comp (k + 1) hk).1, (hch.comp (k + 1) hk).2⟩
    have hLne : L (k + 1) ≠ N := inL_ne_of_fStarSimple' hN hLL
    rcases hch.link (k + 1) (by omega) hk with h5a | h5b
    · obtain ⟨e⟩ := h5a.2
      obtain ⟨f⟩ := hk'
      exact ⟨e.trans f⟩
    · obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem (k + 1) (by omega) hk
      obtain ⟨hincl, -⟩ := hch.incl (k + 1) (by omega) hk
      have hPq : CFSG.IsQuasisimple ↥(L k) := hLp.isQuasisimple
      have hne : L k ≠ L (k + 1) := fun h => by
        have := hch.inj k (by omega) (k + 1) hk h
        omega
      exact (fiFalse_of_link5b hsec ih hUp hN hidx hkp hLL hLq hLne hPq hne hS hk' hFi hEven
        (hch.comp (k + 1) hk).2 hs2 hLp hincl h5b).elim

theorem fiCentral_type_step (hsec : Link5bSection) (junction : Sol78JunctionAt H)
    (ih : BelowSec (Sol78PredS S) H) (hUp : FiNoUp Up H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {P Q : Subgroup H}
    {s' : TauCeti.SporadicName} (hS : s' ∈ S) (hs' : IsSporadic (↥P ⧸ center ↥P) s')
    (hFi : Fi23Excl s' ∨ TauCeti.SporadicName.Fi24Prime ∈ Up)
    (hEven : EvenCoverOutHered Up s') (hsexc : SporadicNotExc s') (hLt : Lt P Q) :
    Nonempty ((↥Q ⧸ center ↥Q) ≃* (↥P ⧸ center ↥P)) := by
  by_cases hPQ : P = Q
  · subst hPQ
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨m, L, T, s, -, hch, h0, hT, -⟩ :=
    junction hkp N hN P Q (lt_inL_left' hLt) (lt_inL_right' hLt) hLt hPQ (hsexc _ hs').1
      (hsexc _ hs').2
  have h0' : IsSporadic (↥(L 0) ⧸ center ↥(L 0)) s' := by
    rw [h0]
    exact hs'
  have hm := fiCentral_type_chain hsec ih hUp hN hidx hkp hch hT hS hFi hEven h0' m le_rfl
  rw [hch.last] at hm
  obtain ⟨f₁⟩ := hm
  obtain ⟨f₂⟩ := hs'
  exact ⟨f₁.trans f₂.symm⟩

theorem fiMaximal_of_central_type (hsec : Link5bSection) (junction : Sol78JunctionAt H)
    (ih : BelowSec (Sol78PredS S) H) (hUp : FiNoUp Up H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {L₁ : Subgroup H} (hL₁ : InL L₁) {s' : TauCeti.SporadicName} (hS : s' ∈ S)
    (hs' : IsSporadic (↥L₁ ⧸ center ↥L₁) s')
    (hFi : Fi23Excl s' ∨ TauCeti.SporadicName.Fi24Prime ∈ Up)
    (hEven : EvenCoverOutHered Up s') (hsexc : SporadicNotExc s') : Maximal L₁ := by
  refine ⟨hL₁, fun M hM => ?_⟩
  have key : IsSporadic (↥M ⧸ center ↥M) s' := by
    induction hM with
    | single hlt =>
      obtain ⟨e⟩ := fiCentral_type_step hsec junction ih hUp hN hidx hkp hS hs' hFi hEven hsexc hlt
      obtain ⟨f⟩ := hs'
      exact ⟨e.trans f⟩
    | tail _ hlt ih' =>
      obtain ⟨e⟩ := fiCentral_type_step hsec junction ih hUp hN hidx hkp hS ih' hFi hEven hsexc hlt
      obtain ⟨f⟩ := ih'
      exact ⟨e.trans f⟩
  obtain ⟨f₁⟩ := hs'
  obtain ⟨f₂⟩ := key
  exact ⟨f₁.trans f₂.symm⟩

end CFSG.EvenSporadicStandard.Induction.Fi
