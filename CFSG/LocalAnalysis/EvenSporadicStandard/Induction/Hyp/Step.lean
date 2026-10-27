module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Link
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.PredS
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EvenCoverOutHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {A Up : List TauCeti.SporadicName}

@[expose] def Fi23Excl (s' : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X], IsSporadic X .Fi23 → ¬ IsSporadic (X ⧸ center X) s'

@[expose] def EvenCoverOut (Up : List TauCeti.SporadicName) (s' : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → ∀ L' : Subgroup Y, SolStd L' →
      CFSG.IsQuasisimple ↥L' → IsSporadic (↥L' ⧸ center ↥L') s' →
        ¬ Odd (Nat.card ↥(center ↥L')) → ∃ s'' ∈ Up, IsSporadic ↥N' s''

@[expose] def NoUp (Up : List TauCeti.SporadicName) (H : Type) [Group H] : Prop :=
  ∀ Q : Subgroup H, InL Q → ∀ s'' ∈ Up, ¬ IsSporadic (↥Q ⧸ center ↥Q) s''

omit [Finite H] in
theorem noUp_nil : NoUp [] H := fun _ _ _ h => absurd h List.not_mem_nil

@[expose] def NotExc (X : Type) [Group X] : Prop :=
  ¬ Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
    ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel X .PSL 2 p f

@[expose] def SporadicNotExc (s' : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X], IsSporadic X s' → NotExc X

@[expose] def JunctionStmtAt (H : Type) [Group H] [Finite H] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H), FStarSimple N → ∀ K M : Subgroup H,
    InL K → InL M → Lt K M → K ≠ M →
      ¬ Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 2 p f) →
        ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), 1 ≤ m ∧ Sol78Chain23 H M m L T s ∧
          L 0 = K ∧ (∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) ∧
          (K ≤ M → ∀ i, 1 ≤ i → i ≤ m → L i ≤ M)

theorem false_of_odd_standard (ih : BelowSec (Sol78PredS A) H) {Y : Type} [Group Y]
    [Finite Y] (hsec : CFSG.SignalizerFunctorTheorem.IsSectionOf Y H)
    (hcard : Nat.card Y < Nat.card H) {N' P' : Subgroup Y} (hFS : FStarSimple N')
    (hidx' : N'.index ≤ 2) (hkp' : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y)
    (hsol : SolStd P') (hq' : CFSG.IsQuasisimple ↥P') (hodd : Odd (Nat.card ↥(center ↥P')))
    {s' : TauCeti.SporadicName} (hs' : s' ∈ A) (hcq : IsSporadic (↥P' ⧸ center ↥P') s')
    (hFi : Fi23Excl s') : False := by
  obtain ⟨hF23, -⟩ := ih.apply hsec hcard N' hFS hidx' hkp' P' hsol ⟨s', hs', ⟨hq', hodd, hcq⟩⟩
  exact hFi ↥P' hF23 hcq

theorem false_of_link5b (ih : BelowSec (Sol78PredS A) H) (hUp : NoUp Up H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {P Q : Subgroup H} (hQL : InL Q) (hQq : CFSG.IsQuasisimple ↥Q) (hQne : Q ≠ N)
    (hPq : CFSG.IsQuasisimple ↥P) (hPne : P ≠ Q)
    {s' : TauCeti.SporadicName} (hS : s' ∈ A) (hs' : IsSporadic (↥P ⧸ center ↥P) s')
    (hFi : Fi23Excl s') (hEven : EvenCoverOutHered Up s')
    {T : Subgroup H} {s : H} (hQc : IsCompIn Q (centralizer (T : Set H))) (hsT : s ^ 2 ∈ T)
    (hPc : IsCompIn P (centralizer ((T ⊔ zpowers s : Subgroup H) : Set H)))
    (hincl : P ≤ Q ⊔ Q.map (MulAut.conj s).toMonoidHom) (h5b : Sol78Link5b Q P s) : False := by
  obtain ⟨Y, _, _, N', P', hcard, hsec, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩, -⟩ :=
    link5b_section hN hidx hkp hQq hQne hPq hPne hQc hsT hPc hincl h5b
  obtain ⟨f⟩ := hs'
  have hcq : IsSporadic (↥P' ⧸ center ↥P') s' := ⟨e.symm.trans f⟩
  by_cases hodd : Odd (Nat.card ↥(center ↥P'))
  · exact (false_of_odd_standard ih hsec hcard hFS hidx' hkp' hsol hq' hodd hS hcq hFi).elim
  · obtain ⟨s'', hs'', ⟨g'⟩⟩ :=
      hEven Y (ih.uHered.of_section hsec) N' hFS hidx' hkp' P' hsol hq' hcq hodd
    exact hUp Q hQL s'' hs'' ⟨g.trans g'⟩

omit [Finite H] in
theorem lt_inL_left {P Q : Subgroup H} (h : Lt P Q) : InL P := by
  obtain ⟨S₁, T₁, hS₁, -, hS₁p, -, -, hP, -, -⟩ := h
  exact ⟨S₁, hS₁, hS₁p, hP⟩

omit [Finite H] in
theorem lt_inL_right {P Q : Subgroup H} (h : Lt P Q) : InL Q := by
  obtain ⟨S₁, T₁, -, hT₁, -, hT₁p, -, -, hQ, -⟩ := h
  exact ⟨T₁, hT₁, hT₁p, hQ⟩

theorem inL_ne_of_fStarSimple (hN : FStarSimple N) {Q : Subgroup H} (hQ : InL Q) : Q ≠ N := by
  rintro rfl
  obtain ⟨T', hT', -, hc⟩ := hQ
  exact hT' (eq_bot_of_isCompIn_fStarSimple hN hc)

theorem central_type_chain (ih : BelowSec (Sol78PredS A) H) (hUp : NoUp Up H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {M : Subgroup H} {m : ℕ}
    {L T : ℕ → Subgroup H} {s : ℕ → H} (hch : Sol78Chain23 H M m L T s)
    (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) {s' : TauCeti.SporadicName} (hS : s' ∈ A)
    (hFi : Fi23Excl s') (hEven : EvenCoverOutHered Up s')
    (h0 : IsSporadic (↥(L 0) ⧸ center ↥(L 0)) s') :
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
    have hLne : L (k + 1) ≠ N := inL_ne_of_fStarSimple hN hLL
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
      exact (false_of_link5b ih hUp hN hidx hkp hLL hLq hLne hPq hne hS hk' hFi hEven
        (hch.comp (k + 1) hk).2 hs2 hLp hincl h5b).elim

theorem central_type_step (junction : JunctionStmtAt H) (ih : BelowSec (Sol78PredS A) H)
    (hUp : NoUp Up H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {P Q : Subgroup H}
    {s' : TauCeti.SporadicName} (hS : s' ∈ A)
    (hs' : IsSporadic (↥P ⧸ center ↥P) s') (hFi : Fi23Excl s') (hEven : EvenCoverOutHered Up s')
    (hsexc : SporadicNotExc s') (hLt : Lt P Q) :
    Nonempty ((↥Q ⧸ center ↥Q) ≃* (↥P ⧸ center ↥P)) := by
  by_cases hPQ : P = Q
  · subst hPQ
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨m, L, T, s, -, hch, h0, hT, -⟩ :=
    junction hkp N hN P Q (lt_inL_left hLt) (lt_inL_right hLt) hLt hPQ (hsexc _ hs').1
      (hsexc _ hs').2
  have h0' : IsSporadic (↥(L 0) ⧸ center ↥(L 0)) s' := by
    rw [h0]
    exact hs'
  have hm := central_type_chain ih hUp hN hidx hkp hch hT hS hFi hEven h0' m le_rfl
  rw [hch.last] at hm
  obtain ⟨f₁⟩ := hm
  obtain ⟨f₂⟩ := hs'
  exact ⟨f₁.trans f₂.symm⟩

theorem maximal_of_central_type (junction : JunctionStmtAt H) (ih : BelowSec (Sol78PredS A) H)
    (hUp : NoUp Up H) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {L₁ : Subgroup H} (hL₁ : InL L₁)
    {s' : TauCeti.SporadicName} (hS : s' ∈ A)
    (hs' : IsSporadic (↥L₁ ⧸ center ↥L₁) s') (hFi : Fi23Excl s') (hEven : EvenCoverOutHered Up s')
    (hsexc : SporadicNotExc s') : Maximal L₁ := by
  refine ⟨hL₁, fun M hM => ?_⟩
  have key : IsSporadic (↥M ⧸ center ↥M) s' := by
    induction hM with
    | single hlt =>
      obtain ⟨e⟩ := central_type_step junction ih hUp hN hidx hkp hS hs' hFi hEven hsexc hlt
      obtain ⟨f⟩ := hs'
      exact ⟨e.trans f⟩
    | tail _ hlt ih' =>
      obtain ⟨e⟩ := central_type_step junction ih hUp hN hidx hkp hS ih' hFi hEven hsexc hlt
      obtain ⟨f⟩ := ih'
      exact ⟨e.trans f⟩
  obtain ⟨f₁⟩ := hs'
  obtain ⟨f₂⟩ := key
  exact ⟨f₁.trans f₂.symm⟩

end CFSG.EvenSporadicStandard.Induction.Hyp
