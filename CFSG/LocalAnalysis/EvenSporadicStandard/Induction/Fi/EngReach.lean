module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Mono
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.Eng

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def KEven (IsK : GroupClass) : Prop :=
  ∀ (X : Type) [Group X], IsK X → Even (Nat.card (center X))

@[expose] def HasEvenCover (N' : Type) [Group N'] : Prop :=
  ∃ (Q₀ : Type) (_ : Group Q₀), CFSG.IsQuasisimple Q₀ ∧ Even (Nat.card (center Q₀)) ∧
    Nonempty ((Q₀ ⧸ center Q₀) ≃* N')

@[expose] def LoCq (IsK : GroupClass) (Lo : List TauCeti.SporadicName) : Prop :=
  ∀ s ∈ Lo, ∀ (X Y : Type) [Group X] [Group Y], IsSporadic X s → IsK Y →
    Nonempty (X ≃* (Y ⧸ center Y))

@[expose] def LoPair (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) (R : GroupClass) :
    Prop :=
  ∀ s ∈ Lo, ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → ∀ (N' P' : Subgroup Y),
    FStarSimple N' → N'.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
    IsSporadic ↥N' s → SolStd P' → CFSG.IsQuasisimple ↥P' → R (↥P' ⧸ center ↥P') →
    (¬ ∃ s' ∈ S ++ Up, IsSporadic (↥P' ⧸ center ↥P') s') →
    (Odd (Nat.card ↥(center ↥P')) → ¬ ∃ s' ∈ Lo, IsSporadic (↥P' ⧸ center ↥P') s') →
      (∃ (X : Type) (_ : Group X), IsK X ∧
        Nonempty ((↥P' ⧸ center ↥P') ≃* (X ⧸ center X))) ∧ Odd (Nat.card ↥(center ↥P'))

structure ReachRow (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) (R : GroupClass) :
    Prop where
  iso : R.IsoInv
  fi23_lo : ∀ s ∈ Lo, Fi23Excl s
  K_reach : ∀ (X : Type) [Group X], IsK X → R (X ⧸ center X)
  K_quot : ∀ (X : Type) [Group X], IsK X → IsK (X ⧸ CFSG.oddCore X)
  K_not_sporadic : ∀ (X : Type) [Group X], IsK X → ∀ s ∈ S ++ Up,
    ¬ IsSporadic (X ⧸ center X) s
  K_odd_lo : ∀ (X : Type) [Group X], IsK X → Odd (Nat.card (center X)) → ∀ s ∈ Lo,
    ¬ IsSporadic (X ⧸ center X) s
  lo : LoCq IsK Lo ∨ (LoPair IsK S Up Lo R ∧ KEven IsK)
  K_iso : ∀ (X Y : Type) [Group X] [Group Y], IsK X → IsK Y → CFSG.oddCore X = ⊥ →
    CFSG.oddCore Y = ⊥ → Nonempty (X ≃* Y)
  K_cq : ∀ (X Y : Type) [Group X] [Group Y], IsK X → IsK Y →
    Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y))
  not_exc : ∀ (X : Type) [Group X], R X → NotExc X
  sp_not_exc : ∀ s ∈ S ++ Up, SporadicNotExc s
  rank : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → R (X ⧸ center X) →
    (Odd (Nat.card (center X)) → ¬ ∃ s ∈ S ++ Up, IsSporadic (X ⧸ center X) s) →
    3 ≤ CFSG.pRank 2 X
  up_reach : ∀ s ∈ Up, ∀ (X : Type) [Group X], IsSporadic X s → R X
  closure : ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → ∀ (N' : Subgroup Y),
    FStarSimple N' → N'.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
      ∀ P : Subgroup Y, SolStd P → CFSG.IsQuasisimple ↥P → R (↥P ⧸ center ↥P) →
        (¬ ∃ s ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s) →
        (Odd (Nat.card ↥(center ↥P)) → ¬ ∃ s ∈ Lo, IsSporadic (↥P ⧸ center ↥P) s) →
        (KEven IsK → ∀ (X : Type) [Group X], IsK X →
          Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
            HasEvenCover ↥N') → R ↥N'
  pair_into : ∀ (Y : Type) [Group Y] [Finite Y], Balance.UHered Y → ∀ (N' : Subgroup Y),
    FStarSimple N' → N'.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y →
      ∀ P : Subgroup Y, SolStd P → CFSG.IsQuasisimple ↥P → R (↥P ⧸ center ↥P) →
        (¬ ∃ s ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s) →
        (Odd (Nat.card ↥(center ↥P)) → ¬ ∃ s ∈ Lo, IsSporadic (↥P ⧸ center ↥P) s) →
        (KEven IsK → ∀ (X : Type) [Group X], IsK X →
          Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P)) →
            HasEvenCover ↥N') →
        (∃ s ∈ S, IsSporadic ↥N' s) → IsK (↥P ⧸ CFSG.oddCore ↥P)

structure ReachFacts (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) (R : GroupClass) :
    Prop extends ReachRow IsK S Up Lo R where
  evenOut : ∀ s ∈ S, EvenCoverOutHered Up s

@[expose] def NoLink5bOut (S Up : List TauCeti.SporadicName) (H : Type) [Group H] [Finite H] :
    Prop :=
  ∀ {P Q T : Subgroup H} {s : H}, InL P → P ≠ Q → T ≠ ⊥ → Sol78Link5bData P Q T s →
    (∃ s' ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s') → False

structure UpCtx (S Up : List TauCeti.SporadicName) (H : Type) [Group H] [Finite H] : Prop where
  nu : NoUp Up H
  out : NoLink5bOut S Up H

@[expose] def Link5bLeaf (S Up : List TauCeti.SporadicName) (R : GroupClass) (H : Type) [Group H]
    [Finite H] : Prop :=
  ∀ {P Q T : Subgroup H} {s : H}, InL P → P ≠ Q → T ≠ ⊥ → Sol78Link5bData P Q T s →
    (∃ s' ∈ S ++ Up, IsSporadic (↥P ⧸ center ↥P) s') → R (↥Q ⧸ center ↥Q)

theorem UpCtx.leaf {S Up : List TauCeti.SporadicName} {R : GroupClass} {H : Type} [Group H]
    [Finite H] (hUp : UpCtx S Up H) : Link5bLeaf S Up R H :=
  fun hP hne hT hd hsp => (hUp.out hP hne hT hd hsp).elim

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {IsK : GroupClass}
  {S Up Lo : List TauCeti.SporadicName} {R : GroupClass}

@[expose] def Reached (R : GroupClass) (K₁ A : Subgroup H) : Prop :=
  R (↥A ⧸ center ↥A) ∧ cqCard K₁ ≤ cqCard A ∧
    (cqCard K₁ = cqCard A → ∃ π : ↥A →* ↥K₁, Function.Surjective π ∧ π.ker ≤ center ↥A)

omit [Finite H] in
theorem Reached.refl {K₁ : Subgroup H} (hR : R (↥K₁ ⧸ center ↥K₁)) : Reached R K₁ K₁ :=
  ⟨hR, le_rfl, fun _ => ⟨MonoidHom.id _, Function.surjective_id, by simp⟩⟩

omit [Finite H] in
theorem chain_inL {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) {i : ℕ}
    (hi : 1 ≤ i) (him : i ≤ m) : InL (L i) :=
  ⟨T i, hT i hi him, (hch.comp i him).1, (hch.comp i him).2⟩

omit [Finite H] in
theorem card_ker_dvd_center {P Q : Subgroup H} (hPQ : P ≤ Q) {P' : Type*} [Group P']
    (π : ↥P →* P') (hπc : ∀ x ∈ π.ker, ((x : ↥P) : H) ∈ centralizer (Q : Set H)) :
    Nat.card π.ker ∣ Nat.card (center ↥Q) := by
  let κ : ↥π.ker →* ↥(center ↥Q) := MonoidHom.mk' (fun x =>
    ⟨⟨((x : ↥P) : H), hPQ x.1.2⟩, by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 (hπc x x.2) g g.2)⟩) (fun x y => rfl)
  have hκ : Function.Injective κ := fun x y h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(center ↥Q) => ((z : ↥Q) : H)) h
  exact Subgroup.card_dvd_of_injective κ hκ

theorem even_center_of_klike {K₁ : Subgroup H} (hK₁q : CFSG.IsQuasisimple ↥K₁)
    (hK₁ : KLike IsK K₁) (hKeven : KEven IsK) : Even (Nat.card ↥(center ↥K₁)) := by
  obtain ⟨Y₀, _, σ, hσ, hσk, hY₀⟩ := hK₁
  have : Group.IsPerfect ↥K₁ := hK₁q.1
  exact even_card_center_of_cover σ hσ hσk (hKeven Y₀ hY₀)

theorem even_center_of_reached (rc : ReachFacts IsK S Up Lo R) (hKeven : KEven IsK)
    {K₁ P : Subgroup H} (hK₁q : CFSG.IsQuasisimple ↥K₁) (hK₁ : KLike IsK K₁)
    (hPq : CFSG.IsQuasisimple ↥P) (hreach : Reached R K₁ P) {X : Type} [Group X] (hXK : IsK X)
    (hcq : Nonempty ((↥P ⧸ center ↥P) ≃* (X ⧸ center X))) :
    Even (Nat.card ↥(center ↥P)) := by
  have hKev := even_center_of_klike hK₁q hK₁ hKeven
  obtain ⟨Y₀, _, σ, hσ, hσk, hY₀⟩ := hK₁
  have : Group.IsPerfect ↥K₁ := hK₁q.1
  obtain ⟨e₁⟩ := cqEquiv_of_cover σ hσ hσk
  obtain ⟨e₂⟩ := rc.K_cq Y₀ X hY₀ hXK
  obtain ⟨e₃⟩ := hcq
  have heq : cqCard K₁ = cqCard P := Nat.card_congr (e₁.trans (e₂.trans e₃.symm)).toEquiv
  obtain ⟨ρ, hρ, hρk⟩ := hreach.2.2 heq
  have : Group.IsPerfect ↥P := hPq.1
  exact even_card_center_of_cover ρ hρ hρk hKev

theorem hasEvenCover_of_section (rc : ReachFacts IsK S Up Lo R) (hKeven : KEven IsK)
    {K₁ P Q : Subgroup H} (hK₁q : CFSG.IsQuasisimple ↥K₁) (hK₁ : KLike IsK K₁)
    (hPq : CFSG.IsQuasisimple ↥P) (hQq : CFSG.IsQuasisimple ↥Q) (hPQ : P ≤ Q)
    (hreach : Reached R K₁ P) {P' N' : Type} [Group P'] [Group N'] (π : ↥P →* P')
    (hπ : Function.Surjective π) (hπk : π.ker ≤ center ↥P)
    (hπc : ∀ x ∈ π.ker, ((x : ↥P) : H) ∈ centralizer (Q : Set H))
    (g : (↥Q ⧸ center ↥Q) ≃* N') {X : Type} [Group X] (hXK : IsK X)
    (hcq : Nonempty ((P' ⧸ center P') ≃* (X ⧸ center X))) (hodd : Odd (Nat.card (center P'))) :
    HasEvenCover N' := by
  have : Group.IsPerfect ↥P := hPq.1
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hπk
  obtain ⟨f⟩ := hcq
  have hPev : Even (Nat.card ↥(center ↥P)) :=
    even_center_of_reached rc hKeven hK₁q hK₁ hPq hreach hXK ⟨e.trans f⟩
  have hprod := card_center_eq_of_cover π hπ hπk
  have hkev : Even (Nat.card π.ker) := by
    by_contra hne
    have hko : Odd (Nat.card π.ker) := Nat.not_even_iff_odd.1 hne
    have : Odd (Nat.card ↥(center ↥P)) := by
      rw [hprod]
      exact hko.mul hodd
    exact (Nat.not_even_iff_odd.2 this) hPev
  have hdvd := card_ker_dvd_center hPQ π hπc
  have hQev : Even (Nat.card ↥(center ↥Q)) :=
    even_iff_two_dvd.2 ((even_iff_two_dvd.1 hkev).trans hdvd)
  exact ⟨↥Q, inferInstance, hQq, hQev, ⟨g⟩⟩

theorem reached_succ {M : Subgroup H} {m : ℕ} {L T : ℕ → Subgroup H} {s : ℕ → H}
    (hch : Sol78Chain23 H M m L T s) {K₁ : Subgroup H} {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (hP : Reached R K₁ (L (i - 1))) (hR : R (↥(L i) ⧸ center ↥(L i))) : Reached R K₁ (L i) := by
  have h1 : cqCard (L (i - 1)) ≤ cqCard (L i) := chain_link_le hch hi him
  have h2 := hP.2.1
  refine ⟨hR, h2.trans h1, fun heq => ?_⟩
  obtain ⟨ρ, hρ, hρk⟩ := hP.2.2 (by omega)
  obtain ⟨π, hπ, hπk⟩ := chain_link_cover hch hi him (by omega)
  have : Group.IsPerfect ↥(L i) := (hch.comp i him).2.isQuasisimple.1
  exact ⟨ρ.comp π, hρ.comp hπ, cover_comp π ρ hπk hρk⟩

theorem reach_chain_gen (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H)
    (hleaf : Link5bLeaf S Up R H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {M : Subgroup H} {m : ℕ}
    {L T : ℕ → Subgroup H} {s : ℕ → H} (hch : Sol78Chain23 H M m L T s)
    (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) (hL0 : InL (L 0)) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) (h0 : Reached R K₁ (L 0)) : ∀ i, i ≤ m → Reached R K₁ (L i) := by
  intro i
  induction i with
  | zero => exact fun _ => h0
  | succ k ihk =>
    intro hk
    have hk' := ihk (by omega)
    have hLq : CFSG.IsQuasisimple ↥(L (k + 1)) := (hch.comp (k + 1) hk).2.isQuasisimple
    have hLL : InL (L (k + 1)) := chain_inL hch hT (by omega) hk
    have hLne : L (k + 1) ≠ N := inL_ne_of_fStarSimple hN hLL
    have hLk : InL (L k) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h]; exact hL0
      · exact chain_inL hch hT h (by omega)
    refine reached_succ hch (by omega) hk hk' ?_
    rcases hch.link (k + 1) (by omega) hk with h5a | h5b
    · obtain ⟨e⟩ := h5a.2
      exact rc.iso _ _ e.symm hk'.1
    · obtain ⟨hsp, hsN, hs2, hLp⟩ := hch.elem (k + 1) (by omega) hk
      obtain ⟨hincl, -⟩ := hch.incl (k + 1) (by omega) hk
      have hPq : CFSG.IsQuasisimple ↥(L k) := hLp.isQuasisimple
      have hne : L k ≠ L (k + 1) := fun h => by
        have := hch.inj k (by omega) (k + 1) hk h
        omega
      by_cases hsp' : ∃ s' ∈ S ++ Up, IsSporadic (↥(L k) ⧸ center ↥(L k)) s'
      · exact hleaf hLk hne (hT (k + 1) (by omega) hk)
          (chain_link5bData hch (by omega) hk h5b) hsp'
      · obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩, π, hπ, hπk,
          hπc⟩ :=
          link5b_section hN hidx hkp hLq hLne hPq hne (hch.comp (k + 1) hk).2 hs2 hLp hincl h5b
        obtain ⟨-, hPQ, -, -, -⟩ :=
          link5b_setup hPq hne (hch.comp (k + 1) hk).2 hs2 hLp hincl h5b
        have hRP : R (↥P' ⧸ center ↥P') := rc.iso _ _ e hk'.1
        have hns : ¬ ∃ s ∈ S ++ Up, IsSporadic (↥P' ⧸ center ↥P') s := by
          rintro ⟨s', hs', ⟨f⟩⟩
          exact hsp' ⟨s', hs', ⟨e.trans f⟩⟩
        have hlow : Odd (Nat.card ↥(center ↥P')) → ¬ ∃ s ∈ Lo, IsSporadic (↥P' ⧸ center ↥P') s := by
          rintro hodd ⟨s'', hs'', hsc⟩
          exact false_of_odd_standard ih hsecY hcard hFS hidx' hkp' hsol hq' hodd
            (List.mem_append_right _ hs'') hsc (rc.fi23_lo s'' hs'')
        have hev : KEven IsK → ∀ (X : Type) [Group X], IsK X →
            Nonempty ((↥P' ⧸ center ↥P') ≃* (X ⧸ center X)) → Odd (Nat.card ↥(center ↥P')) →
              HasEvenCover ↥N' := fun hKeven X _ hXK hcq hodd =>
          hasEvenCover_of_section rc hKeven hK₁L.isQuasisimple hK₁ hPq hLq hPQ hk' π hπ hπk hπc g
            hXK hcq hodd
        exact rc.iso _ _ g.symm (rc.closure Y (ih.uHered.of_section hsecY) N' hFS hidx' hkp' P'
          hsol hq' hRP hns hlow hev)

theorem reach_chain (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hUp : UpCtx S Up H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {M : Subgroup H} {m : ℕ}
    {L T : ℕ → Subgroup H} {s : ℕ → H} (hch : Sol78Chain23 H M m L T s)
    (hT : ∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) (hL0 : InL (L 0)) {K₁ : Subgroup H} (hK₁L : InL K₁)
    (hK₁ : KLike IsK K₁) (h0 : Reached R K₁ (L 0)) : ∀ i, i ≤ m → Reached R K₁ (L i) :=
  reach_chain_gen ih hUp.leaf rc hN hidx hkp hch hT hL0 hK₁L hK₁ h0

theorem reach_step_gen (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hleaf : Link5bLeaf S Up R H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K₁ P Q : Subgroup H}
    (hK₁L : InL K₁) (hK₁ : KLike IsK K₁) (hP : Reached R K₁ P) (hLt : Lt P Q) :
    Reached R K₁ Q := by
  by_cases hPQ : P = Q
  · subst hPQ
    exact hP
  obtain ⟨m, L, T, s, -, hch, hL0, hT, -⟩ :=
    junction hkp N hN P Q (lt_inL_left hLt) (lt_inL_right hLt) hLt hPQ (rc.not_exc _ hP.1).1
      (rc.not_exc _ hP.1).2
  have hm := reach_chain_gen ih hleaf rc hN hidx hkp hch hT
    (by rw [hL0]; exact lt_inL_left hLt) hK₁L hK₁ (by rw [hL0]; exact hP) m le_rfl
  rw [hch.last] at hm
  exact hm

theorem reach_reflTransGen_gen (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hleaf : Link5bLeaf S Up R H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K A : Subgroup H} (hKL : InL K)
    (hK : KLike IsK K) (h : ReflTransGen Lt K A) (h0 : R (↥K ⧸ center ↥K)) :
    Reached R K A := by
  induction h with
  | refl => exact Reached.refl h0
  | tail _ hlt ihr => exact reach_step_gen junction ih hleaf rc hN hidx hkp hKL hK ihr hlt

theorem reach_reflTransGen (junction : JunctionStmtAt H)
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hUp : UpCtx S Up H)
    (rc : ReachFacts IsK S Up Lo R) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) {K A : Subgroup H} (hKL : InL K)
    (hK : KLike IsK K) (h : ReflTransGen Lt K A) (h0 : R (↥K ⧸ center ↥K)) :
    Reached R K A :=
  reach_reflTransGen_gen junction ih hUp.leaf rc hN hidx hkp hKL hK h h0

end CFSG.EvenSporadicStandard.Induction.Fi.Eng
