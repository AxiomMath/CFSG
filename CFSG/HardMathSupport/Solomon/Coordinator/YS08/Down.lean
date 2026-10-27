module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Simple
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.ChevTwo

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def SporL3Down (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
    ∀ J : Subgroup S, GLAPComponent 3 (Lemma510Ns.fixSub β) J → ∀ p : ℕ, ¬ IsL3Kind p (barOf 3 J)

@[expose] def LieL3Down : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ J : Subgroup S, GLAPComponent 3 (Lemma510Ns.fixSub β) J →
      ∀ p : ℕ, p.Prime → IsL3Kind p (barOf 3 J) → lieIndexChar idx.1 = p

theorem isChevIndexOfChar_of_lieIndexChar_eq {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : lieIndexChar d = p) : IsChevIndexOfChar p d := by
  cases d with
  | A r q =>
    match r with
    | 0 => exact h
    | 1 => exact Or.inl h
    | r + 2 => exact h
  | twistedA r q =>
    match r with
    | 0 => exact h
    | 1 => exact h
    | 2 => exact Or.inl h
    | r + 3 => exact h
  | _ => exact h

theorem isCharTwoLieIndex_of_lieIndexChar_eq {d : TauCeti.LieTypeIndex} (h : lieIndexChar d = 2) :
    IsCharTwoLieIndex d := by
  cases d <;> simp_all [lieIndexChar, IsCharTwoLieIndex]

theorem l3EpsSporBranch_of_down {s : TauCeti.SporadicName} (h : SporL3Down s) :
    L3EpsSporBranch s := by
  intro Y _ _ hY he α hα J hJ p hSL
  obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := component_to_simple hα hJ
  exact h (Y ⧸ Subgroup.center Y) hY.2
    (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY) he β hβ J' hJ'
    p (isL3Kind_of_central_quotient hSL ψ hψ hψk)

theorem l34SporBranch_of_down {s : TauCeti.SporadicName} (h : SporL3Down s) : L34SporBranch s := by
  intro Y _ _ hY _ he α hα J hJ hL34
  obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := component_to_simple hα hJ
  exact h (Y ⧸ Subgroup.center Y) hY.2
    (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY) he β hβ J' hJ'
    2 (isL3Kind_of_isLThreeFour (isLThreeFour_of_central_quotient hL34 ψ hψ hψk))

theorem l3EpsLieBranch_of_down (h : LieL3Down) : L3EpsLieBranch := by
  intro Y _ _ hY idx he α hα J hJ p hp hSL
  obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := component_to_simple hα hJ
  exact isChevIndexOfChar_of_lieIndexChar_eq
    (h (Y ⧸ Subgroup.center Y) hY.2
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY) idx he β hβ J'
      hJ' p hp (isL3Kind_of_central_quotient hSL ψ hψ hψk))

theorem l34LieBranch_of_down (h : LieL3Down) : L34LieBranch := by
  intro Y _ _ hY _ idx he α hα J hJ hL34
  obtain ⟨β, J', hβ, hJ', ψ, hψ, hψk⟩ := component_to_simple hα hJ
  exact isCharTwoLieIndex_of_lieIndexChar_eq
    (h (Y ⧸ Subgroup.center Y) hY.2
      (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY) idx he β hβ J'
      hJ' 2 Nat.prime_two
      (isL3Kind_of_isLThreeFour (isLThreeFour_of_central_quotient hL34 ψ hψ hψk)))

@[expose] def SporL3DownInner (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) → ∀ x : S, x ^ 3 = 1 →
    ∀ J : Subgroup S, GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J →
      ∀ p : ℕ, ¬ IsL3Kind p (barOf 3 J)

theorem sporL3Down_of_inner {s : TauCeti.SporadicName}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (h : SporL3DownInner s) : SporL3Down s := by
  intro S _ _ hs hnab he β hβ J hJ p
  have hOut' := hOut S hs hnab s he
  have hmk : (QuotientGroup.mk β : CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 1 := by
    have h3 : (QuotientGroup.mk β : CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hβ]; rfl
    have hd3 := orderOf_dvd_of_pow_eq_one h3
    have hle : orderOf (QuotientGroup.mk β : CFSG.ComponentClassification.OuterAutomorphisms.Outer S) ≤
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) :=
      Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)
    have hcard := hle.trans hOut'
    rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h3'
    · exact orderOf_eq_one_iff.1 h1
    · omega
  obtain ⟨a, rfl⟩ : ∃ a : S, MulAut.conj a = β := (QuotientGroup.eq_one_iff β).1 hmk
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨u, v, huv⟩ := hnab
      exact huv ((Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top v)) u)
  have ha3 : a ^ 3 = 1 := by
    have : MulAut.conj (a ^ 3) = 1 := by rw [map_pow, hβ]
    have hc : a ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut S => φ g) this
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hfix : Lemma510Ns.fixSub (MulAut.conj a) = Subgroup.centralizer ({a} : Set S) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    show MulAut.conj a y = y ↔ y * a = a * y
    rw [MulAut.conj_apply]
    constructor
    · intro hy
      exact (mul_inv_eq_iff_eq_mul.1 hy).symm
    · intro hy
      rw [← hy]
      group
  rw [hfix] at hJ
  exact h S hs hnab he a ha3 J hJ p

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
