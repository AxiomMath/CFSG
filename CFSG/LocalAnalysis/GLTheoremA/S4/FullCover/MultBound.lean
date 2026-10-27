module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Defs
public import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def ListedMultiplierBoundAt (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  (k2 p i ∨ k3 p i) →
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ π : Q →* i.Group, Function.Surjective π → π.ker = Subgroup.center Q →
    IsPGroup p (Subgroup.center Q) → Subgroup.center Q ≠ ⊥ →
      p = 3 ∧ Nat.card (Subgroup.center Q) = 3 ∧ CoverListed i

@[expose] def HatOddMultiplierBoundAt (i : TauCeti.CFSGIndex) : Prop :=
  (k2HatIndex 3 i ∨ k3HatIndex 3 i) →
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ π : Q →* i.Group, Function.Surjective π → π.ker = Subgroup.center Q →
      Odd (Nat.card (Subgroup.center Q)) → Nat.card (Subgroup.center Q) ∣ 3

theorem listedMultiplierBound_of_forall {p : ℕ} (h : ∀ i, ListedMultiplierBoundAt p i) :
    ListedMultiplierBound p := h

theorem hatOddMultiplierBound_of_forall (h : ∀ i, HatOddMultiplierBoundAt i) :
    HatOddMultiplierBound := h

theorem card_center_dvd_hopfMultiplier_of_cover {Q S : Type} [Group Q] [Finite Q] [Group S]
    (hQ : CFSG.Open.IsQuasisimple Q) (π : Q →* S) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center Q) :
    Nat.card (Subgroup.center Q) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) := by
  have h := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier (Group.isPerfect_def.2 hQ.1) π hπ
    hker.le
  rwa [hker] at h

theorem pGroup_card_of_dvd {p m : ℕ} (hp : p.Prime) {Z : Type} [Group Z] [Finite Z]
    (hZ : IsPGroup p Z) (hne : Nontrivial Z) (hd : Nat.card Z ∣ m) :
    p ∣ m ∧ (¬ p ^ 2 ∣ m → Nat.card Z = p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hn
    have := Nat.card_eq_one_iff_unique.1 hn
    exact (not_nontrivial_iff_subsingleton.2 this.1) hne
  rw [hn] at hd
  refine ⟨(dvd_pow_self p (by omega)).trans hd, fun h2 => ?_⟩
  have : n ≤ 1 := by
    by_contra hgt
    exact h2 ((pow_dvd_pow p (by omega : 2 ≤ n)).trans hd)
  rw [hn, show n = 1 by omega, pow_one]

end CFSG.LocalAnalysis.GLTheoremA
