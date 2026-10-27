module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Transport
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog.Swap

private lemma cSideT0_fst_of_preserves {ψ : A5 × A5 ≃* A5 × A5} (h : PreservesFactorsAut ψ)
    (h' : PreservesFactorsAut ψ.symm) (g : A5 × A5) : g.2 = 1 ↔ (ψ g).2 = 1 := by
  constructor
  · intro hg
    obtain ⟨x', hx'⟩ := h.1 g.1
    rw [show g = (g.1, 1) from Prod.ext rfl hg, hx']
  · intro hg
    obtain ⟨x', hx'⟩ := h'.1 (ψ g).1
    have hgg : g = (x', 1) := by
      have hh := congrArg ψ.symm (show ψ g = ((ψ g).1, 1) from Prod.ext rfl hg)
      rw [MulEquiv.symm_apply_apply] at hh
      exact hh.trans hx'
    rw [hgg]

private lemma cSideT0_snd_of_preserves {ψ : A5 × A5 ≃* A5 × A5} (h : PreservesFactorsAut ψ)
    (h' : PreservesFactorsAut ψ.symm) (g : A5 × A5) : g.1 = 1 ↔ (ψ g).1 = 1 := by
  constructor
  · intro hg
    obtain ⟨y', hy'⟩ := h.2 g.2
    rw [show g = (1, g.2) from Prod.ext hg rfl, hy']
  · intro hg
    obtain ⟨y', hy'⟩ := h'.2 (ψ g).2
    have hgg : g = (1, y') := by
      have hh := congrArg ψ.symm (show ψ g = (1, (ψ g).2) from Prod.ext hg rfl)
      rw [MulEquiv.symm_apply_apply] at hh
      exact hh.trans hy'
    rw [hgg]

private lemma cSideT0_fst_of_swaps {ψ : A5 × A5 ≃* A5 × A5} (h : SwapsFactorsAut ψ)
    (h' : SwapsFactorsAut ψ.symm) (g : A5 × A5) : g.2 = 1 ↔ (ψ g).1 = 1 := by
  constructor
  · intro hg
    obtain ⟨y', hy'⟩ := h.1 g.1
    rw [show g = (g.1, 1) from Prod.ext rfl hg, hy']
  · intro hg
    obtain ⟨x', hx'⟩ := h'.2 (ψ g).2
    have hgg : g = (x', 1) := by
      have hh := congrArg ψ.symm (show ψ g = (1, (ψ g).2) from Prod.ext hg rfl)
      rw [MulEquiv.symm_apply_apply] at hh
      exact hh.trans hx'
    rw [hgg]

private lemma cSideT0_snd_of_swaps {ψ : A5 × A5 ≃* A5 × A5} (h : SwapsFactorsAut ψ)
    (h' : SwapsFactorsAut ψ.symm) (g : A5 × A5) : g.1 = 1 ↔ (ψ g).2 = 1 := by
  constructor
  · intro hg
    obtain ⟨x', hx'⟩ := h.2 g.2
    rw [show g = (1, g.2) from Prod.ext hg rfl, hx']
  · intro hg
    obtain ⟨y', hy'⟩ := h'.1 (ψ g).1
    have hgg : g = (1, y') := by
      have hh := congrArg ψ.symm (show ψ g = ((ψ g).1, 1) from Prod.ext rfl hg)
      rw [MulEquiv.symm_apply_apply] at hh
      exact hh.trans hy'
    rw [hgg]

theorem cSide_psi_trivial_iff (ψ : A5 × A5 ≃* A5 × A5) (g : A5 × A5) :
    (g.1 = 1 ∨ g.2 = 1) ↔ ((ψ g).1 = 1 ∨ (ψ g).2 = 1) := by
  rcases exists_preserves_or_swaps ψ with ⟨hp, hp'⟩ | ⟨hs, hs'⟩
  · rw [cSideT0_snd_of_preserves hp hp' g, cSideT0_fst_of_preserves hp hp' g]
  · rw [cSideT0_snd_of_swaps hs hs' g, cSideT0_fst_of_swaps hs hs' g, or_comm]

theorem cSide_psi_nontrivial_iff (ψ : A5 × A5 ≃* A5 × A5) (g : A5 × A5) :
    (g.1 ≠ 1 ∧ g.2 ≠ 1) ↔ ((ψ g).1 ≠ 1 ∧ (ψ g).2 ≠ 1) := by
  have h := not_congr (cSide_psi_trivial_iff ψ g)
  simpa only [ne_eq, not_or] using h

private lemma cSideT0_sandwich_apply {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V']
    {b' : V' ≃ₗ[ZMod 2] V'} {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} {g h : A5 × A5}
    (hb : b' * σ' g * b'.symm = σ' h) (w : V') : b' (σ' g (b'.symm w)) = σ' h w := by
  have hh := congrArg (fun f : V' ≃ₗ[ZMod 2] V' => f w) hb
  simpa only [LinearEquiv.mul_apply] using hh

theorem cSideFreeSwap_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (hq : ∀ u, q' (a u) = q u)
    {b' : V' ≃ₗ[ZMod 2] V'} (hb' : cSideFreeSwap q' σ' b') :
    cSideFreeSwap q σ (Swap.transport a.symm b') := by
  obtain ⟨hb'1, hb'iso, hb'swap, hb'rank⟩ := hb'
  have hb'swap_s : (∀ x : A5, ∃ y : A5, b' * σ' (x, 1) * b'.symm = σ' (1, y)) ∧
      (∀ y : A5, ∃ x : A5, b' * σ' (1, y) * b'.symm = σ' (x, 1)) := hb'swap
  set B : V ≃ₗ[ZMod 2] V := Swap.transport a.symm b' with hB
  have hb_apply : ∀ w : V, B w = a.symm (b' (a w)) := by
    intro w
    rw [hB, Swap.transport_apply, LinearEquiv.symm_symm]
  have hb_symm_apply : ∀ w : V, B.symm w = a.symm (b'.symm (a w)) := by
    intro w
    have hbw : B (a.symm (b'.symm (a w))) = w := by
      simp only [hb_apply, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
    have hh := congrArg B.symm hbw
    simpa using hh.symm
  have hconj_apply : ∀ (g : A5 × A5) (v : V),
      (B * σ g * B.symm) v = a.symm (b' (σ' (ψ g) (b'.symm (a v)))) := by
    intro g v
    simp only [LinearEquiv.mul_apply]
    rw [hb_symm_apply v, hb_apply, hψ g (a.symm (b'.symm (a v))),
      LinearEquiv.apply_symm_apply]
  have hsigma_apply : ∀ (g : A5 × A5) (v : V),
      a.symm (σ' (ψ g) (a v)) = σ g v := by
    intro g v
    rw [← hψ g v, LinearEquiv.symm_apply_apply]
  have hiso : ∀ v : V, q (B v) = q v := by
    intro v
    rw [hb_apply, ← hq (a.symm (b' (a v))), LinearEquiv.apply_symm_apply, hb'iso (a v),
      hq v]
  have hswap : SwapsFactors σ B := by
    change (∀ x : A5, ∃ y : A5, B * σ (x, 1) * B.symm = σ (1, y)) ∧
      (∀ y : A5, ∃ x : A5, B * σ (1, y) * B.symm = σ (x, 1))
    rcases exists_preserves_or_swaps ψ with ⟨hp, hp'⟩ | ⟨hs, hs'⟩
    · refine ⟨?_, ?_⟩
      · intro x
        obtain ⟨x', hx'⟩ := hp.1 x
        obtain ⟨y'', hy''⟩ := hb'swap_s.1 x'
        obtain ⟨y, hy⟩ := hp'.2 y''
        have hpsi : ψ (1, y) = (1, y'') := by
          have hh := congrArg ψ hy
          simpa using hh.symm
        refine ⟨y, ?_⟩
        ext v
        rw [hconj_apply (x, 1) v, hx', cSideT0_sandwich_apply hy'' (a v), ← hpsi,
          hsigma_apply (1, y) v]
      · intro y
        obtain ⟨y', hy'⟩ := hp.2 y
        obtain ⟨x'', hx''⟩ := hb'swap_s.2 y'
        obtain ⟨x, hx⟩ := hp'.1 x''
        have hpsi : ψ (x, 1) = (x'', 1) := by
          have hh := congrArg ψ hx
          simpa using hh.symm
        refine ⟨x, ?_⟩
        ext v
        rw [hconj_apply (1, y) v, hy', cSideT0_sandwich_apply hx'' (a v), ← hpsi,
          hsigma_apply (x, 1) v]
    · refine ⟨?_, ?_⟩
      · intro x
        obtain ⟨y', hy'⟩ := hs.1 x
        obtain ⟨x'', hx''⟩ := hb'swap_s.2 y'
        obtain ⟨y, hy⟩ := hs'.1 x''
        have hpsi : ψ (1, y) = (x'', 1) := by
          have hh := congrArg ψ hy
          simpa using hh.symm
        refine ⟨y, ?_⟩
        ext v
        rw [hconj_apply (x, 1) v, hy', cSideT0_sandwich_apply hx'' (a v), ← hpsi,
          hsigma_apply (1, y) v]
      · intro y
        obtain ⟨x', hx'⟩ := hs.2 y
        obtain ⟨y'', hy''⟩ := hb'swap_s.1 x'
        obtain ⟨x, hx⟩ := hs'.2 y''
        have hpsi : ψ (x, 1) = (1, y'') := by
          have hh := congrArg ψ hx
          simpa using hh.symm
        refine ⟨x, ?_⟩
        ext v
        rw [hconj_apply (1, y) v, hx', cSideT0_sandwich_apply hy'' (a v), ← hpsi,
          hsigma_apply (x, 1) v]
  refine ⟨?_, hiso, hswap, ?_⟩
  · rw [hB]
    exact Swap.transport_mul_self a.symm hb'1
  · rw [hB, Swap.finrank_range_transport a.symm b']
    exact hb'rank

end CFSG.EvenSporadicStandard.HNRecog.CSide
