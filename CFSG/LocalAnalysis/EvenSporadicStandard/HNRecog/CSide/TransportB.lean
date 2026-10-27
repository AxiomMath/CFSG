module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Transport0

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog.Swap

theorem cSideOrbits_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (hq : ∀ u, q' (a u) = q u)
    (h : CSideOrbits q σ) : CSideOrbits q' σ' := by
  unfold CSideOrbits at h ⊢
  obtain ⟨O, hcover, hdisj, hinv, htrans, hcard0, hcard1⟩ := h
  refine ⟨fun i => a '' O i, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v'
    have hsymm : q' v' = q (a.symm v') := by
      rw [← hq (a.symm v'), LinearEquiv.apply_symm_apply]
    constructor
    · rintro ⟨hv'ne, hv'q⟩
      have hsne : a.symm v' ≠ 0 := fun h0 =>
        hv'ne (by rw [← LinearEquiv.apply_symm_apply a v', h0, LinearEquiv.map_zero])
      have hsq : q (a.symm v') = 0 := by rw [← hsymm, hv'q]
      obtain ⟨i, hi⟩ := (hcover (a.symm v')).mp ⟨hsne, hsq⟩
      exact ⟨i, a.symm v', hi, LinearEquiv.apply_symm_apply a v'⟩
    · rintro ⟨i, u, hu, rfl⟩
      obtain ⟨hune, huq⟩ := (hcover u).mpr ⟨i, hu⟩
      refine ⟨?_, ?_⟩
      · intro h0
        exact hune (a.injective (by rw [h0, LinearEquiv.map_zero]))
      · rw [hq u, huq]
  · intro i j hij
    refine Set.disjoint_left.mpr fun v' hv'i hv'j => ?_
    obtain ⟨u, hu, hui⟩ := hv'i
    obtain ⟨w, hw, hwj⟩ := hv'j
    have hwu : w = u := a.injective (hwj.trans hui.symm)
    exact (Set.disjoint_left.mp (hdisj i j hij) hu) (hwu ▸ hw)
  · intro i g' v' hv'
    obtain ⟨v, hv, hav⟩ := hv'
    refine ⟨σ (ψ.symm g') v, hinv i (ψ.symm g') v hv, ?_⟩
    rw [← hav, hψ (ψ.symm g') v, MulEquiv.apply_symm_apply]
  · intro i v' hv' w' hw'
    obtain ⟨v, hv, hav⟩ := hv'
    obtain ⟨w, hw, haw⟩ := hw'
    obtain ⟨g, hg⟩ := htrans i v hv w hw
    refine ⟨ψ g, ?_⟩
    rw [← hav, ← haw, ← hψ g v, hg]
  · rw [Nat.card_image_of_injective a.injective (O 0), hcard0]
  · rw [Nat.card_image_of_injective a.injective (O 1), hcard1]

theorem cSideOmega_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (hq : ∀ u, q' (a u) = q u)
    (h : CSideOmega q σ) : CSideOmega q' σ' := by
  unfold CSideOmega at h ⊢
  obtain ⟨ω, hcomm, hquad, hswap⟩ := h
  refine ⟨Swap.transport a ω, ?_, ?_, ?_⟩
  · intro g'
    ext v'
    have hσ : a.symm (σ' g' v') = σ (ψ.symm g') (a.symm v') := by
      have hh := hψ (ψ.symm g') (a.symm v')
      rw [MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at hh
      rw [← hh, LinearEquiv.symm_apply_apply]
    have hmul : ω (σ (ψ.symm g') (a.symm v')) = σ (ψ.symm g') (ω (a.symm v')) := by
      rw [← LinearEquiv.mul_apply, hcomm (ψ.symm g'), LinearEquiv.mul_apply]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Swap.transport_apply,
      Swap.transport_apply, hσ, hmul, hψ (ψ.symm g') (ω (a.symm v')),
      MulEquiv.apply_symm_apply]
  · intro v'
    have h0 : a (ω (ω (a.symm v')) + ω (a.symm v') + a.symm v') = 0 := by
      rw [hquad (a.symm v'), LinearEquiv.map_zero]
    have h1 : a (ω (ω (a.symm v')) + ω (a.symm v') + a.symm v') =
        a (ω (ω (a.symm v'))) + a (ω (a.symm v')) + v' := by
      rw [LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.apply_symm_apply]
    simp only [Swap.transport_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
    rw [← h1, h0]
  · intro b' hb' v'
    have hb : cSideFreeSwap q σ (Swap.transport a.symm b') :=
      cSideFreeSwap_transport a ψ hψ hq hb'
    have hw := hswap (Swap.transport a.symm b') hb (a.symm v')
    simp only [Swap.transport_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply] at hw
    simpa only [Swap.transport_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply] using congrArg a hw

end CFSG.EvenSporadicStandard.HNRecog.CSide
