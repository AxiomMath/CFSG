module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Transport0

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

private theorem cSide_transport_fixed_iff {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (g' : A5 × A5) (u : V) :
    σ (ψ.symm g') u = u ↔ σ' g' (a u) = a u := by
  have h := hψ (ψ.symm g') u
  rw [MulEquiv.apply_symm_apply] at h
  constructor
  · intro hu
    rw [← h, hu]
  · intro hu
    exact a.injective (by rw [h]; exact hu)

private theorem cSide_card_fixed_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (g' : A5 × A5) :
    Nat.card {v' : V' // σ' g' v' = v'} = Nat.card {v : V // σ (ψ.symm g') v = v} := by
  have e : {v : V // σ (ψ.symm g') v = v} ≃ {v' : V' // σ' g' v' = v'} :=
    Equiv.subtypeEquiv a.toEquiv (fun u => cSide_transport_fixed_iff a ψ hψ g' u)
  exact (Nat.card_congr e).symm

private theorem cSide_polar_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} (a : V ≃ₗ[ZMod 2] V') (hq : ∀ u, q' (a u) = q u)
    (u w : V) : QuadraticMap.polar q' (a u) (a w) = QuadraticMap.polar q u w := by
  have h : QuadraticMap.polar q' (a u) (a w) = q (u + w) - q u - q w := by
    unfold QuadraticMap.polar
    rw [← map_add, hq (u + w), hq u, hq w]
  rw [h]
  rfl

theorem cSideFixedZero_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (h : CSideFixedZero σ) : CSideFixedZero σ' := by
  intro g' hord htriv v' hv'
  have hord' : orderOf (ψ.symm g') = 3 ∨ orderOf (ψ.symm g') = 5 := by
    have hordψ : orderOf (ψ.symm g') = orderOf g' := by
      rw [← MulEquiv.orderOf_eq ψ (ψ.symm g'), MulEquiv.apply_symm_apply]
    rw [hordψ]
    exact hord
  have htriv' : (ψ.symm g').1 = 1 ∨ (ψ.symm g').2 = 1 :=
    (cSide_psi_trivial_iff ψ.symm g').mp htriv
  have hfix : σ (ψ.symm g') (a.symm v') = a.symm v' :=
    (cSide_transport_fixed_iff a ψ hψ g' (a.symm v')).mpr (by simpa using hv')
  have h0 : a.symm v' = 0 := h (ψ.symm g') hord' htriv' (a.symm v') hfix
  have ha0 : a (a.symm v') = a 0 := congrArg a h0
  simpa using ha0

theorem cSideThreeBoth_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (hq : ∀ u, q' (a u) = q u)
    (h : CSideThreeBoth q σ) : CSideThreeBoth q' σ' := by
  intro g' hord h1 h2
  have hord' : orderOf (ψ.symm g') = 3 := by
    have hordψ : orderOf (ψ.symm g') = orderOf g' := by
      rw [← MulEquiv.orderOf_eq ψ (ψ.symm g'), MulEquiv.apply_symm_apply]
    rw [hordψ]
    exact hord
  have hnt' : (ψ.symm g').1 ≠ 1 ∧ (ψ.symm g').2 ≠ 1 :=
    (cSide_psi_nontrivial_iff ψ.symm g').mp (⟨h1, h2⟩ : g'.1 ≠ 1 ∧ g'.2 ≠ 1)
  obtain ⟨hcard, hnd, hplane⟩ := h (ψ.symm g') hord' hnt'.1 hnt'.2
  refine ⟨?_, ?_, ?_⟩
  · rw [cSide_card_fixed_transport a ψ hψ g']
    exact hcard
  · intro v' hv' hv'0
    have hu_fix : σ (ψ.symm g') (a.symm v') = a.symm v' :=
      (cSide_transport_fixed_iff a ψ hψ g' (a.symm v')).mpr (by simpa using hv')
    have hu_ne : a.symm v' ≠ 0 := by
      intro h0
      exact hv'0 (by simpa using congrArg a h0)
    obtain ⟨w, hw_fix, hw_polar⟩ := hnd (a.symm v') hu_fix hu_ne
    refine ⟨a w, (cSide_transport_fixed_iff a ψ hψ g' w).mp hw_fix, ?_⟩
    have hp : QuadraticMap.polar q' v' (a w) = QuadraticMap.polar q (a.symm v') w := by
      simpa using cSide_polar_transport a hq (a.symm v') w
    rw [hp]
    exact hw_polar
  · obtain ⟨v, w, hv, hw, hv0, hw0, hvw, hvq, hwq, hpvw⟩ := hplane
    refine ⟨a v, a w, (cSide_transport_fixed_iff a ψ hψ g' v).mp hv,
      (cSide_transport_fixed_iff a ψ hψ g' w).mp hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => hv0 (a.injective (by simpa using h))
    · exact fun h => hw0 (a.injective (by simpa using h))
    · exact fun h => hvw (a.injective h)
    · rw [hq v]
      exact hvq
    · rw [hq w]
      exact hwq
    · rw [cSide_polar_transport a hq v w]
      exact hpvw

theorem cSideInvol_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (h : CSideInvol σ) : CSideInvol σ' := by
  intro g' hne hsq
  have hne' : ψ.symm g' ≠ 1 := by
    intro h1
    exact hne (by simpa using congrArg ψ h1)
  have hsq' : (ψ.symm g') ^ 2 = 1 := by
    have h2 := congrArg ψ.symm hsq
    simpa using h2
  rw [cSide_card_fixed_transport a ψ hψ g']
  exact h (ψ.symm g') hne' hsq'

end CFSG.EvenSporadicStandard.HNRecog.CSide
