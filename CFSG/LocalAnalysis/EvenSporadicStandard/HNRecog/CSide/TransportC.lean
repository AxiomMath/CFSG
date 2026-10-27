module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.Transport0

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf CFSG.EvenSporadicStandard.HNRecog.Swap

private lemma transportC_apply {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (b' : V' ≃ₗ[ZMod 2] V') (l g : A5 × A5) :
    ∀ v : V, a ((σ l * Swap.transport a.symm b' * σ g) v) =
      (σ' (ψ l) * b' * σ' (ψ g)) (a v) := by
  intro v
  calc a ((σ l * Swap.transport a.symm b' * σ g) v)
      = a (σ l ((Swap.transport a.symm b') (σ g v))) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = σ' (ψ l) (a ((Swap.transport a.symm b') (σ g v))) := hψ l _
    _ = σ' (ψ l) (a (a.symm (b' (a (σ g v))))) := by
        rw [Swap.transport_apply, LinearEquiv.symm_symm]
    _ = σ' (ψ l) (b' (a (σ g v))) := by rw [LinearEquiv.apply_symm_apply]
    _ = σ' (ψ l) (b' (σ' (ψ g) (a v))) := by rw [hψ g v]
    _ = (σ' (ψ l) * b' * σ' (ψ g)) (a v) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]

private lemma transportC_apply_snd {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (b' : V' ≃ₗ[ZMod 2] V') (p q : A5 × A5) :
    ∀ v : V, a ((σ p * (σ q * Swap.transport a.symm b')) v) =
      (σ' (ψ p) * (σ' (ψ q) * b')) (a v) := by
  intro v
  calc a ((σ p * (σ q * Swap.transport a.symm b')) v)
      = a (σ p (σ q ((Swap.transport a.symm b') v))) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = σ' (ψ p) (a (σ q ((Swap.transport a.symm b') v))) := hψ p _
    _ = σ' (ψ p) (σ' (ψ q) (a ((Swap.transport a.symm b') v))) := by rw [hψ q]
    _ = σ' (ψ p) (σ' (ψ q) (b' (a v))) := by
        rw [Swap.transport_apply, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
    _ = (σ' (ψ p) * (σ' (ψ q) * b')) (a v) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]

private lemma transportC_conj_iff {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (b' : V' ≃ₗ[ZMod 2] V') (g l : A5 × A5) :
    (σ l * Swap.transport a.symm b' * σ g = σ g * (σ l * Swap.transport a.symm b')) ↔
      (σ' (ψ l) * b' * σ' (ψ g) = σ' (ψ g) * (σ' (ψ l) * b')) := by
  have hfl := transportC_apply (σ := σ) (σ' := σ') a ψ hψ b' l g
  have hgl := transportC_apply_snd (σ := σ) (σ' := σ') a ψ hψ b' g l
  constructor
  · intro hEq
    ext w
    obtain ⟨v, rfl⟩ := a.surjective w
    rw [← hfl v, hEq, hgl v]
  · intro hEq
    ext v
    apply a.injective
    rw [hfl v, hgl v, hEq]

private lemma transportC_polar {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} (a : V ≃ₗ[ZMod 2] V') (hq : ∀ u, q' (a u) = q u) :
    ∀ x y : V, QuadraticMap.polar q' (a x) (a y) = QuadraticMap.polar q x y := by
  intro x y
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hq, hq, hq]

private lemma transportC_fixedNondeg {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} (a : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V)
    (f' : V' ≃ₗ[ZMod 2] V') (hpt : ∀ v, a (f v) = f' (a v))
    (hpol : ∀ x y : V, QuadraticMap.polar q' (a x) (a y) = QuadraticMap.polar q x y)
    (h : cSideFixedNondeg q f) : cSideFixedNondeg q' f' := by
  intro v' hv' hv'0
  let v : V := a.symm v'
  have hv : f v = v := by
    apply a.injective
    rw [hpt v, show a v = v' from LinearEquiv.apply_symm_apply a v', hv']
  have hv0 : v ≠ 0 := by
    intro h0
    apply hv'0
    calc v' = a v := (LinearEquiv.apply_symm_apply a v').symm
      _ = a 0 := by rw [h0]
      _ = 0 := map_zero a
  obtain ⟨w, hw, hwne⟩ := h v hv hv0
  refine ⟨a w, ?_, ?_⟩
  · rw [← hpt w, hw]
  · have hv'a : v' = a v := (LinearEquiv.apply_symm_apply a v').symm
    rw [hv'a, hpol v w]
    exact hwne

private lemma transportC_fixedPlane {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} (a : V ≃ₗ[ZMod 2] V') (f : V ≃ₗ[ZMod 2] V)
    (f' : V' ≃ₗ[ZMod 2] V') (hpt : ∀ v, a (f v) = f' (a v)) (hq : ∀ u, q' (a u) = q u)
    (hpol : ∀ x y : V, QuadraticMap.polar q' (a x) (a y) = QuadraticMap.polar q x y)
    (h : cSideFixedPlane q' f') : cSideFixedPlane q f := by
  obtain ⟨v', w', hv', hw', hv'0, hw'0, hvw', hqv', hqw', hpol'⟩ := h
  refine ⟨a.symm v', a.symm w', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply a.injective
    rw [hpt (a.symm v'), LinearEquiv.apply_symm_apply, hv']
  · apply a.injective
    rw [hpt (a.symm w'), LinearEquiv.apply_symm_apply, hw']
  · intro h0
    apply hv'0
    calc v' = a (a.symm v') := (LinearEquiv.apply_symm_apply a v').symm
      _ = a 0 := by rw [h0]
      _ = 0 := map_zero a
  · intro h0
    apply hw'0
    calc w' = a (a.symm w') := (LinearEquiv.apply_symm_apply a w').symm
      _ = a 0 := by rw [h0]
      _ = 0 := map_zero a
  · intro h
    exact hvw' (by simpa using congrArg a h)
  · rw [← hq (a.symm v'), LinearEquiv.apply_symm_apply]
    exact hqv'
  · rw [← hq (a.symm w'), LinearEquiv.apply_symm_apply]
    exact hqw'
  · rw [← hpol (a.symm v') (a.symm w'), LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact hpol'

theorem cSideFiveBoth_transport {V V' : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup V'] [Module (ZMod 2) V'] {q : QuadraticForm (ZMod 2) V}
    {q' : QuadraticForm (ZMod 2) V'} {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)}
    {σ' : A5 × A5 →* (V' ≃ₗ[ZMod 2] V')} (a : V ≃ₗ[ZMod 2] V') (ψ : A5 × A5 ≃* A5 × A5)
    (hψ : ∀ g u, a (σ g u) = σ' (ψ g) (a u)) (hq : ∀ u, q' (a u) = q u)
    (h : CSideFiveBoth q σ) : CSideFiveBoth q' σ' := by
  intro b' hb' g' hg'5 hg'1 hg'2
  let g : A5 × A5 := ψ.symm g'
  have hψg : ψ g = g' := MulEquiv.apply_symm_apply ψ g'
  have hg5 : orderOf g = 5 := by
    have hg := (ψ.symm).orderOf_eq g'
    simpa [g, hg'5] using hg
  have hgn : g.1 ≠ 1 ∧ g.2 ≠ 1 := by
    have hg := (cSide_psi_nontrivial_iff ψ.symm g').mp ⟨hg'1, hg'2⟩
    simpa [g] using hg
  let b : V ≃ₗ[ZMod 2] V := Swap.transport a.symm b'
  have hb : cSideFreeSwap q σ b := cSideFreeSwap_transport a ψ hψ hq hb'
  have hpair := h b hb g hg5 hgn.1 hgn.2
  have hpt : ∀ v : V, a (σ g v) = σ' g' (a v) := by
    intro v
    rw [hψ g v, hψg]
  have hpol := transportC_polar (q := q) (q' := q') a hq
  have hiff : (∃ l : A5 × A5, σ l * b * σ g = σ g * (σ l * b)) ↔
      (∃ l : A5 × A5, σ' l * b' * σ' g' = σ' g' * (σ' l * b')) := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨ψ l, ?_⟩
      have hl' : σ' (ψ l) * b' * σ' (ψ g) = σ' (ψ g) * (σ' (ψ l) * b') :=
        (transportC_conj_iff (σ := σ) (σ' := σ') a ψ hψ b' g l).mp hl
      simpa [hψg] using hl'
    · rintro ⟨l', hl'⟩
      refine ⟨ψ.symm l', ?_⟩
      have hl'' : σ' (ψ (ψ.symm l')) * b' * σ' (ψ g) =
          σ' (ψ g) * (σ' (ψ (ψ.symm l')) * b') := by
        rw [MulEquiv.apply_symm_apply, hψg]
        exact hl'
      exact (transportC_conj_iff (σ := σ) (σ' := σ') a ψ hψ b' g (ψ.symm l')).mpr hl''
  refine ⟨?_, ?_⟩
  · intro hex'
    have hexV : ∃ l : A5 × A5, σ l * b * σ g = σ g * (σ l * b) := hiff.mpr hex'
    have hzero := hpair.1 hexV
    intro v' hv'
    have hv : σ g (a.symm v') = a.symm v' := by
      apply a.injective
      calc a (σ g (a.symm v')) = σ' g' (a (a.symm v')) := hpt (a.symm v')
        _ = σ' g' v' := by rw [LinearEquiv.apply_symm_apply]
        _ = v' := hv'
        _ = a (a.symm v') := (LinearEquiv.apply_symm_apply a v').symm
    have h0 := hzero (a.symm v') hv
    calc v' = a (a.symm v') := (LinearEquiv.apply_symm_apply a v').symm
      _ = a 0 := by rw [h0]
      _ = 0 := map_zero a
  · intro hnex'
    have hnexV : ¬ ∃ l : A5 × A5, σ l * b * σ g = σ g * (σ l * b) :=
      fun hex => hnex' (hiff.mp hex)
    have htriple := hpair.2 hnexV
    refine ⟨?_, ?_, ?_⟩
    · have he : {v : V // σ g v = v} ≃ {v' : V' // σ' g' v' = v'} :=
        Equiv.subtypeEquiv a.toEquiv (fun v => by
          show (σ g v = v) ↔ (σ' g') (a v) = a v
          constructor
          · intro hv
            rw [← hpt v, hv]
          · intro hv
            apply a.injective
            rw [hpt v, hv])
      rw [← Nat.card_congr he]
      exact htriple.1
    · exact transportC_fixedNondeg a (σ g) (σ' g') hpt hpol htriple.2.1
    · intro hp'
      exact htriple.2.2 (transportC_fixedPlane a (σ g) (σ' g') hpt hq hpol hp')

end CFSG.EvenSporadicStandard.HNRecog.CSide