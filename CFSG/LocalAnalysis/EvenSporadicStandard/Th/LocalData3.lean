module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData2

public section

namespace CFSG.EvenSporadicStandard.ThStd

variable {F F' : Type*} [Group F] [Group F']

structure ThLocalWitness3 (S A B Aa : Subgroup F) : Prop where
  transv : ∀ g : F, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∉ B →
    (∃ H : Subgroup F, H ≤ A ∧ Nat.card H = 8 ∧ ∀ a ∈ H, g * a = a * g) →
    ∀ K : Subgroup F, K ≤ Aa → (∀ x ∈ K, g * x = x * g) → Nat.card K ≤ 16
  center_quotient : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B

@[expose] def ThLocalData3 (F : Type*) [Group F] : Prop :=
  ∃ (S A B : Subgroup F) (z : F) (Aa : Subgroup F) (b : F),
    ThLocalWitness S A B z ∧ ThLocalWitness2 B A Aa b ∧ ThLocalWitness3 S A B Aa

theorem ThLocalWitness3.map_equiv (e : F ≃* F') {S A B Aa : Subgroup F'}
    (W : ThLocalWitness3 S A B Aa) :
    ThLocalWitness3 (S.map (e.symm : F' →* F)) (A.map (e.symm : F' →* F))
      (B.map (e.symm : F' →* F)) (Aa.map (e.symm : F' →* F)) := by
  have hmem : ∀ K : Subgroup F', ∀ x : F, x ∈ K.map (e.symm : F' →* F) ↔ e x ∈ K := fun K x => by
    simpa using Subgroup.mem_map_equiv (f := e.symm) (K := K) (x := x)
  have hmapmem : ∀ K : Subgroup F, ∀ x : F', x ∈ K.map (e : F →* F') ↔ e.symm x ∈ K := fun K x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨e.symm x, h, by simp⟩
  refine ⟨fun g hgA hgB hH K hKAa hKc => ?_, fun s hs hsc => ?_⟩
  · obtain ⟨H, hHA, hHc, hHg⟩ := hH
    set g' : F' := e g with hg'
    have h1 : ∀ a ∈ A, g' * a * g'⁻¹ ∈ A := fun a ha => by
      have := hgA (e.symm a) ((hmem A _).2 (by simpa using ha))
      rw [hmem] at this
      simpa [hg'] using this
    have h2 : g' ∉ B := fun h => hgB ((hmem B _).2 h)
    have hHmap : H.map (e : F →* F') = (H.map (e : F →* F')) := rfl
    have h3 : ∃ H' : Subgroup F', H' ≤ A ∧ Nat.card H' = 8 ∧ ∀ a ∈ H', g' * a = a * g' := by
      refine ⟨H.map (e : F →* F'), ?_, ?_, ?_⟩
      · intro x hx
        have := hHA ((hmapmem H x).1 hx)
        rw [hmem] at this
        simpa using this
      · rw [Subgroup.card_map_of_injective e.injective]
        exact hHc
      · intro a ha
        have := hHg _ ((hmapmem H a).1 ha)
        simpa [hg'] using congrArg e this
    have h4 := W.transv g' h1 h2 h3 (K.map (e : F →* F'))
      (fun x hx => by
        have := hKAa ((hmapmem K x).1 hx)
        rw [hmem] at this
        simpa using this)
      (fun x hx => by
        have := hKc _ ((hmapmem K x).1 hx)
        simpa [hg'] using congrArg e this)
    rwa [Subgroup.card_map_of_injective e.injective] at h4
  · have hs' : e s ∈ S := (hmem S s).1 hs
    have := W.center_quotient (e s) hs' (fun x hx => by
      have := hsc (e.symm x) ((hmem S _).2 (by simpa using hx))
      rw [hmem] at this
      simpa using this)
    exact (hmem B s).2 this

theorem ThLocalData3.of_mulEquiv (e : F ≃* F') (h : ThLocalData3 F') : ThLocalData3 F := by
  obtain ⟨S, A, B, z, Aa, b, W, W2, W3⟩ := h
  exact ⟨_, _, _, _, _, _, W.map_equiv e, W2.map_equiv e, W3.map_equiv e⟩

end CFSG.EvenSporadicStandard.ThStd
