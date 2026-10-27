module

public import CFSG.GH74.Generic.BProg.B3.Obs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace LocBalSL4Basic

theorem congr_conj {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

end LocBalSL4Basic

theorem isLocBal32_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {B : Subgroup (MulAut X)} (h : IsLocBal32 X B) :
    IsLocBal32 Y (B.map (MulAut.congr e).toMonoidHom) := by
  intro H' hH' hBH'
  set Φ : MulAut X ≃* MulAut Y := MulAut.congr e with hΦ
  set H : Subgroup (MulAut X) := H'.map Φ.symm.toMonoidHom with hH
  have hmemH : ∀ g : MulAut X, g ∈ H ↔ Φ g ∈ H' := by
    intro g
    constructor
    · rintro ⟨g', hg', rfl⟩
      simpa using hg'
    · intro hg
      exact ⟨Φ g, hg, by simp⟩
  have hconj : (MulAut.conj : X →* MulAut X).range ≤ H := by
    rintro _ ⟨x, rfl⟩
    rw [hmemH, hΦ, LocBalSL4Basic.congr_conj]
    exact hH' ⟨e x, rfl⟩
  have hBH : B ≤ H := fun b hb => (hmemH b).2 (hBH' ⟨b, hb, rfl⟩)
  obtain ⟨h1, h2⟩ := h H hconj hBH
  let θ : ↥H' ≃* ↥H := Φ.symm.subgroupMap H'
  have hθB : ∀ b : ↥H', b ∈ (B.map Φ.toMonoidHom).subgroupOf H' → θ b ∈ B.subgroupOf H := by
    intro b hb
    obtain ⟨b₀, hb₀, hb₀e⟩ := Subgroup.mem_subgroupOf.mp hb
    rw [Subgroup.mem_subgroupOf]
    show Φ.symm (b : MulAut Y) ∈ B
    rw [← hb₀e]
    simpa using hb₀
  refine ⟨?_, ?_⟩
  · intro b hb hb1 c hc b' hb'
    have hc' : θ c ∈ involutionOddCore (θ b) := by
      rw [← involutionOddCore_map θ b]
      exact ⟨c, hc, rfl⟩
    have key := h1 (θ b) (hθB b hb) (fun hh => hb1 (θ.injective (by rw [hh, map_one]))) (θ c) hc'
      (θ b') (hθB b' hb')
    rw [← map_commutatorElement] at key
    exact θ.injective (by rw [key, map_one])
  · intro D hD hcard hsq
    let D₀ : Subgroup ↥H := D.map θ.toMonoidHom
    have hD₀ : D₀ ≤ B.subgroupOf H := by
      rintro _ ⟨d, hd, rfl⟩
      exact hθB d (hD hd)
    have hcard₀ : Nat.card ↥D₀ = 4 := by
      rw [Subgroup.card_map_of_injective θ.injective]
      exact hcard
    have hsq₀ : ∀ d ∈ D₀, d * d = 1 := by
      rintro _ ⟨d, hd, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, hsq d hd, map_one]
    have hΔ := h2 D₀ hD₀ hcard₀ hsq₀
    rw [eq_bot_iff]
    intro c hc
    have hθc : θ c ∈ deltaCore D₀ := by
      rw [mem_deltaCore_iff]
      rintro _ ⟨d, hd, rfl⟩ hd1
      rw [MulEquiv.coe_toMonoidHom] at hd1 ⊢
      have hc1 : c ∈ involutionOddCore d :=
        mem_deltaCore_iff.mp hc d hd (fun hh => hd1 (by rw [hh, map_one]))
      rw [← involutionOddCore_map θ d]
      exact ⟨c, hc1, rfl⟩
    rw [hΔ, Subgroup.mem_bot] at hθc
    rw [Subgroup.mem_bot]
    exact θ.injective (by rw [hθc, map_one])

end CFSG.GH74.Generic.BProg.B3
