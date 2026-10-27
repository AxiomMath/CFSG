module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathSplit

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] {A Aa D : Subgroup G} {t : G}

@[expose] def wreathN₁ (hD : DHyp A Aa t D) (Q : Subgroup G) (w : AddMonoid.End (VSub hD)) :
    Subgroup G :=
  normalizer (Q : Set G) ⊓ wComm hD w ⊓ centralizer (wKer hD w : Set G)

@[expose] def wreathP₁ (hD : DHyp A Aa t D) (Q : Subgroup G) (w : AddMonoid.End (VSub hD)) :
    Subgroup G :=
  closure {x | x ∈ wreathN₁ hD Q w ∧ Odd (orderOf x)}

@[expose] def wreathE₂ (hD : DHyp A Aa t D) (Q : Subgroup G) (w : AddMonoid.End (VSub hD)) :
    Subgroup G :=
  Q ⊓ centralizer (wreathP₁ hD Q w : Set G)

theorem mem_wreathN₁_iff (hD : DHyp A Aa t D) {Q : Subgroup G} {w : AddMonoid.End (VSub hD)}
    {x : G} : x ∈ wreathN₁ hD Q w ↔
      x ∈ normalizer (Q : Set G) ∧ x ∈ wComm hD w ∧ ∀ v ∈ wKer hD w, x * v * x⁻¹ = v := by
  simp only [wreathN₁, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨hxQ, hxw⟩, hc⟩
    exact ⟨hxQ, hxw, fun v hv => by rw [← hc v hv]; group⟩
  · rintro ⟨hxQ, hxw, hc⟩
    refine ⟨⟨hxQ, hxw⟩, fun v hv => ?_⟩
    calc v * x = (x * v * x⁻¹) * x := by rw [hc v hv]
      _ = x * v := by group

theorem wreathP₁_le_wreathN₁ (hD : DHyp A Aa t D) (Q : Subgroup G)
    (w : AddMonoid.End (VSub hD)) : wreathP₁ hD Q w ≤ wreathN₁ hD Q w :=
  (closure_le _).2 fun _ hx => hx.1

theorem mem_wreathP₁_of_odd (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} {x : G} (hx : x ∈ wreathN₁ hD Q w) (hodd : Odd (orderOf x)) :
    x ∈ wreathP₁ hD Q w :=
  subset_closure ⟨hx, hodd⟩

theorem wreathP₁_le_closure_odd (hD : DHyp A Aa t D) (Q : Subgroup G)
    (w : AddMonoid.End (VSub hD)) :
    wreathP₁ hD Q w ≤ closure {x | x ∈ wreathP₁ hD Q w ∧ Odd (orderOf x)} :=
  closure_mono fun _ hx => ⟨subset_closure hx, hx.2⟩

theorem wreathE₂_le (hD : DHyp A Aa t D) (Q : Subgroup G) (w : AddMonoid.End (VSub hD)) :
    wreathE₂ hD Q w ≤ Q :=
  inf_le_left

theorem mem_wreathE₂_iff (hD : DHyp A Aa t D) {Q : Subgroup G} {w : AddMonoid.End (VSub hD)}
    {e : G} : e ∈ wreathE₂ hD Q w ↔ e ∈ Q ∧ ∀ x ∈ wreathP₁ hD Q w, x * e = e * x := by
  simp only [wreathE₂, mem_inf, mem_centralizer_iff, SetLike.mem_coe]

end CFSG.EvenSporadicStandard.ThStd
