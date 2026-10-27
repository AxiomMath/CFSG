module

public import CFSG.ClassicalInvolution.Q3.TL3T13
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfGlue
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfModel

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G]

theorem model37_two {m : ℕ} {𝒜 : Set (Finset (Fin m))} {X : Subgroup G} (φ : ↥X →* AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥X) (hZ : Subgroup.center ↥φ.range = ⊥)
    (hFix : FixTrivial φ.range 𝒜) {α : Finset (Fin m)} (hα : α ∈ 𝒜) (h4 : α.card = 4)
    (b : Bool) {L₀ : Subgroup G} (hL₀ : L₀ ≤ X)
    (hlab : (L₀.subgroupOf X).map φ = memBar α h4 b) {y : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    (hyL₀ : ∀ l ∈ L₀, y * l = l * y)
    (hgen : ∀ x ∈ X, x ∈ Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹}) :
    ∀ x ∈ X, y * x = x * y := by
  refine centralizes_of_oddFix φ hy hker hZ ?_ hy3 hyL₀ hL₀ hgen
  intro σ hσ hfixL r
  refine hFix α hα h4 b σ hσ ?_ r
  intro x hx
  have hx' : (x : AEQ m) ∈ (L₀.subgroupOf X).map φ := by rw [hlab]; exact hx
  obtain ⟨l, hl, hlx⟩ := hx'
  have hxl : x = φ.rangeRestrict l := Subtype.ext hlx.symm
  rw [hxl]
  exact hfixL l (Subgroup.mem_subgroupOf.mp hl)

theorem memBar_le_of_aeIdentOn {P : Set (Subgroup G)} {m : ℕ} {𝒜 : Set (Finset (Fin m))}
    {H : Subgroup (AEQ m)} (I : AEIdentOn P m 𝒜 H) {β : Finset (Fin m)} (hβ : β ∈ 𝒜)
    (h4 : β.card = 4) (b : Bool) : memBar β h4 b ≤ H := by
  obtain ⟨L, hL, hlab⟩ := I.label_surj β hβ h4 b
  intro x hx
  rw [← hlab] at hx
  obtain ⟨l, -, rfl⟩ := hx
  have : I.φ l ∈ I.φ.range := ⟨l, rfl⟩
  rw [I.range_eq] at this
  exact this

theorem gen_of_trans {P : Set (Subgroup G)} {L : Subgroup G}
    (htrans : ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') :
    ∀ x ∈ pSpan P, x ∈ Subgroup.closure
      {u : G | ∃ l ∈ L, ∃ c ∈ pSpan P, u = c * l * c⁻¹} := by
  have : pSpan P ≤ Subgroup.closure {u : G | ∃ l ∈ L, ∃ c ∈ pSpan P, u = c * l * c⁻¹} := by
    refine pSpan_le fun L' hL' u hu => ?_
    obtain ⟨c, hc, rfl⟩ := htrans L' hL'
    refine Subgroup.subset_closure ⟨c⁻¹ * u * c, mem_conjSub_iff.mp hu, c, hc, ?_⟩
    group
  exact fun x hx => this hx

theorem centralizes_of_e64 {P : Set (Subgroup G)} (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub)
    (hFix : FixTrivial AE.e64Sub AE.e64Sets) {y : G}
    (hy : y ∈ Subgroup.normalizer (pSpan P : Set G))
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1) {L : Subgroup G} (hL : L ∈ P)
    (hyL : ∀ l ∈ L, y * l = l * y)
    (htrans : ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') :
    ∀ x ∈ pSpan P, y * x = x * y := by
  obtain ⟨α, hα, h4, b, hlab⟩ := I.label L hL
  have hmem : ∀ β ∈ AE.e64Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ I.φ.range := by
    intro β hβ h4 b
    rw [I.range_eq]
    exact memBar_le_of_aeIdentOn I hβ h4 b
  have hFix' : FixTrivial I.φ.range AE.e64Sets := by rw [I.range_eq]; exact hFix
  exact model37_two I.φ I.ker_le (center_e64' I.range_eq hmem) hFix' hα h4 b (le_pSpan hL) hlab
    hy hy3 hyL (gen_of_trans htrans)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
