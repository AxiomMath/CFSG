module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Pair
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfShared

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G]

section Induced

variable {X : Subgroup G} {M : Type} [Group M] (φ : ↥X →* M) {y : G}
  (hy : y ∈ Subgroup.normalizer (X : Set G))

include hy in
theorem centralizes_of_oddFixPair {L₀ L₁ : Subgroup G} (hker : φ.ker ≤ Subgroup.center ↥X)
    (hZ : Subgroup.center ↥φ.range = ⊥)
    (hfix : ∀ σ : ↥φ.range →* ↥φ.range, (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) →
      (∀ l : ↥X, (l : G) ∈ L₀ → σ (φ.rangeRestrict l) = φ.rangeRestrict l) →
      (∀ l : ↥X, (l : G) ∈ L₁ → σ (φ.rangeRestrict l) = φ.rangeRestrict l) →
        ∀ r, σ r = r)
    (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    (hyL₀ : ∀ l ∈ L₀, y * l = l * y) (hyL₁ : ∀ l ∈ L₁, y * l = l * y) (hL₀ : L₀ ≤ X)
    (hgen : ∀ x ∈ X, x ∈ Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹}) :
    ∀ x ∈ X, y * x = x * y := by
  have hk := fun x (hx : x ∈ φ.ker) => ker_invariant φ hy hker hZ hx
  obtain ⟨a, ha⟩ := hy3
  have hfixL : ∀ L : Subgroup G, (∀ l ∈ L, y * l = l * y) → ∀ l : ↥X, (l : G) ∈ L →
      induced φ hy hk (φ.rangeRestrict l) = φ.rangeRestrict l := by
    intro L hyL l hl
    rw [induced_apply]
    congr 1
    apply Subtype.ext
    rw [conjOn_apply]
    have := hyL l hl
    calc y * (l : G) * y⁻¹ = l * y * y⁻¹ := by rw [this]
      _ = l := by group
  have hfixσ := hfix (induced φ hy hk) ⟨a, fun r => by
      obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective r
      rw [induced_iterate]
      congr 1
      apply Subtype.ext
      rw [conjOn_iterate, ha]
      simp⟩ (hfixL L₀ hyL₀) (hfixL L₁ hyL₁)
  refine centralizes_of_trivial_mod_ker φ hker hy (fun x => ?_) hyL₀ hL₀ hgen
  have := hfixσ (φ.rangeRestrict x)
  rw [induced_apply] at this
  have h2 := congrArg Subtype.val this
  exact h2

end Induced

theorem model37_pair {m : ℕ} {𝒜 : Set (Finset (Fin m))} {X : Subgroup G} (φ : ↥X →* AEQ m)
    (hker : φ.ker ≤ Subgroup.center ↥X) (hZ : Subgroup.center ↥φ.range = ⊥)
    (hFix : FixTrivialPair φ.range 𝒜) {α β : Finset (Fin m)} (hα : α ∈ 𝒜) (hβ : β ∈ 𝒜)
    (h4 : α.card = 4) (h4' : β.card = 4) (b b' : Bool) {L₀ L₁ : Subgroup G} (hL₀ : L₀ ≤ X)
    (hL₁ : L₁ ≤ X) (hlab : (L₀.subgroupOf X).map φ = memBar α h4 b)
    (hlab' : (L₁.subgroupOf X).map φ = memBar β h4' b') (hzb : zBar β h4' = zBar α h4)
    (hne : memBar α h4 b ≠ memBar β h4' b') {y : G}
    (hy : y ∈ Subgroup.normalizer (X : Set G)) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    (hyL₀ : ∀ l ∈ L₀, y * l = l * y) (hyL₁ : ∀ l ∈ L₁, y * l = l * y)
    (hgen : ∀ x ∈ X, x ∈ Subgroup.closure {u : G | ∃ l ∈ L₀, ∃ c ∈ X, u = c * l * c⁻¹}) :
    ∀ x ∈ X, y * x = x * y := by
  refine centralizes_of_oddFixPair φ hy hker hZ ?_ hy3 hyL₀ hyL₁ hL₀ hgen
  intro σ hσ hfixL₀ hfixL₁ r
  refine hFix α hα h4 b β hβ h4' b' hzb hne σ hσ ?_ ?_ r
  · intro x hx
    have hx' : (x : AEQ m) ∈ (L₀.subgroupOf X).map φ := by rw [hlab]; exact hx
    obtain ⟨l, hl, hlx⟩ := hx'
    have hxl : x = φ.rangeRestrict l := Subtype.ext hlx.symm
    rw [hxl]
    exact hfixL₀ l (Subgroup.mem_subgroupOf.mp hl)
  · intro x hx
    have hx' : (x : AEQ m) ∈ (L₁.subgroupOf X).map φ := by rw [hlab']; exact hx
    obtain ⟨l, hl, hlx⟩ := hx'
    have hxl : x = φ.rangeRestrict l := Subtype.ext hlx.symm
    rw [hxl]
    exact hfixL₁ l (Subgroup.mem_subgroupOf.mp hl)

theorem centralizes_of_e29_pair [Finite G] {P : Set (Subgroup G)}
    (I : AEIdentOn P 8 AE.e29Sets AE.e29Sub) {y : G}
    (hy : y ∈ Subgroup.normalizer (pSpan P : Set G)) (hy3 : ∃ a : ℕ, y ^ 3 ^ a = 1)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) (h8 : Nat.card L = 8) (h8' : Nat.card L' = 8)
    {u : G} (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u)
    (hne : (L.subgroupOf (pSpan P)).map I.φ ≠ (L'.subgroupOf (pSpan P)).map I.φ)
    (hyL : ∀ l ∈ L, y * l = l * y) (hyL' : ∀ l ∈ L', y * l = l * y)
    (htrans : ∀ L'' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L'') :
    ∀ x ∈ pSpan P, y * x = x * y := by
  obtain ⟨α, hα, h4, b, hlab⟩ := I.label L hL
  obtain ⟨β, hβ, h4', b', hlab'⟩ := I.label L' hL'
  have hmem : ∀ γ ∈ AE.e29Sets, ∀ hγ : γ.card = 4, ∀ b, memBar γ hγ b ≤ I.φ.range := by
    intro γ hγ h4 b
    rw [I.range_eq]
    exact memBar_le_of_aeIdentOn I hγ h4 b
  have hFix' : FixTrivialPair I.φ.range AE.e29Sets := by
    rw [I.range_eq]; exact fixTrivialPair_e29
  have hzb : zBar β h4' = zBar α h4 := by
    have h1 := phi_map_eq_zBar I.φ (by norm_num) hL h8 hlab hu
    have h2 := phi_map_eq_zBar I.φ (by norm_num) hL' h8' hlab' hu'
    rw [← h1, ← h2]
  have hne' : memBar α h4 b ≠ memBar β h4' b' := by
    rw [← hlab, ← hlab']; exact hne
  exact model37_pair I.φ I.ker_le (center_e29' I.range_eq hmem) hFix' hα hβ h4 h4' b b'
    (le_pSpan hL) (le_pSpan hL') hlab hlab' hzb hne' hy hy3 hyL hyL' (gen_of_trans htrans)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf
