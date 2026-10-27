module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

theorem le_trivialOnQuot_of_mutual_normalizer {G : Type} [Group G] [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {M L : Subgroup G} (hM : M ∈ Ω) (hL : L ∈ Ω)
    (hne : M ≠ L) (hML : M ≤ Subgroup.normalizer (L : Set G))
    (hLM : L ≤ Subgroup.normalizer (M : Set G)) : M ≤ trivialOnQuot L := by
  have hcomm : ∀ a ∈ M, ∀ x ∈ L, ⁅a, x⁆ ∈ M ⊓ L := by
    intro a ha x hx
    have h1 : a * x * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hML ha) x).mp hx
    have h2 : x * a⁻¹ * x⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hLM hx) a⁻¹).mp (inv_mem ha)
    have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by
      simp only [commutatorElement_def, mul_assoc]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [e]
      exact M.mul_mem ha h2
    · rw [commutatorElement_def]
      exact L.mul_mem h1 (inv_mem hx)
  have hLN : L ≤ Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) := by
    intro l hl
    have hM' : ∀ y, y ∈ M ↔ l * y * l⁻¹ ∈ M := fun y =>
      Subgroup.mem_normalizer_iff.mp (hLM hl) y
    have hL' : ∀ y, y ∈ L ↔ l * y * l⁻¹ ∈ L := fun y =>
      Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) y
    rw [Subgroup.mem_normalizer_iff]
    intro y
    show y ∈ M ⊓ L ↔ l * y * l⁻¹ ∈ M ⊓ L
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (hM' y) (hL' y)
  intro a ha
  refine mem_trivialOnQuot_iff.mpr ⟨hML ha, fun x hx => ?_⟩
  obtain ⟨h2, himp⟩ := hΩ.omega4 M hM L hL hne
  rcases (show padicValNat 2 (Nat.card ↥(M ⊓ L)) = 0 ∨
      padicValNat 2 (Nat.card ↥(M ⊓ L)) = 1 by omega) with h0 | h1
  ·
    have hodd : Odd (Nat.card ↥(M ⊓ L)) := by
      rcases padicValNat.eq_zero_iff.mp h0 with h | h | h
      · exact absurd h (by norm_num)
      · exact absurd h (Nat.card_pos.ne')
      · exact Nat.odd_iff.mpr (by omega)
    have hsub : M ⊓ L ≤ CFSG.ClassicalInvolution.Balance.oddCoreIn L :=
      CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes inf_le_right hLN hodd
    exact hsub (hcomm a ha x hx)
  ·
    have hc : ⁅a, x⁆ ∈ ⁅M, L⁆ := Subgroup.commutator_mem_commutator ha hx
    exact (Subgroup.mem_inf.mp (himp h1 hc)).2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
