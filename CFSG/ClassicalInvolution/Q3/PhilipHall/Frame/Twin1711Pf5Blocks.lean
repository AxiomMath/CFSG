module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf3Sp0Core

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open Sp0Core in
theorem noSandwich_blocks {Y : Type} [Group Y] [Finite Y] {R₀ : Subgroup Y} {t₀ c : Y} {b1 b2 : ℕ}
    (hu : IsUniqueInvolution R₀ t₀)
    (hnorm : ∀ s ∈ TT t₀, conjSub s R₀ = R₀)
    (hover : ∀ S : Subgroup Y, TT t₀ ≤ S → S ≠ ⊤ → ∀ g ∈ S, g ∈ TT t₀ ∨ ∃ s ∈ TT t₀, g = c * s)
    (hfix1 : Nat.card ↥(fixSet (⊤ : Subgroup Y) ({R₀} : Set (Subgroup Y))) ≤ b1)
    (hfix2 : Nat.card ↥(fixSet (⊤ : Subgroup Y) ({R₀, conjSub c R₀} : Set (Subgroup Y))) ≤ b2)
    (hidx1 : ∀ N : Subgroup Y, R₀ ≤ N → N ≤ TT t₀ → (N.subgroupOf (TT t₀)).Normal →
      (∀ x : Y, x * t₀ * x⁻¹ ∈ N → x * t₀ * x⁻¹ = t₀) → b1 < N.relIndex (TT t₀))
    (hidx2 : ∀ N : Subgroup Y, R₀ ≤ N → N ≤ TT t₀ → (N.subgroupOf (TT t₀)).Normal →
      (∀ x : Y, x * t₀ * x⁻¹ ∈ N → x * t₀ * x⁻¹ = t₀ ∨ x * t₀ * x⁻¹ = c * t₀ * c⁻¹) →
        b2 < N.relIndex (TT t₀))
    {B : Set (Subgroup Y)} {N : Subgroup Y} (hS : SandwichData (⊤ : Subgroup Y) R₀ t₀ B N) :
    False := by
  have hstab : ∀ g : Y, conjSub g R₀ ∈ B → g ∈ stabB B := by
    intro g hg
    rcases hS.block g (Subgroup.mem_top g) with h1 | h1
    · exact Sp0Core.mem_stabB.2 h1
    · exfalso
      exact Set.disjoint_left.mp h1 ⟨R₀, hS.mem, rfl⟩ hg
  have hTS : TT t₀ ≤ stabB B := fun s hs => hstab s (by rw [hnorm s hs]; exact hS.mem)
  have hSne : stabB B ≠ ⊤ := by
    intro h
    apply hS.proper
    ext J
    constructor
    · exact fun hJ => hS.sub hJ
    · rintro ⟨g, -, rfl⟩
      have h' : conjSub g '' B = B := Sp0Core.mem_stabB.1 (h ▸ Subgroup.mem_top g : g ∈ stabB B)
      rw [← h']
      exact ⟨R₀, hS.mem, rfl⟩
  have hBeq : ∀ J, J ∈ B ↔ ∃ s ∈ stabB B, conjSub s R₀ = J := by
    intro J
    constructor
    · intro hJ
      obtain ⟨x, -, hx⟩ := hS.sub hJ
      exact ⟨x, hstab x (hx ▸ hJ), hx⟩
    · rintro ⟨s, hs, rfl⟩
      have h' : conjSub s '' B = B := Sp0Core.mem_stabB.1 hs
      rw [← h']
      exact ⟨R₀, hS.mem, rfl⟩
  have hNle : N ≤ TT t₀ := hS.le
  have hNn : (N.subgroupOf (TT t₀)).Normal := hS.normal
  have hR₀N : R₀ ≤ N := by
    have := hS.twins_le 1 (Subgroup.one_mem _)
    rwa [conjSub_one] at this
  have hidx : N.relIndex (TT t₀) ≤ Nat.card ↥(fixSet (⊤ : Subgroup Y) B) := hS.index
  by_cases hall : ∀ g ∈ stabB B, g ∈ TT t₀
  · have hB : B = {R₀} := by
      ext J
      rw [hBeq J, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hnorm s (hall s hs)
      · rintro rfl
        exact ⟨1, Subgroup.one_mem _, conjSub_one _⟩
    rw [hB] at hidx
    have h1 := hidx1 N hR₀N hNle hNn (by
      intro x hx
      obtain ⟨J, hJ, hJu⟩ := hS.inv x (Subgroup.mem_top x) hx
      rw [hB, Set.mem_singleton_iff] at hJ
      subst hJ
      exact (hu.eq hJu).symm)
    omega
  · push Not at hall
    obtain ⟨g, hg, hgT⟩ := hall
    rcases hover _ hTS hSne g hg with h | ⟨s, hs, hgs⟩
    · exact hgT h
    have hcS : c ∈ stabB B := by
      have : c = g * s⁻¹ := by rw [hgs]; group
      rw [this]
      exact (stabB B).mul_mem hg ((stabB B).inv_mem (hTS hs))
    have hB : B = {R₀, conjSub c R₀} := by
      ext J
      rw [hBeq J]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s', hs', rfl⟩
        rcases hover _ hTS hSne s' hs' with h | ⟨s'', hs'', rfl⟩
        · left; exact hnorm s' h
        · right; rw [conjSub_mul, hnorm s'' hs'']
      · rintro (rfl | rfl)
        · exact ⟨1, Subgroup.one_mem _, conjSub_one _⟩
        · exact ⟨c, hcS, rfl⟩
    rw [hB] at hidx
    have h2 := hidx2 N hR₀N hNle hNn (by
      intro x hx
      obtain ⟨J, hJ, hJu⟩ := hS.inv x (Subgroup.mem_top x) hx
      rw [hB] at hJ
      rcases hJ with rfl | rfl
      · left; exact (hu.eq hJu).symm
      · right; exact ((hu.conj c).eq hJu).symm)
    omega

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711
