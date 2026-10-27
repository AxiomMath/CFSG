module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrMem

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Defs

variable {G : Type} [Group G]

@[expose] def MovedOddFreeAt (c a : G) (haC : a ∈ Subgroup.centralizer ({c} : Set G)) : Prop :=
  (∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) →
      (∃ y ∈ L₂, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) → L₁ = L₂) ∧
    ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L →
      oddQuotMk c ⟨a, haC⟩ ∈ Subgroup.normalizer (L : Set (OddQuot c)) →
      (∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) →
      Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨a, haC⟩))

variable [Finite G]

@[expose] def SecOddFree {Y : Type} [Group Y] [Finite Y] (R : Subgroup Y) (c : Y)
    (x : SecQ R c) : Prop :=
  (∀ L₁ L₂ : Subgroup (SecQ R c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, x * y ≠ y * x) → (∃ y ∈ L₂, x * y ≠ y * x) → L₁ = L₂) ∧
    SecMovedOddFree R c x

end Defs

section Classical

variable {G : Type} [Group G] [Finite G]


theorem movedOddFreeAt_of_classicalOrQuiet (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {c a : G} (hc1 : c ≠ 1)
    {haC : a ∈ Subgroup.centralizer ({c} : Set G)} (h : ClassicalOrQuiet c a haC) :
    MovedOddFreeAt c a haC :=
  ⟨atMostOne_of_classicalOrQuiet hBelow hZ hc1 h, fun L hL hN hm =>
    autOddFreeOn_of_classicalOrQuiet hBelow hZ hc1 h L hL hN hm⟩

end Classical

section Transport

variable {G : Type} [Group G] [Finite G]

theorem atMostOne_quot_of_subnormal {H : Subgroup G} (hH : IsSubnormal H ⊤) {τ : G}
    (hτ : τ ∈ H)
    (hsec : ∀ L₁ L₂ : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H), CFSG.IsComponent L₁ →
      CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) * y ≠
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)) →
      (∃ y ∈ L₂, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H) * y ≠
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨τ, hτ⟩ : H)) → L₁ = L₂)
    (L₁ L₂ : Subgroup (G ⧸ componentClassificationOddCore G)) (hL₁ : CFSG.IsComponent L₁)
    (hL₂ : CFSG.IsComponent L₂)
    (hm₁ : ∃ y ∈ L₁, QuotientGroup.mk' (componentClassificationOddCore G) τ * y ≠
      y * QuotientGroup.mk' (componentClassificationOddCore G) τ)
    (hm₂ : ∃ y ∈ L₂, QuotientGroup.mk' (componentClassificationOddCore G) τ * y ≠
      y * QuotientGroup.mk' (componentClassificationOddCore G) τ) : L₁ = L₂ := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  obtain ⟨χ, hχ, hχmk, hχR⟩ := exists_oddQuot_embedding hH
  set x : ↥H ⧸ M := QuotientGroup.mk' M ⟨τ, hτ⟩ with hx
  have hχx : χ x = QuotientGroup.mk' N τ := hχmk ⟨τ, hτ⟩
  have hHm : H.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hH
      Subgroup.IsSubnormal.top
  have hRm : χ.range.IsSubnormal := by
    rw [hχR]
    exact hHm.map (QuotientGroup.mk'_surjective N)
  have hτR : QuotientGroup.mk' N τ ∈ χ.range := ⟨x, hχx⟩
  have key : ∀ L : Subgroup (G ⧸ N), CFSG.IsComponent L →
      (∃ y ∈ L, QuotientGroup.mk' N τ * y ≠ y * QuotientGroup.mk' N τ) →
      L ≤ χ.range ∧ CFSG.IsComponent (L.comap χ) ∧ ∃ y ∈ L.comap χ, x * y ≠ y * x := by
    intro L hL hτL
    have hle : L ≤ χ.range := by
      rcases CFSG.LocalCores.component_subnormal_subgroup hL hRm with h | h
      · exact h
      · exfalso
        obtain ⟨y, hy, hne⟩ := hτL
        apply hne
        have hc := Subgroup.commutator_mem_commutator hy hτR
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc.symm
    refine ⟨hle, ?_, ?_⟩
    · set χ' : (↥H ⧸ M) ≃* ↥χ.range := MonoidHom.ofInjective hχ with hχ'
      have h1 := CFSG.LocalCores.isComponent_map_mulEquiv χ'.symm
        (CFSG.LocalCores.component_overgroup hL hle)
      have h2 : (L.subgroupOf χ.range).map χ'.symm.toMonoidHom = L.comap χ := by
        ext z
        rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
          Subgroup.mem_comap]
        rfl
      rwa [h2] at h1
    · obtain ⟨y, hy, hne⟩ := hτL
      obtain ⟨w, rfl⟩ := hle hy
      refine ⟨w, hy, fun h => hne ?_⟩
      have h2 := congrArg χ h
      rwa [map_mul, map_mul, hχx] at h2
  obtain ⟨hle₁, hc₁, hmv₁⟩ := key L₁ hL₁ hm₁
  obtain ⟨hle₂, hc₂, hmv₂⟩ := key L₂ hL₂ hm₂
  have h12 := hsec _ _ hc₁ hc₂ hmv₁ hmv₂
  rw [← Subgroup.map_comap_eq_self hle₁, ← Subgroup.map_comap_eq_self hle₂, h12]

theorem movedOddFreeAt_of_sec {C : Subgroup G} {H : Subgroup ↥C} (hH : IsSubnormal H ⊤)
    {a : C} (ha : a ∈ H) {c : G} (hC : C = Subgroup.centralizer ({c} : Set G))
    (hx : (∀ L₁ L₂ : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H), CFSG.IsComponent L₁ →
      CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H) * y ≠
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H)) →
      (∃ y ∈ L₂, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H) * y ≠
        y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H)) → L₁ = L₂) ∧
      ∀ L : Subgroup (↥H ⧸ classicalInvolutionOddCore ↥H), CFSG.IsComponent L →
        QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H) ∈
          Subgroup.normalizer (L : Set (↥H ⧸ classicalInvolutionOddCore ↥H)) →
        (∃ y ∈ L, QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H) * y ≠
          y * QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H)) →
        Q3NM.AutOddFreeOn ↥L
          (IsInducedAut L (QuotientGroup.mk' (classicalInvolutionOddCore ↥H) (⟨a, ha⟩ : H)))) :
    (∀ L₁ L₂ : Subgroup (↥C ⧸ componentClassificationOddCore ↥C), CFSG.IsComponent L₁ →
      CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, QuotientGroup.mk' (componentClassificationOddCore ↥C) a * y ≠
        y * QuotientGroup.mk' (componentClassificationOddCore ↥C) a) →
      (∃ y ∈ L₂, QuotientGroup.mk' (componentClassificationOddCore ↥C) a * y ≠
        y * QuotientGroup.mk' (componentClassificationOddCore ↥C) a) → L₁ = L₂) ∧
    ∀ L : Subgroup (↥C ⧸ componentClassificationOddCore ↥C), CFSG.IsComponent L →
      QuotientGroup.mk' (componentClassificationOddCore ↥C) a ∈
        Subgroup.normalizer (L : Set (↥C ⧸ componentClassificationOddCore ↥C)) →
      (∃ y ∈ L, QuotientGroup.mk' (componentClassificationOddCore ↥C) a * y ≠
        y * QuotientGroup.mk' (componentClassificationOddCore ↥C) a) →
      Q3NM.AutOddFreeOn ↥L
        (IsInducedAut L (QuotientGroup.mk' (componentClassificationOddCore ↥C) a)) := by
  subst hC
  exact ⟨atMostOne_quot_of_subnormal hH ha hx.1, fun L hL hN hm =>
    movedOddFree_quot_of_subnormal hH ha hx.2 L hL hN hm⟩

end Transport

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
