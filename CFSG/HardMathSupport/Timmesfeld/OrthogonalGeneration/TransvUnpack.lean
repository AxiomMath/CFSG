module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvAction
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.LocalAnalysis.GLTheoremB

variable {X : Type*} [Group X]

theorem actsLike_cases {T K : Subgroup X} (hTN : T ≤ Subgroup.normalizer (K : Set X)) {G : Type*}
    [Group G] (e : ↥K ≃* G) {c : MulAut G} (hcard : Nat.card (inducedAutGroup T K) = 2)
    (hact : ActsLike T K e (Subgroup.zpowers c)) :
    c ≠ 1 ∧
      (∀ (x : X) (hx : x ∈ T),
        MulAut.congr e (K.normalizerMonoidHom ⟨x, hTN hx⟩) = 1 ∨
          MulAut.congr e (K.normalizerMonoidHom ⟨x, hTN hx⟩) = c) ∧
      ∃ (x : X) (hx : x ∈ T), MulAut.congr e (K.normalizerMonoidHom ⟨x, hTN hx⟩) = c := by
  set φ : MulAut ↥K →* MulAut G := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  have hS : Nat.card (Subgroup.zpowers c) = 2 := by
    rw [← hact, Subgroup.card_map_of_injective hφinj, hcard]
  have hord : orderOf c = 2 := by rw [← Nat.card_zpowers]; exact hS
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hc2 : c ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one c
  have hmem : ∀ s ∈ Subgroup.zpowers c, s = 1 ∨ s = c := by
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk : c ^ k = c ^ (k % 2) := by
      have := zpow_mod_orderOf c k
      rw [hord] at this
      exact this.symm
    rw [hk]
    have : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases this with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  have hxI : ∀ (x : X) (hx : x ∈ T),
      K.normalizerMonoidHom ⟨x, hTN hx⟩ ∈ inducedAutGroup T K := fun x hx =>
    ⟨⟨x, hTN hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩
  refine ⟨hc1, fun x hx => ?_, ?_⟩
  · apply hmem
    rw [← hact]
    exact ⟨_, hxI x hx, rfl⟩
  · have hcS : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
    rw [← hact] at hcS
    obtain ⟨a, ha, hac⟩ := hcS
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨(y : X), (Subgroup.mem_subgroupOf).1 hy, ?_⟩
    exact hac

section ActsAs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {G : Type*} [Group G]

theorem normalizerMonoidHom_eq {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X)) (k : ↥K)
    (hk : x * (k : X) * x⁻¹ ∈ K) :
    K.normalizerMonoidHom ⟨x, hx⟩ k = ⟨x * (k : X) * x⁻¹, hk⟩ :=
  Subtype.ext (by simp)

theorem congr_normalizerMonoidHom_apply {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X))
    (e₀ : ↥K ≃* G) (k : ↥K) :
    MulAut.congr e₀ (K.normalizerMonoidHom ⟨x, hx⟩) (e₀ k) =
      e₀ (K.normalizerMonoidHom ⟨x, hx⟩ k) := by
  simp [MulAut.congr_apply]

theorem actsAsConj_one_of_eq_one {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X))
    (e₀ : ↥K ≃* G) (e₁ : G ≃* ↥(elementaryGroup Q))
    (h : MulAut.congr e₀ (K.normalizerMonoidHom ⟨x, hx⟩) = 1) :
    ActsAsConj (e₀.trans e₁) x (1 : V ≃ₗ[ZMod 2] V) := by
  intro k hk
  have h1 : e₀ ⟨x * (k : X) * x⁻¹, hk⟩ = e₀ k := by
    rw [← normalizerMonoidHom_eq hx k hk, ← congr_normalizerMonoidHom_apply hx e₀ k, h]
    rfl
  simp only [MulEquiv.trans_apply, h1]
  simp

theorem actsAsConj_of_eq {x : X} (hx : x ∈ Subgroup.normalizer (K : Set X))
    (e₀ : ↥K ≃* G) (e₁ : G ≃* ↥(elementaryGroup Q)) {c : MulAut G} {g : V ≃ₗ[ZMod 2] V}
    (h : MulAut.congr e₀ (K.normalizerMonoidHom ⟨x, hx⟩) = c)
    (hc : ∀ y : G, ((e₁ (c y) : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V) =
      g * (e₁ y : V ≃ₗ[ZMod 2] V) * g⁻¹) :
    ActsAsConj (e₀.trans e₁) x g := by
  intro k hk
  have h1 : e₀ ⟨x * (k : X) * x⁻¹, hk⟩ = c (e₀ k) := by
    rw [← normalizerMonoidHom_eq hx k hk, ← congr_normalizerMonoidHom_apply hx e₀ k, h]
  simp only [MulEquiv.trans_apply, h1]
  exact hc (e₀ k)

end ActsAs

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
