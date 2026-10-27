module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Complement

public section

namespace CFSG.EvenSporadicStandard.ReeStd

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem pow_apply_of_intertwine {X Y : Type*} [Group X] [Group Y] (θ : X → Y)
    (ψ : MulAut X) (φ : MulAut Y) (h : ∀ x, θ (ψ x) = φ (θ x)) (n : ℕ) (x : X) :
    θ ((ψ ^ n) x) = (φ ^ n) (θ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

theorem exists_complement' {R Λ : Subgroup G} (hΛR : Λ ≤ R)
    (hΛn : ∀ r ∈ R, ∀ l ∈ Λ, r * l * r⁻¹ ∈ Λ)
    (hcard : Nat.card R = 16 * Nat.card Λ)
    {c : G} (hcR : c ∈ R) (hcΛ : c ∉ Λ) (hc2 : c * c = 1)
    (hccentral : ∀ r ∈ R, c * r * c⁻¹ * r⁻¹ ∈ Λ)
    {σ : G} (hσR : σ ∈ normalizer (R : Set G)) (hσΛ : σ ∈ normalizer (Λ : Set G))
    (hσ7 : ∀ r ∈ R, σ ^ 7 * r * (σ ^ 7)⁻¹ = r) (hσc : σ * c * σ⁻¹ = c)
    (hfree : ∀ r ∈ R, (σ * r * σ⁻¹ * r⁻¹ ∈ Λ ∨ σ * r * σ⁻¹ * r⁻¹ * c ∈ Λ) →
      (r ∈ Λ ∨ r * c ∈ Λ)) :
    (∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Λ) ∧ (∀ a ∈ R, a * a ∈ Λ) ∧
    ∃ W : Subgroup G, W ≤ R ∧ Λ ≤ W ∧ c ∉ W ∧ Nat.card R = 2 * Nat.card W ∧
      (∀ w ∈ W, σ * w * σ⁻¹ ∈ W) ∧ (∀ r ∈ R, r ∈ W ∨ r * c ∈ W) ∧
      ∀ a ∈ W, a ∉ Λ → ∀ b ∈ W, b ∉ Λ → ∃ i : ℕ, (σ ^ i * a * (σ ^ i)⁻¹) * b⁻¹ ∈ Λ := by
  classical
  have hN : (Λ.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff hΛR).mpr fun l r hl hr => hΛn r hr l hl
  obtain ⟨τ, hτ⟩ : ∃ τ : MulAut R, ∀ r : R, ((τ r : R) : G) = σ * r * σ⁻¹ :=
    ⟨Subgroup.normalizerMonoidHom R ⟨σ, hσR⟩, fun r => rfl⟩
  have hτpow : ∀ (n : ℕ) (r : R), ((τ ^ n) r : G) = σ ^ n * r * (σ ^ n)⁻¹ := by
    intro n r
    have h := pow_apply_of_intertwine (fun r : R => (r : G)) τ (MulAut.conj σ)
      (fun r => (hτ r).trans (MulAut.conj_apply σ r).symm) n r
    rw [h, ← map_pow (MulAut.conj : G →* MulAut G) σ n, MulAut.conj_apply]
  have hτ7 : τ ^ 7 = 1 := by
    ext r
    rw [hτpow]
    exact hσ7 r r.2
  have hNcard : Nat.card (Λ.subgroupOf R) = Nat.card Λ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΛR).toEquiv
  have hτN : ∀ r : R, τ r ∈ Λ.subgroupOf R ↔ r ∈ Λ.subgroupOf R := by
    intro r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hτ]
    exact (Subgroup.mem_normalizer_iff.mp hσΛ r).symm
  have hτc : τ ⟨c, hcR⟩ = ⟨c, hcR⟩ := Subtype.ext (by rw [hτ]; exact hσc)
  have hfreeR : ∀ r : R, (τ r * r⁻¹ ∈ Λ.subgroupOf R ∨
      τ r * r⁻¹ * ⟨c, hcR⟩ ∈ Λ.subgroupOf R) →
      (r ∈ Λ.subgroupOf R ∨ r * ⟨c, hcR⟩ ∈ Λ.subgroupOf R) := by
    intro r hr
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hτ] at hr ⊢
    exact hfree r r.2 hr
  obtain ⟨hcomm, hsq, W, hNW, hcW, hWcard, hWτ, hcover, htrans⟩ :=
    J1Std.exists_complement_quotient (Λ.subgroupOf R) (by rw [hNcard]; exact hcard)
      (c := ⟨c, hcR⟩) (fun h => hcΛ (Subgroup.mem_subgroupOf.mp h)) (Subtype.ext hc2)
      (fun r => Subgroup.mem_subgroupOf.mpr (hccentral r r.2)) τ hτN hτ7 hτc hfreeR
  refine ⟨fun a ha b hb => Subgroup.mem_subgroupOf.mp (hcomm ⟨a, ha⟩ ⟨b, hb⟩),
    fun a ha => Subgroup.mem_subgroupOf.mp (hsq ⟨a, ha⟩), W.map R.subtype, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact Subgroup.map_subtype_le W
  · intro l hl
    exact Subgroup.mem_map.mpr ⟨⟨l, hΛR hl⟩, hNW (Subgroup.mem_subgroupOf.mpr hl), rfl⟩
  · intro hcm
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.mp hcm
    have hxc' : x = ⟨c, hcR⟩ := Subtype.ext hxc
    rw [hxc'] at hx
    exact hcW hx
  · rw [Subgroup.card_subtype]
    exact hWcard
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_map.mpr ⟨τ x, hWτ x hx, hτ x⟩
  · intro r hr
    rcases hcover ⟨r, hr⟩ with h | h
    · exact Or.inl (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)
    · exact Or.inr (Subgroup.mem_map.mpr ⟨_, h, rfl⟩)
  · intro a ha haΛ b hb hbΛ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨i, hi⟩ := htrans x hx (fun h => haΛ (Subgroup.mem_subgroupOf.mp h)) y hy
      (fun h => hbΛ (Subgroup.mem_subgroupOf.mp h))
    refine ⟨i, ?_⟩
    have h := Subgroup.mem_subgroupOf.mp hi
    rwa [Subgroup.coe_mul, hτpow, Subgroup.coe_inv] at h

end CFSG.EvenSporadicStandard.ReeStd
