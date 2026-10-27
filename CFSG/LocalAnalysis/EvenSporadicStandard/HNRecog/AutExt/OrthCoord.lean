module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

variable {G : Type} [Group G]

structure OrthCoord (K M : Subgroup G) (ρ : ↥K →* Perm (Fin 5)) (θ : G → Fv5) : Prop where
  le : M ≤ K
  sign_eq : ∀ l : ↥K, sign (ρ l) = 1
  surj : ∀ g : Perm (Fin 5), sign g = 1 → ∃ l : ↥K, ρ l = g
  ker : ∀ l : ↥K, ρ l = 1 ↔ (l : G) ∈ M
  mul : ∀ x ∈ M, ∀ y ∈ M, θ (x * y) = θ x + θ y
  even : ∀ x ∈ M, Fv5Even (θ x)
  inj : ∀ x ∈ M, ∀ y ∈ M, θ x = θ y → x = y
  exists_eq : ∀ e : Fv5, Fv5Even e → ∃ x ∈ M, θ x = e
  conj : ∀ l : ↥K, ∀ x ∈ M, θ ((l : G) * x * (l : G)⁻¹) = fv5Act (ρ l) (θ x)

namespace OrthCoord

variable {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)} {θ : G → Fv5}

theorem theta_one (hC : OrthCoord K M ρ θ) : θ 1 = 0 := by
  have h := hC.mul 1 M.one_mem 1 M.one_mem
  rw [mul_one] at h
  exact left_eq_add.mp h

theorem theta_ne_zero (hC : OrthCoord K M ρ θ) {x : G} (hx : x ∈ M) (hx1 : x ≠ 1) :
    θ x ≠ 0 := fun h =>
  hx1 (hC.inj x hx 1 M.one_mem (by rw [h, hC.theta_one]))

theorem mul_self_eq_one (hC : OrthCoord K M ρ θ) {x : G} (hx : x ∈ M) : x * x = 1 := by
  refine hC.inj _ (M.mul_mem hx hx) 1 M.one_mem ?_
  rw [hC.mul x hx x hx, hC.theta_one, fv5_add_self]

theorem comm (hC : OrthCoord K M ρ θ) {x y : G} (hx : x ∈ M) (hy : y ∈ M) :
    x * y = y * x := by
  refine hC.inj _ (M.mul_mem hx hy) _ (M.mul_mem hy hx) ?_
  rw [hC.mul x hx y hy, hC.mul y hy x hx, add_comm]

theorem conj_mem (hC : OrthCoord K M ρ θ) (l : ↥K) {x : G} (hx : x ∈ M) :
    (l : G) * x * (l : G)⁻¹ ∈ M := by
  have hxK : x ∈ K := hC.le hx
  have h1 : ρ ⟨x, hxK⟩ = 1 := (hC.ker ⟨x, hxK⟩).mpr hx
  have h2 : ρ (l * ⟨x, hxK⟩ * l⁻¹) = 1 := by
    rw [map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  exact (hC.ker _).mp h2

theorem conj_mem' (hC : OrthCoord K M ρ θ) {k : G} (hk : k ∈ K) {x : G} (hx : x ∈ M) :
    k * x * k⁻¹ ∈ M :=
  hC.conj_mem ⟨k, hk⟩ hx

theorem exists_perm_trans (hC : OrthCoord K M ρ θ) (i j : Fin 5) :
    ∃ l : ↥K, ρ l i = j := by
  obtain ⟨g, hg, hgij⟩ := trans5 i j
  obtain ⟨l, hl⟩ := hC.surj g hg
  exact ⟨l, by rw [hl, hgij]⟩

theorem centralizer_le (hC : OrthCoord K M ρ θ) {l : G} (hl : l ∈ K)
    (hcomm : ∀ x ∈ M, l * x = x * l) : l ∈ M := by
  refine (hC.ker ⟨l, hl⟩).mp ?_
  refine faithful5 _ (hC.sign_eq ⟨l, hl⟩) fun e he => ?_
  obtain ⟨x, hxM, rfl⟩ := hC.exists_eq e he
  rw [← hC.conj ⟨l, hl⟩ x hxM]
  congr 1
  rw [hcomm x hxM]
  group

theorem eq_one_or_eq_of_fix (hC : OrthCoord K M ρ θ) {m c : G} (hm : m ∈ M) (hm1 : m ≠ 1)
    (hc : c ∈ M) (hfix : ∀ l ∈ K, l * m * l⁻¹ = m → l * c * l⁻¹ = c) : c = 1 ∨ c = m := by
  have key : ∀ g : Perm (Fin 5), sign g = 1 → fv5Act g (θ m) = θ m → fv5Act g (θ c) = θ c := by
    intro g hg hgm
    obtain ⟨l, hl⟩ := hC.surj g hg
    have h1 : (l : G) * m * (l : G)⁻¹ = m := by
      refine hC.inj _ (hC.conj_mem l hm) m hm ?_
      rw [hC.conj l m hm, hl]
      exact hgm
    rw [← hl, ← hC.conj l c hc, hfix l l.2 h1]
  rcases fix5 (θ m) (hC.even m hm) (hC.theta_ne_zero hm hm1) (θ c) (hC.even c hc) key with h | h
  · exact Or.inl (hC.inj c hc 1 M.one_mem (by rw [h, hC.theta_one]))
  · exact Or.inr (hC.inj c hc m hm h)

end OrthCoord

end CFSG.EvenSporadicStandard.HNRecog.Section4
