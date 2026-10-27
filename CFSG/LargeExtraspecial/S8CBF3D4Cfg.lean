module

public import CFSG.LargeExtraspecial.S8CBF3D4Coord
public import CFSG.LargeExtraspecial.S8CBF3D4Long

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup
open scoped commutatorElement

structure A5Config {G : Type*} [Group G] (C : Subgroup G) (s : G) (R N : Subgroup G) : Prop where
  s_mem : s ∈ C
  orderOf_s : orderOf s = 2
  le : N ≤ R
  le_centralizer : R ≤ C ⊓ centralizer ({s} : Set G)
  perfect : ⁅R, R⁆ = R
  normal : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N
  isPGroup : IsPGroup 2 N
  center : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1 ∨ x = s
  commutator : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = s
  nonabelian : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x
  maximal : ∀ H : Subgroup G, N ≤ H → H ≤ R → (∀ r ∈ R, ∀ h ∈ H, r * h * r⁻¹ ∈ H) →
    H = N ∨ H = R
  card : Nat.card R = 60 * Nat.card N
  sq : ∀ c ∈ C ⊓ centralizer ({s} : Set G), ∀ r ∈ R, c ^ 2 * r * (c ^ 2)⁻¹ ∈ R

namespace A5Config

variable {G H : Type*} [Group G] [Group H]

theorem s_mem_N {C : Subgroup G} {s : G} {R N : Subgroup G} (h : A5Config C s R N) : s ∈ N := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian
  rcases h.commutator x hx y hy with h1 | h1
  · exact absurd (commutatorElement_eq_one_iff_mul_comm.1 h1) hxy
  · rw [← h1, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem of_injective {C : Subgroup G} {C' : Subgroup H} {s : G} {R N : Subgroup G}
    (h : A5Config C s R N) (φ : G →* H) (hφ : Function.Injective φ) (hC : C.map φ = C') :
    A5Config C' (φ s) (R.map φ) (N.map φ) := by
  have hcent : ∀ x : G, x ∈ C ⊓ centralizer ({s} : Set G) ↔
      φ x ∈ C' ⊓ centralizer ({φ s} : Set H) := by
    intro x
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hC,
      mem_map_iff_mem hφ, ← map_mul, ← map_mul, hφ.eq_iff]
  have hCφ : ∀ y ∈ C' ⊓ centralizer ({φ s} : Set H), ∃ x, φ x = y := by
    intro y hy
    have hyC : y ∈ C.map φ := by rw [hC]; exact (mem_inf.1 hy).1
    obtain ⟨x, -, rfl⟩ := hyC
    exact ⟨x, rfl⟩
  refine ⟨?_, ?_, map_mono h.le, ?_, ?_, ?_, h.isPGroup.map φ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hC]
    exact mem_map_of_mem φ h.s_mem
  · rw [orderOf_injective φ hφ, h.orderOf_s]
  · rintro _ ⟨r, hr, rfl⟩
    exact (hcent r).1 (h.le_centralizer hr)
  · rw [← map_commutator, h.perfect]
  · rintro _ ⟨r, hr, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨r * n * r⁻¹, h.normal r hr n hn, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩ hxc
    have hx' : ∀ y ∈ N, x * y = y * x := fun y hy => hφ (by
      rw [map_mul, map_mul]
      exact hxc _ ⟨y, hy, rfl⟩)
    rcases h.center x hx hx' with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_commutatorElement]
    rcases h.commutator x hx y hy with h1 | h1
    · exact Or.inl (by rw [h1, map_one])
    · exact Or.inr (by rw [h1])
  · obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian
    refine ⟨φ x, ⟨x, hx, rfl⟩, φ y, ⟨y, hy, rfl⟩, fun he => hxy (hφ ?_)⟩
    rw [map_mul, map_mul]
    exact he
  · intro H' hNH hHR hRH
    have hH : H' = (H'.comap φ).map φ := by
      rw [map_comap_eq, inf_of_le_right (hHR.trans (map_le_range φ R))]
    have h1 := h.maximal (H'.comap φ) (fun n hn => hNH ⟨n, hn, rfl⟩)
      (fun x hx => by
        obtain ⟨r, hr, hrx⟩ := hHR hx
        rw [← hφ hrx]
        exact hr)
      (fun r hr x hx => by
        rw [mem_comap, map_mul, map_mul, map_inv]
        exact hRH _ ⟨r, hr, rfl⟩ _ hx)
    rcases h1 with h1 | h1
    · left
      rw [hH, h1]
    · right
      rw [hH, h1]
  · rw [card_map_of_injective hφ, card_map_of_injective hφ, h.card]
  · intro y hy r' hr'
    obtain ⟨c, rfl⟩ := hCφ y hy
    obtain ⟨r, hr, rfl⟩ := hr'
    have hc := (hcent c).2 hy
    exact ⟨c ^ 2 * r * (c ^ 2)⁻¹, h.sq c hc r hr, by simp⟩

theorem conj {C : Subgroup G} {s : G} {R N : Subgroup G} (h : A5Config C s R N) {g : G}
    (hg : g ∈ C) :
    A5Config C (g * s * g⁻¹) (R.map (MulAut.conj g).toMonoidHom)
      (N.map (MulAut.conj g).toMonoidHom) := by
  have hC : C.map (MulAut.conj g).toMonoidHom = C := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hg hx) (inv_mem hg)
    · intro x hx
      refine ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact h.of_injective _ (MulAut.conj g).injective hC

end A5Config

end CFSG.LargeExtraspecial.S8
