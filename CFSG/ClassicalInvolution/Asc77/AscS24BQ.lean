module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace S24B

variable {G : Type} [Group G] [Finite G]

theorem mem_or_inv_mul_mem {R₀ : Subgroup G} {x s₀ : G} (hU : Subgroup.zpowers x ≤ R₀)
    (hcard : Nat.card ↥R₀ = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs₀ : s₀ ∈ R₀)
    (hs₀U : s₀ ∉ Subgroup.zpowers x) {y : G} (hy : y ∈ R₀) :
    y ∈ Subgroup.zpowers x ∨ s₀⁻¹ * y ∈ Subgroup.zpowers x := by
  by_cases h : y ∈ Subgroup.zpowers x
  · exact Or.inl h
  · exact Or.inr (Thompson.inv_mul_mem_of_card_eq_two_mul hU hcard hs₀ hy hs₀U h)

theorem commute_of_index_two {R₀ : Subgroup G} {x s₀ : G} (hU : Subgroup.zpowers x ≤ R₀)
    (hcard : Nat.card ↥R₀ = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs₀ : s₀ ∈ R₀)
    (hs₀U : s₀ ∉ Subgroup.zpowers x) {a : G} (hax : a * x = x * a) (has : a * s₀ = s₀ * a) :
    R₀ ≤ Subgroup.centralizer ({a} : Set G) := by
  have hxc : Subgroup.zpowers x ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hax.symm
  intro y hy
  rcases mem_or_inv_mul_mem hU hcard hs₀ hs₀U hy with h | h
  · exact hxc h
  · have hs : s₀ ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr has.symm
    have e : y = s₀ * (s₀⁻¹ * y) := by group
    rw [e]
    exact Subgroup.mul_mem _ hs (hxc h)

omit [Finite G] in
theorem zpowers_le_centralizer {x a : G} (ha : a ∈ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.zpowers x ≤ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp ha).symm

theorem qHom_mem {R₀ : Subgroup G} {x s₀ : G} (hU : Subgroup.zpowers x ≤ R₀)
    (hcard : Nat.card ↥R₀ = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs₀ : s₀ ∈ R₀)
    (hs₀U : s₀ ∉ Subgroup.zpowers x) {a : G} (haN : a ∈ Subgroup.normalizer (R₀ : Set G))
    (haC : a ∈ Subgroup.centralizer ({x} : Set G)) :
    s₀⁻¹ * (a * s₀ * a⁻¹) ∈ Subgroup.zpowers x := by
  have h1 : a * s₀ * a⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp haN s₀).mp hs₀
  have h2 : a * s₀ * a⁻¹ ∉ Subgroup.zpowers x := by
    intro h
    apply hs₀U
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (zpowers_le_centralizer haC h)
    have e : s₀ = a * s₀ * a⁻¹ := by
      calc s₀ = a⁻¹ * ((a * s₀ * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * s₀ * a⁻¹)) := by rw [hc]
        _ = a * s₀ * a⁻¹ := by group
    rw [e]
    exact h
  exact Thompson.inv_mul_mem_of_card_eq_two_mul hU hcard hs₀ h1 hs₀U h2

@[expose] noncomputable def qHom {R₀ X : Subgroup G} {x s₀ : G} (hU : Subgroup.zpowers x ≤ R₀)
    (hcard : Nat.card ↥R₀ = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs₀ : s₀ ∈ R₀)
    (hs₀U : s₀ ∉ Subgroup.zpowers x) (hXN : X ≤ Subgroup.normalizer (R₀ : Set G))
    (hXC : X ≤ Subgroup.centralizer ({x} : Set G)) : ↥X →* ↥(Subgroup.zpowers x) :=
  MonoidHom.mk' (fun a => ⟨s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹),
      qHom_mem hU hcard hs₀ hs₀U (hXN a.2) (hXC a.2)⟩)
    (fun a b => by
      apply Subtype.ext
      have hβ := qHom_mem hU hcard hs₀ hs₀U (hXN b.2) (hXC b.2)
      have hc := Subgroup.mem_centralizer_singleton_iff.mp
        (zpowers_le_centralizer (hXC a.2) hβ)
      change s₀⁻¹ * ((a : G) * b * s₀ * ((a : G) * b)⁻¹) =
        s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹) * (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹))
      calc s₀⁻¹ * ((a : G) * b * s₀ * ((a : G) * b)⁻¹)
          = s₀⁻¹ * (a : G) * s₀ * ((s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹)) * (a : G)⁻¹) := by group
        _ = s₀⁻¹ * (a : G) * s₀ * ((a : G)⁻¹ * (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹))) := by
          congr 1
          calc (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹)) * (a : G)⁻¹
              = (a : G)⁻¹ * ((a : G) * (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹))) * (a : G)⁻¹ := by
                group
            _ = (a : G)⁻¹ * ((s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹)) * (a : G)) * (a : G)⁻¹ := by
                rw [← hc]
            _ = (a : G)⁻¹ * (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹)) := by group
        _ = s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹) * (s₀⁻¹ * ((b : G) * s₀ * (b : G)⁻¹)) := by
          group)

theorem qHom_eq_one_iff {R₀ X : Subgroup G} {x s₀ : G} (hU : Subgroup.zpowers x ≤ R₀)
    (hcard : Nat.card ↥R₀ = 2 * Nat.card ↥(Subgroup.zpowers x)) (hs₀ : s₀ ∈ R₀)
    (hs₀U : s₀ ∉ Subgroup.zpowers x) (hXN : X ≤ Subgroup.normalizer (R₀ : Set G))
    (hXC : X ≤ Subgroup.centralizer ({x} : Set G)) (a : ↥X) :
    qHom hU hcard hs₀ hs₀U hXN hXC a = 1 ↔ R₀ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
  constructor
  · intro h
    have h1 : s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹) = 1 := congrArg Subtype.val h
    have h2 : (a : G) * s₀ = s₀ * a := by
      calc (a : G) * s₀ = s₀ * (s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹)) * a := by group
        _ = s₀ * a := by rw [h1, mul_one]
    exact commute_of_index_two hU hcard hs₀ hs₀U
      (Subgroup.mem_centralizer_singleton_iff.mp (hXC a.2)) h2
  · intro h
    apply Subtype.ext
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (h hs₀)
    change s₀⁻¹ * ((a : G) * s₀ * (a : G)⁻¹) = 1
    rw [← h2]; group

end S24B

end CFSG.ClassicalInvolution.Asc77
