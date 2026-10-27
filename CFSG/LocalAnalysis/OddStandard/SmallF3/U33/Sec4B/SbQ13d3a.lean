module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem charIn_of_unique_normal_elemAb {H X : Subgroup G} (hXH : X ≤ H)
    (hX : CFSG.Open.IsElemAbelian 2 X) (hXn : NormalIn X H)
    (huniq : ∀ Y : Subgroup G, NormalIn Y H → CFSG.Open.IsElemAbelian 2 Y →
      Nat.card Y = Nat.card X → Y = X) :
    CharIn X H := by
  refine ⟨hXH, ?_⟩
  rw [Subgroup.characteristic_iff_map_le]
  intro φ z hz
  rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
  let X₀ : Subgroup ↥H := X.subgroupOf H
  let N₁ : Subgroup ↥H := X₀.map φ.toMonoidHom
  let F : Subgroup G := N₁.map H.subtype
  have hX₀normal : X₀.Normal :=
    (Subgroup.normal_subgroupOf_iff hXH).mpr fun h k hh hk => hXn.2 k hk h hh
  have hN₁normal : N₁.Normal := Subgroup.Normal.map hX₀normal φ.toMonoidHom φ.surjective
  have hF : NormalIn F H := by
    refine ⟨Subgroup.map_subtype_le N₁, ?_⟩
    intro g hg k hk
    rcases Subgroup.mem_map.mp hk with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hN₁normal.conj_mem y hy ⟨g, hg⟩, ?_⟩
    rfl
  have hFe : CFSG.Open.IsElemAbelian 2 F := by
    have h1 : CFSG.Open.IsElemAbelian 2 (X.subgroupOf H) := hX.subgroupOf H
    have h2 : CFSG.Open.IsElemAbelian 2 N₁ := h1.map φ.toMonoidHom
    exact h2.map H.subtype
  have hFcard : Nat.card F = Nat.card X := by
    have h1 : Nat.card F = Nat.card N₁ :=
      Subgroup.card_map_of_injective (K := N₁) H.subtype_injective
    have h2 : Nat.card N₁ = Nat.card X₀ :=
      Subgroup.card_map_of_injective (K := X₀) (f := φ.toMonoidHom) φ.injective
    have h3 : Nat.card X₀ = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
    rw [h1, h2, h3]
  have hFX : F = X := huniq F hF hFe hFcard
  have hmemN₁ : φ x ∈ N₁ := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hmemF : ((φ x : ↥H) : G) ∈ F := Subgroup.mem_map.mpr ⟨φ x, hmemN₁, rfl⟩
  rw [hFX] at hmemF
  show ((φ x : ↥H) : G) ∈ X
  exact hmemF

private theorem subgroupOf_inf_centralizer {H K : Subgroup G} (hKH : K ≤ H) :
    (H ⊓ centralizer (K : Set G)).subgroupOf H =
      Subgroup.centralizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hx⟩ y hy
    apply Subtype.ext
    exact hx (y : G) (Subgroup.mem_subgroupOf.mp hy)
  · intro hx
    refine ⟨x.2, ?_⟩
    intro n hn
    have hy : (⟨n, hKH hn⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hn
    have h := hx ⟨n, hKH hn⟩ hy
    have h' := congrArg (fun z : ↥H => (z : G)) h
    simpa using h'

theorem q13d_N_char_U (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    CharIn (ctxN tau x₁ x₂) (ctxU t tau x₁ x₂ lam) := by
  have hBU : Q13B t x₁ x₂ tau (ctxU t tau x₁ x₂ lam) :=
    hB (ctxU t tau x₁ x₂ lam) (q13b_isPGroup_U h) le_rfl
  exact charIn_of_unique_normal_elemAb (q13d_N_le_U h) (q13b_N_elemAbelian h)
    (q13b_N_normal_U h)
    (fun Y hY hYe hYc => hBU.N_unique Y hY hYe (hYc.trans (q13b_card_N h)))

theorem q13d_cent_N_char_U (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    CharIn (ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) :
      Set G)) (ctxU t tau x₁ x₂ lam) := by
  haveI : ((ctxN tau x₁ x₂).subgroupOf (ctxU t tau x₁ x₂ lam)).Characteristic :=
    (q13d_N_char_U h hB).2
  refine ⟨inf_le_left, ?_⟩
  rw [subgroupOf_inf_centralizer (q13d_N_le_U h)]
  exact inferInstance

theorem q13d_E0_char_U (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hB : Q13Bs t x₁ x₂ lam tau) :
    CharIn (q13E0 t tau x₁ x₂ rho om) (ctxU t tau x₁ x₂ lam) := by
  rw [← q13d_E0_eq h]
  exact q13d_cent_N_char_U h hB

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
