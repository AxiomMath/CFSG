module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1PtsA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Orb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act6

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private theorem y7a_conj_U16 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G)) :
    ∀ x ∈ X, ∀ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V},
      x * u * x⁻¹ ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} := by
  intro x hxX u hu
  refine ⟨(hX1 hxX u).mp hu.1, ?_⟩
  intro hconj
  have hx1' : x⁻¹ ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := hX1 (X.inv_mem hxX)
  have hx2' : x⁻¹ ∈ normalizer (V : Set G) := hX2 (X.inv_mem hxX)
  have hback : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ ∈ A ⊔ V :=
    ((y7a_conj_AV h hx1' hx2') (x * u * x⁻¹)).mp hconj
  exact hu.2 (by convert hback using 1; group)

theorem y7a_psi16 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hall : ∀ w ∈ A ⊔ C0, w ∉ A ⊔ V → w ∈ y7aO X V t) :
    ∃ (ψ : ↥X →* Equiv.Perm (Fin 16)) (lab : G → Fin 16),
      ψ.ker = (CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V).subgroupOf X ∧
      (∀ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}, ∀ u' ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V},
        lab u = lab u' ↔ u⁻¹ * u' ∈ V) ∧
      (∀ i : Fin 16, ∃ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}, lab u = i) ∧
      (∀ x : ↥X, ∀ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V},
        ψ x (lab u) = lab ((x : G) * u * (x : G)⁻¹)) ∧
      lab t = 0 := by
  classical
  obtain ⟨lab₀, hlab₀, hsurj₀⟩ :=
    y6_lab_exists (n := 16) (by norm_num) (y7a_U16_V h) (y7a_card_U16 h)
  have htU : t ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} :=
    ⟨mem_sup_right (y7a_t_mem_C0 h), y7a_t_not_mem_AV h⟩
  let lab : G → Fin 16 := fun w => Equiv.swap (lab₀ t) 0 (lab₀ w)
  have hlab : ∀ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V},
      ∀ u' ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}, lab u = lab u' ↔ u⁻¹ * u' ∈ V := by
    intro u hu u' hu'
    dsimp only [lab]
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_self]
    exact hlab₀ u hu u' hu'
  have hsurj : ∀ i : Fin 16, ∃ u ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V}, lab u = i := by
    intro i
    obtain ⟨u, hu, hu'⟩ := hsurj₀ (Equiv.swap (lab₀ t) 0 i)
    refine ⟨u, hu, ?_⟩
    dsimp only [lab]
    rw [hu', Equiv.swap_apply_self]
  have hXU := y7a_conj_U16 h hX1 hX2
  obtain ⟨ψ, hψ, hψ1⟩ := y6_act_exists hX2 hXU lab hlab hsurj
  refine ⟨ψ, lab, ?_, hlab, hsurj, hψ, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ1 x]
    exact (y6_mem_centSec_iff ((y7a_V_le_C0 h).trans le_sup_right) (y7a_C1_le_N_V h)
      (fun u hu => hu.1) (y7a_gen_U16 h) (hX1 x.property) (hX2 x.property)).symm
  · dsimp only [lab]
    rw [Equiv.swap_apply_left]

theorem y7a_orbit16 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X C : Subgroup G} (hCX : C ≤ X)
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hC : ∀ x ∈ X, x ∈ C ↔ t⁻¹ * (x * t * x⁻¹) ∈ V)
    (hall : ∀ w ∈ A ⊔ C0, w ∉ A ⊔ V → w ∈ y7aO X V t) :
    Nat.card ↥X = 16 * Nat.card ↥C := by
  classical
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (n := 16) (by norm_num) (y7a_U16_V h) (y7a_card_U16 h)
  have htU : t ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} :=
    ⟨mem_sup_right (y7a_t_mem_C0 h), y7a_t_not_mem_AV h⟩
  obtain ⟨ψ, hψ, _hψ1⟩ := y6_act_exists hX2 (y7a_conj_U16 h hX1 hX2) lab hlab hsurj
  refine y6_card_orbit_stab ψ (lab t) ?_ hCX ?_
  · intro j
    obtain ⟨w, hwU, hwlab⟩ := hsurj j
    obtain ⟨x, hxX, hxV⟩ := hall w hwU.1 hwU.2
    refine ⟨⟨x, hxX⟩, ?_⟩
    have hconjU : x * t * x⁻¹ ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} :=
      y7a_conj_U16 h hX1 hX2 x hxX t htU
    have hlab_eq : lab (x * t * x⁻¹) = lab w :=
      (hlab (x * t * x⁻¹) hconjU w hwU).mpr hxV
    calc ψ ⟨x, hxX⟩ (lab t) = lab (x * t * x⁻¹) := hψ ⟨x, hxX⟩ t htU
      _ = lab w := hlab_eq
      _ = j := hwlab
  · intro x
    have hconjU : (x : G) * t * (x : G)⁻¹ ∈ {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ⊔ V} :=
      y7a_conj_U16 h hX1 hX2 (x : G) x.property t htU
    rw [hψ x t htU, hlab ((x : G) * t * (x : G)⁻¹) hconjU t htU, hC (x : G) x.property]
    have hy : ((x : G) * t * (x : G)⁻¹)⁻¹ * t =
        (t⁻¹ * ((x : G) * t * (x : G)⁻¹))⁻¹ := by group
    rw [hy]
    exact V.inv_mem_iff.symm

end CFSG.OddStandard.HigherRank.YamadaG23
