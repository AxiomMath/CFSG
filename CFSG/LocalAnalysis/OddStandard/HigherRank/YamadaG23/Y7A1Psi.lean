module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1PtsB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Orb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act6

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

theorem y7a_O_eq_Up (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hUm : ∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) :
    ∀ w, w ∈ y7aO X V t ↔ w ∈ y6Up A V t := by
  intro w
  constructor
  · intro hw
    obtain ⟨hwC1, hwAV⟩ := y7a_O_sub h hX1 hX2 w hw
    rcases y7a_C1_split h w hwC1 with h1 | h1 | h1
    · exact absurd h1 hwAV
    · exact absurd hw (hUm w h1)
    · exact h1
  · exact hUp w

private lemma y7a_conj_Um (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hUm : ∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) {x u : G} (hx : x ∈ X)
    (hu : u ∈ y6Um A V z t) : x * u * x⁻¹ ∈ y6Um A V z t := by
  obtain ⟨huC1, huAV⟩ := y7a_Um_sub h u hu
  have hxC1 : x * u * x⁻¹ ∈ A ⊔ C0 := (mem_normalizer_iff.mp (hX1 hx) u).mp huC1
  have hxAV : x * u * x⁻¹ ∉ A ⊔ V :=
    fun hconj => huAV ((y7a_conj_AV h (hX1 hx) (hX2 hx) u).mpr hconj)
  have hxO : x * u * x⁻¹ ∉ y7aO X V t := by
    intro hconj
    have hmem := (y7a_O_conj_iff hX2 (X.inv_mem hx)).mpr hconj
    have hkey : x⁻¹ * (x * u * x⁻¹) * (x⁻¹)⁻¹ = u := by group
    rw [hkey] at hmem
    exact hUm u hu hmem
  rcases y7a_C1_split h (x * u * x⁻¹) hxC1 with h1 | h1 | h1
  · exact absurd h1 hxAV
  · exact h1
  · exact absurd ((y7a_O_eq_Up h hX1 hX2 hUp hUm (x * u * x⁻¹)).mpr h1) hxO

private lemma y7a_conj_Up (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hUm : ∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) {x u : G} (hx : x ∈ X)
    (hu : u ∈ y6Up A V t) : x * u * x⁻¹ ∈ y6Up A V t :=
  (y7a_O_eq_Up h hX1 hX2 hUp hUm (x * u * x⁻¹)).mp
    (y7a_O_conj hX2 hx ((y7a_O_eq_Up h hX1 hX2 hUp hUm u).mpr hu))

theorem y7a_psi6 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hUm : ∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) :
    ∃ ψ : ↥X →* Equiv.Perm (Fin 6),
      ψ.ker = (CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V).subgroupOf X := by
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (n := 6) (by norm_num) (y7a_Um_V h) (y7a_card_Um h)
  obtain ⟨ψ, _hψ, hψ1⟩ := y6_act_exists hX2
    (fun x hx u hu => y7a_conj_Um h hX1 hX2 hUp hUm hx hu) lab hlab hsurj
  refine ⟨ψ, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ1 x]
  exact (y6_mem_centSec_iff ((y7a_V_le_C0 h).trans le_sup_right) (y7a_C1_le_N_V h)
    (fun u hu => (y7a_Um_sub h u hu).1) (y7a_gen_Um h) (hX1 x.property)
    (hX2 x.property)).symm

theorem y7a_orbit10 (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {X C : Subgroup G} (hCX : C ≤ X)
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hC : ∀ x ∈ X, x ∈ C ↔ t⁻¹ * (x * t * x⁻¹) ∈ V)
    (hUp : ∀ w ∈ y6Up A V t, w ∈ y7aO X V t)
    (hUm : ∀ w ∈ y6Um A V z t, w ∉ y7aO X V t) :
    Nat.card ↥X = 10 * Nat.card ↥C := by
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (n := 10) (by norm_num) (y7a_Up_V h) (y7a_card_Up h)
  obtain ⟨ψ, hψ, _hψ1⟩ := y6_act_exists hX2
    (fun x hx u hu => y7a_conj_Up h hX1 hX2 hUp hUm hx hu) lab hlab hsurj
  have htU : t ∈ y6Up A V t := y7a_t_mem_Up h
  refine y6_card_orbit_stab ψ (lab t) ?_ hCX ?_
  · intro j
    obtain ⟨w, hwU, hwlab⟩ := hsurj j
    obtain ⟨x, hxX, hxV⟩ := hUp w hwU
    refine ⟨⟨x, hxX⟩, ?_⟩
    have hconjU : x * t * x⁻¹ ∈ y6Up A V t := y7a_conj_Up h hX1 hX2 hUp hUm hxX htU
    have hlab_eq : lab (x * t * x⁻¹) = lab w :=
      (hlab (x * t * x⁻¹) hconjU w hwU).mpr hxV
    calc ψ ⟨x, hxX⟩ (lab t) = lab (x * t * x⁻¹) := hψ ⟨x, hxX⟩ t htU
      _ = lab w := hlab_eq
      _ = j := hwlab
  · intro x
    have hconjU : (x : G) * t * (x : G)⁻¹ ∈ y6Up A V t :=
      y7a_conj_Up h hX1 hX2 hUp hUm x.property htU
    rw [hψ x t htU, hlab ((x : G) * t * (x : G)⁻¹) hconjU t htU, hC (x : G) x.property]
    have hy : ((x : G) * t * (x : G)⁻¹)⁻¹ * t =
        (t⁻¹ * ((x : G) * t * (x : G)⁻¹))⁻¹ := by group
    rw [hy]
    exact V.inv_mem_iff.symm

end CFSG.OddStandard.HigherRank.YamadaG23
