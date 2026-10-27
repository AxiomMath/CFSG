module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Act
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Inv
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6PtsB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

theorem y6_card_orbit_stab {X C : Subgroup G} {n : ℕ} (ψ : ↥X →* Equiv.Perm (Fin n)) (i : Fin n)
    (hsurj : ∀ j : Fin n, ∃ x : ↥X, ψ x i = j) (hCX : C ≤ X)
    (hC : ∀ x : ↥X, (x : G) ∈ C ↔ ψ x i = i) : Nat.card ↥X = n * Nat.card ↥C := by
  let _ : MulAction ↥X (Fin n) := MulAction.compHom (Fin n) ψ
  have hst : MulAction.stabilizer ↥X i = C.subgroupOf X := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change ψ x • i = i ↔ (x : G) ∈ C
    rw [Equiv.Perm.smul_def]
    exact (hC x).symm
  have htrans : MulAction.orbit ↥X i = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    obtain ⟨x, hx⟩ := hsurj j
    exact ⟨x, hx⟩
  have hcard : Nat.card ↥(C.subgroupOf X) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  rw [← Subgroup.card_mul_index (MulAction.stabilizer ↥X i), MulAction.index_stabilizer, htrans,
    Set.ncard_univ, hst, hcard, Nat.card_fin, Nat.mul_comm]

theorem y6_psi6 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {X : Subgroup G}
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G)) :
    ∃ ψ : ↥X →* Equiv.Perm (Fin 6),
      ψ.ker = (CFSG.GH74.GLS.centralizerSection (A ⊔ C0) V).subgroupOf X := by
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (n := 6) (by norm_num) (y6_Um_V h) (y6_card_Um h)
  obtain ⟨ψ, _hψ, hψ1⟩ := y6_act_exists hX2
    (fun x hx u hu => y6_conj_Um h (hX1 hx) (hX2 hx) u hu) lab hlab hsurj
  refine ⟨ψ, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hψ1 x]
  exact (y6_mem_centSec_iff ((y6_V_le_C0 h).trans le_sup_right) (y6_C1_le_N_V h)
    (fun u hu => (y6_Um_sub h u hu).1) (y6_gen_Um h) (hX1 x.property)
    (hX2 x.property)).symm

theorem y6_orbit10 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {X C : Subgroup G} (hCX : C ≤ X)
    (hX1 : X ≤ normalizer ((A ⊔ C0 : Subgroup G) : Set G)) (hX2 : X ≤ normalizer (V : Set G))
    (hC : ∀ x ∈ X, x ∈ C ↔ t⁻¹ * (x * t * x⁻¹) ∈ V)
    (htrans : ∀ w ∈ y6Up A V t, ∃ x ∈ X, (x * t * x⁻¹)⁻¹ * w ∈ V) :
    Nat.card ↥X = 10 * Nat.card ↥C := by
  obtain ⟨lab, hlab, hsurj⟩ :=
    y6_lab_exists (n := 10) (by norm_num) (y6_Up_V h) (y6_card_Up h)
  obtain ⟨ψ, hψ, _hψ1⟩ := y6_act_exists hX2
    (fun x hx u hu => y6_conj_Up h (hX1 hx) (hX2 hx) u hu) lab hlab hsurj
  have htU : t ∈ y6Up A V t := ⟨1, A.one_mem, by simp, 1, V.one_mem, by simp⟩
  refine y6_card_orbit_stab ψ (lab t) ?_ hCX ?_
  · intro j
    obtain ⟨w, hwU, hwlab⟩ := hsurj j
    obtain ⟨x, hxX, hxV⟩ := htrans w hwU
    refine ⟨⟨x, hxX⟩, ?_⟩
    have hconjU : x * t * x⁻¹ ∈ y6Up A V t :=
      y6_conj_Up h (hX1 hxX) (hX2 hxX) t htU
    have hlab_eq : lab (x * t * x⁻¹) = lab w :=
      (hlab (x * t * x⁻¹) hconjU w hwU).mpr hxV
    calc ψ ⟨x, hxX⟩ (lab t) = lab (x * t * x⁻¹) := hψ ⟨x, hxX⟩ t htU
      _ = lab w := hlab_eq
      _ = j := hwlab
  · intro x
    have hconjU : (x : G) * t * (x : G)⁻¹ ∈ y6Up A V t :=
      y6_conj_Up h (hX1 x.property) (hX2 x.property) t htU
    rw [hψ x t htU, hlab ((x : G) * t * (x : G)⁻¹) hconjU t htU, hC (x : G) x.property]
    have hy : ((x : G) * t * (x : G)⁻¹)⁻¹ * t =
        (t⁻¹ * ((x : G) * t * (x : G)⁻¹))⁻¹ := by group
    rw [hy]
    exact V.inv_mem_iff.symm

end CFSG.OddStandard.HigherRank.YamadaG23
