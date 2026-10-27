module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.MSide
import CFSG.LocalAnalysis.RankFourTheoremC.PPointAbelianAux
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoPElements

public section

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_perfect_le [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    ∀ J : Subgroup G, J ≤ centralizer ({x} : Set G) → ⁅J, J⁆ = J → J ≤ layerOf x := by
  intro J hJ hJp
  obtain ⟨_, n, hn, ⟨e⟩⟩ := hl.layer
  have h5 : 5 ≤ p := hl.p5
  have hpodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hFcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hcard : 3 < Nat.card (GaloisField p n) := by
    rw [hFcard]
    exact lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  have hout : IsMulCommutative (Outer (layerOf x)) :=
    isMulCommutative_outer_of_mulEquiv_psl2 (GaloisField p n) hpodd (by omega) hFcard hcard e
  have hZL : ∀ l : layerOf x, (∀ m : layerOf x, m * l = l * m) → l = 1 := fun l hl' =>
    Subtype.ext (CFSG.LocalAnalysis.RankThreeTheoremC.eq_one_of_commute_of_mulEquiv_psl_two e l.2
      fun h hh => congrArg Subtype.val (hl' ⟨h, hh⟩))
  have hinj : Function.Injective (MulAut.conj : layerOf x →* MulAut (layerOf x)) := by
    rw [injective_iff_map_eq_one]
    intro l hl'
    refine hZL l fun m => ?_
    have h := congrArg (fun φ : MulAut (layerOf x) => φ m) hl'
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hJN : J ≤ normalizer ((layerOf x : Subgroup G) : Set G) :=
    hJ.trans (fr_layer_normal_in_centralizer x)
  let ρ : J →* MulAut (layerOf x) := (layerOf x).normalizerMonoidHom.comp (Subgroup.inclusion hJN)
  have : Group.IsPerfect J := Subgroup.isPerfect_iff.mpr hJp
  have hρ : ∀ j : J, ρ j ∈ (MulAut.conj : layerOf x →* MulAut (layerOf x)).range := fun j => by
    obtain ⟨g, hg⟩ := perfect_action_inner ρ j
    exact ⟨g, hg.symm⟩
  let ℓ : J →* layerOf x :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (ρ.codRestrict _ hρ)
  have hℓ : ∀ j : J, ∀ m ∈ layerOf x,
      (ℓ j : G) * m * (ℓ j : G)⁻¹ = (j : G) * m * (j : G)⁻¹ := by
    intro j m hm
    have h : MulAut.conj (ℓ j) = ρ j := by
      have h0 := congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply
        (ρ.codRestrict _ hρ j))
      rw [MonoidHom.ofInjective_apply] at h0
      exact h0
    have h2 := congrArg (fun φ : MulAut (layerOf x) => ((φ ⟨m, hm⟩ : layerOf x) : G)) h
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [h2]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hμ : ∀ j : J, (ℓ j : G)⁻¹ * j ∈ centralizer ((layerOf x : Subgroup G) : Set G) := by
    intro j
    rw [mem_centralizer_iff]
    intro m hm
    have h2 := hℓ j m hm
    calc m * ((ℓ j : G)⁻¹ * j) = (ℓ j : G)⁻¹ * ((ℓ j : G) * m * (ℓ j : G)⁻¹) * j := by group
      _ = (ℓ j : G)⁻¹ * ((j : G) * m * (j : G)⁻¹) * j := by rw [h2]
      _ = (ℓ j : G)⁻¹ * j * m := by group
  let μ : J →* centralizer ((layerOf x : Subgroup G) : Set G) :=
    MonoidHom.mk' (fun j => ⟨(ℓ j : G)⁻¹ * j, hμ j⟩) fun a b => by
      apply Subtype.ext
      have hc : (ℓ b : G)⁻¹ * ((ℓ a : G)⁻¹ * a) = (ℓ a : G)⁻¹ * a * (ℓ b : G)⁻¹ :=
        mem_centralizer_iff.mp (hμ a) _ (inv_mem (ℓ b).2)
      simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
      calc (ℓ b : G)⁻¹ * (ℓ a : G)⁻¹ * (a * b) = (ℓ b : G)⁻¹ * ((ℓ a : G)⁻¹ * a) * b := by
            group
        _ = (ℓ a : G)⁻¹ * a * (ℓ b : G)⁻¹ * b := by rw [hc]
        _ = (ℓ a : G)⁻¹ * a * ((ℓ b : G)⁻¹ * b) := by group
  have : Group.IsSolvable (centralizer ((layerOf x : Subgroup G) : Set G)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (fr_centralizer_layer_odd hG hl)
  have hμ1 : μ = 1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one μ
  intro j hj
  have h1 : μ ⟨j, hj⟩ = 1 := by
    rw [hμ1]
    rfl
  have h2 : (ℓ ⟨j, hj⟩ : G)⁻¹ * j = 1 := congrArg Subtype.val h1
  rw [inv_mul_eq_one] at h2
  exact h2 ▸ (ℓ ⟨j, hj⟩).2

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
