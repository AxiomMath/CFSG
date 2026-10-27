module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Lin2

variable {G : Type} [Group G] [Finite G]

theorem natCard_commutator_eq_card_add_one {V X : Subgroup G}
    (hreg : ActsRegularlyOn X (nonIdentity ⁅V, X⁆)) (hne : ⁅V, X⁆ ≠ ⊥) :
    Nat.card ↥⁅V, X⁆ = Nat.card X + 1 := by
  classical
  have hΔne : (nonIdentity ⁅V, X⁆).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    refine hne (le_bot_iff.mp fun z hz => ?_)
    by_contra hz1
    have hmem : z ∈ nonIdentity ⁅V, X⁆ := ⟨hz, by simpa using hz1⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨z₀, hz₀⟩ := hΔne
  haveI : Nonempty ↥(nonIdentity ⁅V, X⁆) := ⟨⟨z₀, hz₀⟩⟩
  have hf : Function.Bijective (fun x : X =>
      (⟨(x : G)⁻¹ * z₀ * (x : G), hreg.1 x x.2 z₀ hz₀⟩ :
        ↥(nonIdentity ⁅V, X⁆))) := by
    constructor
    · intro x y hxy
      have h' : (x : G)⁻¹ * z₀ * (x : G) = (y : G)⁻¹ * z₀ * (y : G) := by
        simpa using congrArg Subtype.val hxy
      have hfix : ((x : G) * (y : G)⁻¹)⁻¹ * z₀ * ((x : G) * (y : G)⁻¹) = z₀ := by
        calc ((x : G) * (y : G)⁻¹)⁻¹ * z₀ * ((x : G) * (y : G)⁻¹)
            = (y : G) * ((x : G)⁻¹ * z₀ * (x : G)) * (y : G)⁻¹ := by group
          _ = (y : G) * ((y : G)⁻¹ * z₀ * (y : G)) * (y : G)⁻¹ := by rw [h']
          _ = z₀ := by group
      have h1 := hreg.2.2 z₀ hz₀ ((x : G) * (y : G)⁻¹)
        (X.mul_mem x.2 (X.inv_mem y.2)) hfix
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    · rintro ⟨z, hz⟩
      obtain ⟨b, hb, hbz⟩ := hreg.2.1 z₀ hz₀ z hz
      exact ⟨⟨b, hb⟩, Subtype.ext hbz⟩
  have h1 : Nat.card X = Nat.card ↥(nonIdentity ⁅V, X⁆) :=
    Nat.card_congr (Equiv.ofBijective _ hf)
  have h2 : Nat.card ↥(nonIdentity ⁅V, X⁆) = Nat.card ↥⁅V, X⁆ - 1 := by
    have e1 : nonIdentity ⁅V, X⁆ = ((⁅V, X⁆ : Subgroup G) : Set G) \ {1} := by
      ext z
      simp [nonIdentity]
    rw [Nat.card_coe_set_eq, e1, Set.ncard_sdiff_singleton_of_mem (⁅V, X⁆).one_mem,
      ← Nat.card_coe_set_eq]
    rfl
  have hpos : 0 < Nat.card ↥(nonIdentity ⁅V, X⁆) := Nat.card_pos
  omega


theorem exists_relIndex_two_le_of_rk {W : Type} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (hWne : (⊤ : Subgroup W) ≠ ⊥) {A : Subgroup W}
    (hA : rk W ≤ rk A + 1) :
    ∃ H : Subgroup W, H ≤ A ∧ H.relIndex ⊤ = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWpg : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW2
  by_cases hAW : A = ⊤
  · subst hAW
    have hnt : (⊥ : Subgroup W) ≠ ⊤ := fun h => hWne h.symm
    obtain ⟨H, hHc, -⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup W)).resolve_left hnt
    refine ⟨H, le_top, ?_⟩
    have hidx : H.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hWpg).1 hHc
    rwa [Subgroup.relIndex_top_right]
  · obtain ⟨i, hi⟩ := hWpg.index A
    have hrkIdx : rkIdx A = i := by
      unfold rkIdx
      rw [hi, padicValNat.prime_pow]
    have hi0 : i ≠ 0 := by
      intro h0
      have h1 : A.index = 1 := by rw [hi, h0, pow_zero]
      exact hAW (Subgroup.index_eq_one.mp h1)
    have hle1 : rkIdx A ≤ 1 := by
      have h1 := rk_add_rkIdx A
      omega
    have hrkIdx1 : rkIdx A = 1 := by omega
    refine ⟨A, le_rfl, ?_⟩
    rw [Subgroup.relIndex_top_right, hi, ← hrkIdx, hrkIdx1, pow_one]


end CFSG.GroupTheory
