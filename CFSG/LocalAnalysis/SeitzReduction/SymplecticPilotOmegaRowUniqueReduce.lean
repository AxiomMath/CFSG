module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)

section Torus

variable {K : Type} [Field K] {n : ℕ}

theorem fieldSp_diagSp (σ : K ≃+* K) (t : Fin n → Kˣ) :
    fieldSp n K σ (diagSp K n t) =
      diagSp K n (fun i => Units.map (σ : K →* K) (t i)) := by
  apply mat_injective
  change (mat n K (diagSp K n t)).map σ = _
  rw [mat_diagSp, mat_diagSp, diagonal_map (map_zero σ)]
  congr 1
  funext a
  rcases a with i | i
  · simp [diagSpEntry]
  · simp [diagSpEntry, map_inv₀]

theorem fieldSp_mem_leviTorusSp (σ : K ≃+* K) {J : Finset (Fin n)} {x : StatedSp n K}
    (hx : x ∈ leviTorusSp K J) : fieldSp n K σ x ∈ leviTorusSp K J := by
  obtain ⟨t, ht, rfl⟩ := hx
  rw [fieldSp_diagSp]
  refine diagSp_mem_leviTorusSp fun j hj => ⟨fun h => ?_, fun h => ?_⟩
  · simp only [(ht j hj).1 h]
  · simp only [(ht j hj).2 h, map_one]

end Torus

theorem exists_conj_eq_of_mul_self_of_odd {G : Type*} [Group G] {t z : G} (htt : t * t = 1)
    (hz : Odd (orderOf z)) (hw : (t * z) * (t * z) = 1) :
    ∃ k : ℕ, t * z = z ^ k * t * (z ^ k)⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hinv : t * z * t⁻¹ = z⁻¹ := by
    rw [htinv]
    calc t * z * t = ((t * z) * (t * z)) * z⁻¹ := by group
      _ = z⁻¹ := by rw [hw, one_mul]
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  have hzm : z ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one z
  have hconj : t⁻¹ * z ^ k * t = (z⁻¹) ^ k := by
    rw [← hinv, conj_pow, htinv]
  have h1 : z ^ k * t = t * (z⁻¹) ^ k := by
    calc z ^ k * t = t * (t⁻¹ * z ^ k * t) := by group
      _ = t * (z⁻¹) ^ k := by rw [hconj]
  have h2 : (z ^ (2 * k))⁻¹ = z := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ, hzm]
  calc t * z = t * (z ^ (2 * k))⁻¹ := by rw [h2]
    _ = t * (z ^ k)⁻¹ * (z ^ k)⁻¹ := by rw [two_mul, pow_add, _root_.mul_inv_rev, mul_assoc]
    _ = t * (z⁻¹) ^ k * (z ^ k)⁻¹ := by rw [inv_pow]
    _ = z ^ k * t * (z ^ k)⁻¹ := by rw [h1]

@[expose] def SpOmegaStepOneInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpOmegaRowGlobal e t f κ →
      ∀ (g : G) (hg : g⁻¹ * t * g ∈ normalizer (spGlobal e : Set G)),
        (spGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hg⟩ ∉
          (MulAut.conj : spGlobal e →* MulAut (spGlobal e)).range

end CFSG.SeitzReduction.SymplecticPilot
