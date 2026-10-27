module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPreimage
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G]

open SuzukiAut CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.MatrixGroups in
theorem inv_mul_mem_sylowCenter_of_commute_of_sz {X : Type*} [Group X] [Finite X] {a : ℕ}
    (ha : 1 ≤ a) (e : X ≃* Sz a) (R : Sylow 2 X) {x x' : X} (hx : x ∈ (R : Subgroup X))
    (hx' : x' ∈ (R : Subgroup X)) (hxx : x * x' = x' * x)
    (hxZ : x ∉ sylowCenter (R : Subgroup X)) (hx'Z : x' ∉ sylowCenter (R : Subgroup X)) :
    x⁻¹ * x' ∈ sylowCenter (R : Subgroup X) := by
  classical
  set e' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm with he'
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e' e'.surjective
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_rootSub a (by omega)
  set S : Sylow 2 (SuzukiMatrixGroup a) := R.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hS : (S : Subgroup (SuzukiMatrixGroup a)) = (R : Subgroup X).map e'.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup a) S₀ S
  have hmem : ∀ s, s ∈ (S : Subgroup (SuzukiMatrixGroup a)) ↔ g⁻¹ * s * g ∈ rootSub a := by
    intro s
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS₀]
    simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  have hR : ∀ y ∈ (R : Subgroup X), g⁻¹ * e' y * g ∈ rootSub a := fun y hy =>
    (hmem _).mp (hS ▸ ⟨y, hy, rfl⟩)
  have hcen : ∀ z ∈ (R : Subgroup X), ∀ w, g⁻¹ * e' z * g = root a 0 w →
      z ∈ sylowCenter (R : Subgroup X) := by
    intro z hz w hzw
    have hzc : root a 0 w ∈ sylowCenter (rootSub a) :=
      (mem_sylowCenter_rootSub a (by omega)).mpr ⟨_, rfl⟩
    refine mem_sylowCenter.mpr ⟨hz, fun t ht => e'.injective ?_⟩
    have hc := (mem_sylowCenter.mp hzc).2 _ (hR t ht)
    rw [← hzw] at hc
    simp only [map_mul]
    calc e' t * e' z = g * ((g⁻¹ * e' t * g) * (g⁻¹ * e' z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * e' z * g) * (g⁻¹ * e' t * g)) * g⁻¹ := by rw [hc]
      _ = e' z * e' t := by group
  obtain ⟨u, v, huv⟩ := (mem_rootSub a).mp (hR x hx)
  obtain ⟨u', v', huv'⟩ := (mem_rootSub a).mp (hR x' hx')
  have hu : u ≠ 0 := fun h => hxZ (hcen x hx v (by rw [huv, h]))
  have hu' : u' ≠ 0 := fun h => hx'Z (hcen x' hx' v' (by rw [huv', h]))
  have hxx' : e' x * e' x' = e' x' * e' x := by rw [← map_mul, ← map_mul, hxx]
  have hc : root a u v * root a u' v' = root a u' v' * root a u v := by
    rw [← huv, ← huv']
    calc g⁻¹ * e' x * g * (g⁻¹ * e' x' * g) = g⁻¹ * (e' x * e' x') * g := by group
      _ = g⁻¹ * (e' x' * e' x) * g := by rw [hxx']
      _ = g⁻¹ * e' x' * g * (g⁻¹ * e' x * g) := by group
  rw [root_mul a (by omega), root_mul a (by omega)] at hc
  have h1 : u * tits a u' = u' * tits a u := by
    have h := (root_injective a hc).2
    rw [add_comm v v'] at h
    exact add_left_cancel h
  have h2 := congrArg (tits a) h1
  rw [map_mul, map_mul, tits_tits, tits_tits] at h2
  have h3 : tits a u * u * u' * (u' - u) = 0 := by linear_combination u * h2 + u ^ 2 * h1
  have htu : tits a u ≠ 0 := (map_ne_zero (tits a)).mpr hu
  have huu : u' = u := by
    rcases mul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h htu
        · exact absurd h hu
      · exact absurd h hu'
    · exact sub_eq_zero.mp h
  rw [huu] at huv'
  have hz : (g⁻¹ * e' x * g)⁻¹ * (g⁻¹ * e' x' * g) = root a 0 (v + v') := by
    rw [huv, huv', inv_mul_eq_iff_eq_mul, root_mul a (by omega)]
    have e1 : u + 0 = u := add_zero u
    have e2 : v + (v + v') + u * tits a 0 = v' := by
      rw [map_zero, mul_zero, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [e1, e2]
  refine hcen _ (mul_mem (inv_mem hx) hx') (v + v') ?_
  rw [← hz]
  simp only [map_mul, map_inv]
  group

end CFSG.ComponentClassification.GMS78
