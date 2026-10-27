module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Matrix Module CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.OutcomeLocal

theorem isSolvable_centralizer_of_mulEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    {y : Y} (h : Group.IsSolvable (centralizer ({e y} : Set Z))) :
    Group.IsSolvable (centralizer ({y} : Set Y)) := by
  let f : centralizer ({y} : Set Y) →* centralizer ({e y} : Set Z) :=
    (e.toMonoidHom.comp (centralizer ({y} : Set Y)).subtype).codRestrict _ fun c => by
      have hc := mem_centralizer_singleton_iff.mp c.2
      rw [mem_centralizer_singleton_iff]
      change e c * e y = e y * e c
      rw [← map_mul, ← map_mul, hc]
  refine Group.isSolvable_of_isSolvable_injective (f := f) fun a b hab => ?_
  exact Subtype.ext (e.injective (congrArg Subtype.val hab))

variable {K : Type*} [Field K]

theorem mem_stabilizer_inf_of_commute {n : ℕ} {s A : SpecialLinearGroup (Fin n) K}
    (hAs : A * s = s * A) : A ∈ stabilizer (dispRange s) ⊓ stabilizer (dispKer s) := by
  have hAs' : A⁻¹ * s = s * A⁻¹ := by
    calc A⁻¹ * s = A⁻¹ * (s * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * s) * A⁻¹ := by rw [hAs]
      _ = s * A⁻¹ := by group
  obtain ⟨hW, hL⟩ := mapsTo_of_commute hAs
  obtain ⟨hW', hL'⟩ := mapsTo_of_commute hAs'
  have key : ∀ (V : Submodule K (Fin n → K)),
      (∀ v ∈ V, (A : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V) →
      (∀ v ∈ V, ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ V) →
      V.map (mulVecLin (A : Matrix (Fin n) (Fin n) K)) = V := by
    intro V h1 h2
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact h1 v hv
    · intro v hv
      exact ⟨_, h2 v hv, sl_mulVec_inv_mulVec A v⟩
  exact ⟨key _ hW hW', key _ hL hL'⟩

theorem finrank_dispRange_dispKer [CharP K 2] {s : SpecialLinearGroup (Fin 3) K}
    (hs : s * s = 1) (hs1 : s ≠ 1) :
    finrank K (dispRange s) = 1 ∧ finrank K (dispKer s) = 2 := by
  have hsum : finrank K (dispRange s) + finrank K (dispKer s) = 3 := by
    rw [dispRange, dispKer, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]
  have hle : finrank K (dispRange s) ≤ finrank K (dispKer s) :=
    Submodule.finrank_mono (dispRange_le_dispKer hs)
  have h1 : 0 < finrank K (dispRange s) :=
    Nat.pos_of_ne_zero fun h0 => dispRange_ne_bot hs1 (Submodule.finrank_eq_zero.mp h0)
  have h2 : finrank K (dispKer s) < 3 := by
    have := Submodule.finrank_lt (dispKer_ne_top hs1)
    rwa [finrank_fin_fun] at this
  omega

theorem isSolvable_centralizer_projectiveSL_three [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    [CharP K 2] {t : projectiveSL 3 K} (ht : orderOf t = 2) :
    Group.IsSolvable (centralizer ({t} : Set (projectiveSL 3 K))) := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨hW, hL⟩ := finrank_dispRange_dispKer hs hs1
  have hB := LieType.SteinbergBR.isSolvable_stabilizer_inf_stabilizer Nat.prime_two hK
    (dispRange_le_dispKer hs) hW hL
  have hle : centralizer ({proj 3 K s} : Set (projectiveSL 3 K)) ≤
      (stabilizer (dispRange s) ⊓ stabilizer (dispKer s)).map (proj 3 K) := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective 3 K c
    exact ⟨A, mem_stabilizer_inf_of_commute
      (commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)), rfl⟩
  have : Group.IsSolvable ((stabilizer (dispRange s) ⊓ stabilizer (dispKer s)).map (proj 3 K)) :=
    Group.isSolvable_of_surjective
      (f := ((proj 3 K).comp
        (stabilizer (dispRange s) ⊓ stabilizer (dispKer s)).subtype).codRestrict
          _ fun x => ⟨x, x.2, rfl⟩) fun ⟨_, a, ha, rfl⟩ => ⟨⟨a, ha⟩, rfl⟩
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem isSolvable_centralizer_of_lieModel_psl_three {Y : Type} [Group Y] {f : ℕ}
    (h : LieModel Y .PSL 3 2 f) {y : Y} (hy : orderOf y = 2) :
    Group.IsSolvable (centralizer ({y} : Set Y)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hf : 1 ≤ f := (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h).1.2.1
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine isSolvable_centralizer_of_mulEquiv e ?_
  exact isSolvable_centralizer_projectiveSL_three hK (by rw [MulEquiv.orderOf_eq, hy])

end CFSG.LargeExtraspecial.S8
