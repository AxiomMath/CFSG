module

public import CFSG.LinearAlgebra.LinearGroups.SubspaceSpecialLinear
import CFSG.LinearAlgebra.ScalarBlockNormalizer
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

public section

namespace Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_scalar_mem_specialLinearEmbedding
    {E P : Submodule K V} (h : IsCompl E P) (a : K) (ha : a ≠ 0)
    (hpow : a ^ Module.finrank K E = 1) :
    ∃ z ∈ (specialLinearEmbedding E P h).range,
      (∀ v ∈ E, z v = a • v) ∧ (∀ v ∈ P, z v = v) ∧
      ∀ t ∈ (specialLinearEmbedding E P h).range, Commute z t := by
  let s : E ≃ₗ[K] E := LinearEquiv.smulOfNeZero K E a ha
  have hs : s.toLinearMap = a • LinearMap.id := by
    ext v
    rfl
  have hdet : s.det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, hs, LinearMap.det_smul, LinearMap.det_id,
      mul_one, hpow]
    rfl
  let g : SpecialLinearGroup K E := ⟨s, hdet⟩
  let beta := specialLinearEmbedding E P h
  refine ⟨beta g, ⟨g, rfl⟩, ?_, ?_, ?_⟩
  · intro v hv
    change beta g ((⟨v, hv⟩ : E) : V) = a • v
    rw [specialLinearEmbedding_apply_left]
    rfl
  · intro v hv
    exact specialLinearEmbedding_apply_right h g ⟨v, hv⟩
  · rintro _ ⟨t, rfl⟩
    have hc : Commute g t := by
      change g * t = t * g
      apply SpecialLinearGroup.ext
      intro v
      change s (t.val v) = t.val (s v)
      simp only [s, LinearEquiv.smulOfNeZero_apply, map_smul]
    exact hc.map beta

theorem normalizer_specialLinearEmbedding_preserves_complements
    {E P : Submodule K V} (h : IsCompl E P) (a : K) (ha0 : a ≠ 0)
    (ha1 : a ≠ 1) (hpow : a ^ Module.finrank K E = 1)
    {f : V ≃ₗ[K] V}
    (hf : f ∈ Subgroup.normalizer
      ((specialLinearEmbedding E P h).range : Set (V ≃ₗ[K] V))) :
    (∀ v ∈ E, f v ∈ E) ∧ (∀ v ∈ P, f v ∈ P) := by
  let beta := specialLinearEmbedding E P h
  let e := prodEquivOfIsCompl E P h
  have hmove : ∀ t ∈ beta.range, ∀ v : V, t v - v ∈ E := by
    rintro _ ⟨g, rfl⟩ v
    obtain ⟨⟨u, w⟩, rfl⟩ := e.surjective v
    change beta g ((u : V) + (w : V)) - ((u : V) + (w : V)) ∈ E
    rw [specialLinearEmbedding_apply_add]
    simpa only [add_sub_add_right_eq_sub] using
      E.sub_mem (g u).property u.property
  have hfix : ∀ t ∈ beta.range, ∀ v ∈ P, t v = v := by
    rintro _ ⟨g, rfl⟩ v hv
    exact specialLinearEmbedding_apply_right h g ⟨v, hv⟩
  obtain ⟨z, hz, hzE, hzP, -⟩ := exists_scalar_mem_specialLinearEmbedding h a ha0 hpow
  exact CFSG.LinearAlgebra.preserves_complements_of_normalizes_scalar_block
    h hmove hfix hz ha1 hzE hzP hf

theorem le_left_or_le_right_of_scalar_invariant_line
    {U W L : Submodule K V} (hUW : Disjoint U W)
    (hL : Module.finrank K L = 1) (hle : L ≤ U ⊔ W)
    {f : V →ₗ[K] V} {a b : K} (hab : a ≠ b)
    (ha : ∀ v ∈ U, f v = a • v) (hb : ∀ v ∈ W, f v = b • v)
    (hf : ∀ v ∈ L, f v ∈ L) : L ≤ U ∨ L ≤ W := by
  obtain ⟨v, hv0, hgen⟩ := finrank_eq_one_iff'.mp hL
  obtain ⟨c, hc⟩ := hgen ⟨f (v : V), hf v v.property⟩
  have heig : f (v : V) = c • (v : V) := (congrArg Subtype.val hc).symm
  obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.mp (hle v.property)
  have hz : (a - c) • u + (b - c) • w = 0 := by
    calc
      (a - c) • u + (b - c) • w =
          (a • u + b • w) - c • (u + w) := by
        simp only [sub_smul, smul_add]
        abel
      _ = 0 := sub_eq_zero.mpr (by rw [← ha u hu, ← hb w hw, ← map_add, hsum]; exact heig)
  have hzero := (Submodule.disjoint_iff_add_eq_zero.mp hUW)
    (U.smul_mem (a - c) hu) (W.smul_mem (b - c) hw) hz
  by_cases hu0 : u = 0
  · right
    intro x hx
    obtain ⟨d, hd⟩ := hgen ⟨x, hx⟩
    have hdx : d • (v : V) = x := congrArg Subtype.val hd
    rw [← hdx, ← hsum, hu0, zero_add]
    exact W.smul_mem d hw
  · have hac : a = c := sub_eq_zero.mp ((smul_eq_zero.mp hzero.1).resolve_right hu0)
    have hbc : b - c ≠ 0 := sub_ne_zero.mpr (by simpa only [← hac] using hab.symm)
    have hw0 : w = 0 := (smul_eq_zero.mp hzero.2).resolve_left hbc
    left
    intro x hx
    obtain ⟨d, hd⟩ := hgen ⟨x, hx⟩
    have hdx : d • (v : V) = x := congrArg Subtype.val hd
    rw [← hdx, ← hsum, hw0, add_zero]
    exact U.smul_mem d hu

end Submodule

end
