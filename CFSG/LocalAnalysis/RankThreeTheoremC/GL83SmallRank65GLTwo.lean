module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.GroupTheory.PGroup

import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

private theorem gl65_exists_smul_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : Module.finrank K V ≤ 1) (f : V →ₗ[K] V) :
    ∃ r : K, f = r • (1 : V →ₗ[K] V) := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (fun v hv => ?_)
  have h := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  omega

private theorem gl65_commute_of_finrank_le_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (hV : Module.finrank K V ≤ 1) (a b : V ≃ₗ[K] V) :
    a * b = b * a := by
  obtain ⟨r, hr⟩ := gl65_exists_smul_of_finrank_le_one hV (a : V →ₗ[K] V)
  obtain ⟨s, hs⟩ := gl65_exists_smul_of_finrank_le_one hV (b : V →ₗ[K] V)
  have ha : ∀ x, a x = r • x := fun x => by simpa using LinearMap.congr_fun hr x
  have hb : ∀ x, b x = s • x := fun x => by simpa using LinearMap.congr_fun hs x
  ext x
  simp only [LinearEquiv.mul_apply, ha, hb, smul_comm r s]

private theorem gl65_commute_of_span {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c g₁ g₂ : V →ₗ[K] V) (v : V) (hspan : Submodule.span K {v, c v} = ⊤)
    (h₁ : ∀ x, g₁ (c x) = c (g₁ x)) (h₂ : ∀ x, g₂ (c x) = c (g₂ x)) (x : V) :
    g₁ (g₂ x) = g₂ (g₁ x) := by
  have hv : g₁ (g₂ v) = g₂ (g₁ v) := by
    obtain ⟨a₁, b₁, e₁⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top : g₁ v ∈ _)
    obtain ⟨a₂, b₂, e₂⟩ := Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top : g₂ v ∈ _)
    have h12 : g₁ (g₂ v) = a₂ • g₁ v + b₂ • c (g₁ v) := by
      rw [← e₂, map_add, map_smul, map_smul, h₁]
    have h21 : g₂ (g₁ v) = a₁ • g₂ v + b₁ • c (g₂ v) := by
      rw [← e₁, map_add, map_smul, map_smul, h₂]
    rw [h12, h21, ← e₁, ← e₂]
    simp only [map_add, map_smul]
    module
  have hle : Submodule.span K {v, c v} ≤ LinearMap.eqLocus (g₁ ∘ₗ g₂) (g₂ ∘ₗ g₁) := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hv
    · change g₁ (g₂ (c v)) = g₂ (g₁ (c v))
      rw [h₂, h₁, h₁, h₂, hv]
  exact hle (hspan ▸ Submodule.mem_top : x ∈ Submodule.span K {v, c v})

private theorem gl65_sq_eq_one_of_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (hV : Module.finrank K V = 2) (c : V ≃ₗ[K] V) (hdet : LinearEquiv.det c = 1) (r : K)
    (hr : (c : V →ₗ[K] V) = r • (1 : V →ₗ[K] V)) : c ^ 2 = 1 := by
  have h1 : r ^ 2 = 1 := by
    have h := congrArg Units.val hdet
    rw [LinearEquiv.coe_det, hr, LinearMap.det_smul, hV, map_one, mul_one] at h
    simpa using h
  have hc : ∀ x, c x = r • x := fun x => by simpa using LinearMap.congr_fun hr x
  ext x
  rw [pow_two, LinearEquiv.mul_apply, hc, hc, ← mul_smul, ← pow_two, h1, one_smul]
  rfl

theorem gl65_commute_of_isPGroup_three {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V ≤ 2) (S : Subgroup (V ≃ₗ[K] V))
    [Finite S] (hS : IsPGroup 3 S) (a b : V ≃ₗ[K] V) (ha : a ∈ S) (hb : b ∈ S) : a * b = b * a := by
  by_cases h1 : Module.finrank K V ≤ 1
  · exact gl65_commute_of_finrank_le_one h1 a b
  have hV2 : Module.finrank K V = 2 := by omega
  let δ : S →* Kˣ := LinearEquiv.det.comp S.subtype
  by_cases hker : δ.ker = ⊥
  · have hinj : Function.Injective δ := (MonoidHom.ker_eq_bot_iff δ).1 hker
    have h : (⟨a, ha⟩ : S) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      apply hinj
      simp [δ, mul_comm]
    exact congrArg Subtype.val h
  · have : Group.IsNilpotent S := hS.isNilpotent
    obtain ⟨⟨m, hmk, hmc⟩, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hker)
    have hm1' : m ≠ 1 := fun h => hm1 (Subtype.ext h)
    have hdet : LinearEquiv.det (m : V ≃ₗ[K] V) = 1 := MonoidHom.mem_ker.1 hmk
    have hcomm : ∀ g ∈ S, ∀ x, g (m.1 x) = m.1 (g x) := fun g hg x => by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hmc ⟨g, hg⟩)
      exact (LinearEquiv.congr_fun this x)
    have hex : ∃ v, LinearIndependent K ![v, (m : V ≃ₗ[K] V) v] := by
      by_contra hex
      obtain ⟨r, hr⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
        (f := (m : V ≃ₗ[K] V).toLinearMap) fun v hv => hex ⟨v, hv⟩
      have hm2 : m ^ 2 = 1 := Subtype.ext (gl65_sq_eq_one_of_smul hV2 (m : V ≃ₗ[K] V) hdet r hr)
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).1 hS m
      have hdvd : 3 ^ k ∣ 2 := hk ▸ orderOf_dvd_of_pow_eq_one hm2
      have hk0 : 3 ^ k = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k (by norm_num)) hdvd
      exact hm1' (orderOf_eq_one_iff.1 (hk.trans hk0))
    obtain ⟨v, hv⟩ := hex
    have hspan : Submodule.span K {v, (m : V ≃ₗ[K] V) v} = ⊤ := by
      have := hv.span_eq_top_of_card_eq_finrank' (by simp [hV2])
      rwa [Matrix.range_cons_cons_empty] at this
    ext x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact gl65_commute_of_span (m : V ≃ₗ[K] V).toLinearMap a.toLinearMap b.toLinearMap v hspan
      (hcomm a ha) (hcomm b hb) x

end CFSG.LocalAnalysis.RankThreeTheoremC
