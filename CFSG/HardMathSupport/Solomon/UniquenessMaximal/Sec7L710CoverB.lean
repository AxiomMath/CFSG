module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open scoped Pointwise

variable {H : Type} [Group H]

theorem not_two_dvd_relIndex_of_sup [Finite H] {N A M : Subgroup H} [N.Normal]
    (hN : ¬ 2 ∣ Nat.card N) (hM : A ⊔ N = M) : ¬ 2 ∣ A.relIndex M := by
  have hAM : A ≤ M := hM ▸ le_sup_left
  have hNM : N ≤ M := hM ▸ le_sup_right
  have h1 : N.relIndex M = N.relIndex A := by
    rw [← hM]; exact Subgroup.relIndex_sup_right A N
  have h2 := Subgroup.relIndex_mul_relIndex (A ⊓ N) A M inf_le_left hAM
  have h3 := Subgroup.relIndex_mul_relIndex (A ⊓ N) N M inf_le_right hNM
  have h4 : (A ⊓ N).relIndex A = N.relIndex A := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right N A
  have hpos : N.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 : N.relIndex A * A.relIndex M = N.relIndex A * (A ⊓ N).relIndex N := by
    rw [← h4, h2, ← h3, h1, h4, mul_comm]
  have h6 : A.relIndex M = (A ⊓ N).relIndex N := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) h5
  rw [h6]
  exact fun h => hN (h.trans (Subgroup.relIndex_dvd_card _ _))

theorem frattini_odd_normal [Finite H] {N U : Subgroup H} [N.Normal] (hN : ¬ 2 ∣ Nat.card N)
    (hU : IsPGroup 2 U) {w : H} (hw : w ∈ Subgroup.normalizer ((U ⊔ N : Subgroup H) : Set H)) :
    ∃ z ∈ N, ∃ n ∈ Subgroup.normalizer (U : Set H), w = z * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup H := U ⊔ N with hMdef
  have hUM : U ≤ M := le_sup_left
  have hNM : N ≤ M := le_sup_right
  have hwM : ∀ x : H, x ∈ M ↔ w * x * w⁻¹ ∈ M := fun x => Subgroup.mem_normalizer_iff.1 hw x
  have hMset : (M : Set H) = (U : Set H) * (N : Set H) := Subgroup.mul_normal U N
  set V : Subgroup H := U.map (MulAut.conj w).toMonoidHom with hV
  have hmemV : ∀ x : H, x ∈ V ↔ ∃ u ∈ U, w * u * w⁻¹ = x := by
    intro x
    simp [hV, MulAut.conj_apply]
  have hVM : V ≤ M := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (hmemV x).1 hx
    exact (hwM u).1 (hUM hu)
  have hVN : V ⊔ N = M := by
    refine le_antisymm (sup_le hVM hNM) (sup_le ?_ le_sup_right)
    intro u hu
    have h1 : w⁻¹ * u * w ∈ M := by
      refine (hwM _).2 ?_
      have : w * (w⁻¹ * u * w) * w⁻¹ = u := by group
      rw [this]; exact hUM hu
    obtain ⟨u', hu', z, hz, hxz⟩ := (Set.ext_iff.1 hMset _).1 h1
    have hu_eq : u = (w * u' * w⁻¹) * (w * z * w⁻¹) := by
      have : w⁻¹ * u * w = u' * z := hxz.symm
      calc u = w * (w⁻¹ * u * w) * w⁻¹ := by group
        _ = w * (u' * z) * w⁻¹ := by rw [this]
        _ = (w * u' * w⁻¹) * (w * z * w⁻¹) := by group
    rw [hu_eq]
    exact Subgroup.mul_mem_sup ((hmemV _).2 ⟨u', hu', rfl⟩) (Subgroup.Normal.conj_mem inferInstance z hz w)
  have hU₂ : IsPGroup 2 (U.subgroupOf M) := hU.comap_subtype
  have hV₂ : IsPGroup 2 (V.subgroupOf M) := (hU.map (MulAut.conj w).toMonoidHom).comap_subtype
  let P₁ : Sylow 2 M := hU₂.toSylow (not_two_dvd_relIndex_of_sup hN rfl)
  let P₂ : Sylow 2 M := hV₂.toSylow (not_two_dvd_relIndex_of_sup hN hVN)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M P₁ P₂
  have hcoe : ∀ z : M, (z : H) ∈ V ↔ ((g⁻¹ * z * g : M) : H) ∈ U := by
    intro z
    have : z ∈ (P₂ : Subgroup M) ↔ g⁻¹ * z * g ∈ (P₁ : Subgroup M) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mul_assoc]
    exact this
  have hgn : (g : H)⁻¹ * w ∈ Subgroup.normalizer (U : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hconj : (g : H)⁻¹ * w * x * ((g : H)⁻¹ * w)⁻¹ = (g : H)⁻¹ * (w * x * w⁻¹) * g := by
      group
    rw [hconj]
    constructor
    · intro hx
      have hy : w * x * w⁻¹ ∈ V := (hmemV _).2 ⟨x, hx, rfl⟩
      have := (hcoe ⟨w * x * w⁻¹, hVM hy⟩).1 hy
      simpa using this
    · intro hx
      have hyM : w * x * w⁻¹ ∈ M := by
        have : w * x * w⁻¹ = (g : H) * ((g : H)⁻¹ * (w * x * w⁻¹) * g) * (g : H)⁻¹ := by group
        rw [this]
        exact mul_mem (mul_mem g.2 (hUM hx)) (inv_mem g.2)
      have := (hcoe ⟨w * x * w⁻¹, hyM⟩).2 (by simpa using hx)
      obtain ⟨u, hu, hux⟩ := (hmemV _).1 this
      have : u = x := by
        have h2 : w * u * w⁻¹ = w * x * w⁻¹ := hux
        have h3 := mul_left_cancel (mul_right_cancel h2)
        exact h3
      exact this ▸ hu
  obtain ⟨u, hu, z0, hz0, hgz⟩ := (Set.ext_iff.1 hMset (g : H)).1 g.2
  refine ⟨u * z0 * u⁻¹, Subgroup.Normal.conj_mem inferInstance z0 hz0 u, u * ((g : H)⁻¹ * w),
    mul_mem (Subgroup.le_normalizer hu) hgn, ?_⟩
  have hgeq : (g : H) = u * z0 := hgz.symm
  calc w = (g : H) * ((g : H)⁻¹ * w) := by group
    _ = u * z0 * ((g : H)⁻¹ * w) := by rw [hgeq]
    _ = (u * z0 * u⁻¹) * (u * ((g : H)⁻¹ * w)) := by group

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
