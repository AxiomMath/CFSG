module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddBad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {G : Type} [Group G] [Finite G] {W N T : Subgroup G} {z p₀ a : G} {k : ℕ}

namespace BadCase

omit [Finite G] in
theorem z_mem_W (h : BadCase W N T z p₀ a k) : z ∈ W := h.le_W (h.le_N h.z_mem)

theorem isolated (h : BadCase W N T z p₀ a k) {g : G} (hg : g ∈ W)
    (hc : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) : g * z * g⁻¹ = z := by
  have hzW := z_mem_W h
  have hyW : g * z * g⁻¹ ∈ W := W.mul_mem (W.mul_mem hg hzW) (W.inv_mem hg)
  have hyN : g * z * g⁻¹ ∈ N := h.centralizer_z _ hyW hc
  have hp₀y : (g * z * g⁻¹) * p₀ = p₀ * (g * z * g⁻¹) := h.p₀_central _ hyN
  have hp₀W : p₀ ∈ W := h.le_W h.p₀_mem
  have hp₁W : g⁻¹ * p₀ * g ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hg) hp₀W) hg
  have hp₁z : (g⁻¹ * p₀ * g) * z = z * (g⁻¹ * p₀ * g) := by
    have e := congrArg (fun x => g⁻¹ * x * g) hp₀y
    simp only [mul_assoc, inv_mul_cancel_left] at e
    calc (g⁻¹ * p₀ * g) * z = g⁻¹ * (p₀ * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * p₀) * g := by rw [hp₀y]
      _ = z * (g⁻¹ * p₀ * g) := by group
  have hp₁N : g⁻¹ * p₀ * g ∈ N := h.centralizer_z _ hp₁W hp₁z
  have hsq : (g⁻¹ * p₀ * g) * (g⁻¹ * p₀ * g) ∈ T :=
    mul_self_mem_of_relIndex_eq_two h.relIndex_eq hp₁N
  have hconj : g⁻¹ * z * g = ((g⁻¹ * p₀ * g) * (g⁻¹ * p₀ * g)) ^ k := by
    rw [← h.pow_eq]
    have e : ∀ x : G, (MulAut.conj g⁻¹) x = g⁻¹ * x * g := fun x => by
      rw [MulAut.conj_apply, inv_inv]
    rw [← e, ← e, map_pow, map_mul]
  have hzgT : g⁻¹ * z * g ∈ T := hconj ▸ T.pow_mem hsq k
  have hinv : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [h.z_mul_self, mul_one, inv_mul_cancel]
  have hne : g⁻¹ * z * g ≠ 1 := by
    intro h1
    apply h.z_ne_one
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
  have hz := h.eq_z hzgT hinv hne
  calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hz]
    _ = z := by group

omit [Finite G] in
theorem isSolvable_N (h : BadCase W N T z p₀ a k) : Group.IsSolvable N :=
  isSolvable_of_relIndex_eq_two h.isCyclic h.relIndex_eq

end BadCase

theorem BadCase.isSolvable (h : BadCase W N T z p₀ a k) : Group.IsSolvable W := by
  have hzW := BadCase.z_mem_W h
  refine CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.IsolatedInvolution.isSolvable_of_isolated
    (t := (⟨z, hzW⟩ : W)) ?_ ?_ ?_ ?_
  · intro h1
    exact h.z_ne_one (congrArg Subtype.val h1)
  · exact Subtype.ext h.z_mul_self
  · intro g hc
    exact Subtype.ext (BadCase.isolated h g.2 (congrArg Subtype.val hc))
  ·
    have hN := BadCase.isSolvable_N h
    let ψ : Subgroup.centralizer ({(⟨z, hzW⟩ : W)} : Set W) →* N :=
      { toFun := fun x => ⟨(x : W), h.centralizer_z _ (x : W).2 (by
          have := Subgroup.mem_centralizer_singleton_iff.1 x.2
          exact congrArg Subtype.val this)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := ψ) ?_
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun u : N => (u : G)) hxy))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
