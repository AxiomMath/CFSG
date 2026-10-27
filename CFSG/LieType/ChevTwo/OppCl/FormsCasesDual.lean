module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesSplit

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section DualAPI

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
variable {Φ : ReflForm F V} {TS : Submodule F V → Prop} {W M W' : Submodule F V}

theorem split3_exists_dual_W'_of_W [FiniteDimensional F V] (hS : Split3 Φ TS W M W')
    (hW : Φ.IsTotallyIsotropic W) (hW' : Φ.IsTotallyIsotropic W') (φ : W →ₗ[F] F) :
    ∃ w' ∈ W', ∀ w : W, Φ.β w' w = φ w := by
  have hcompl : IsCompl W (M ⊔ W') :=
    ⟨hS.disj_W, codisjoint_iff.mpr (by rw [← sup_assoc]; exact hS.sup_eq)⟩
  obtain ⟨w', hw', hw'v⟩ := split3_exists_dual_W' hS hW hW'
    (φ ∘ₗ Submodule.projectionOnto W (M ⊔ W') hcompl) fun v hv => by
      rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_right hcompl hv, map_zero]
  refine ⟨w', hw', fun w => ?_⟩
  rw [hw'v, LinearMap.comp_apply, Submodule.projectionOnto_apply_left hcompl w]

theorem split3_exists_dual_bases [FiniteDimensional F V] (hσ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hS : Split3 Φ TS W M W') (hW : Φ.IsTotallyIsotropic W) (hW' : Φ.IsTotallyIsotropic W') :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (f e : ι → V), (∀ k, f k ∈ W) ∧ (∀ k, e k ∈ W') ∧
      (∀ k l, Φ.β (e k) (f l) = if k = l then 1 else 0) ∧
      (∀ w ∈ W, w = ∑ k, Φ.β (e k) w • f k) ∧
      (∀ y ∈ W', y = ∑ k, Φ.σ (Φ.β y (f k)) • e k) := by
  let b := Module.finBasis F W
  have hsumL : ∀ (s : Finset (Fin (Module.finrank F W))) (g : Fin (Module.finrank F W) → V)
      (v : V), Φ.β (∑ i ∈ s, g i) v = ∑ i ∈ s, Φ.β (g i) v := fun s g v =>
    map_sum (AddMonoidHom.mk' (fun x => Φ.β x v) (fun a c => Φ.add_left a c v)) g s
  have hsumR : ∀ (s : Finset (Fin (Module.finrank F W))) (u : V)
      (g : Fin (Module.finrank F W) → V), Φ.β u (∑ i ∈ s, g i) = ∑ i ∈ s, Φ.β u (g i) :=
    fun s u g => map_sum (AddMonoidHom.mk' (Φ.β u) (Φ.add_right u)) g s
  have h1 : ∀ k, ∃ w' ∈ W', ∀ w : W, Φ.β w' w = b.coord k w :=
    fun k => split3_exists_dual_W'_of_W hS hW hW' (b.coord k)
  choose e he he' using h1
  have hdual : ∀ k l, Φ.β (e k) (b l : V) = if k = l then 1 else 0 := by
    intro k l
    rw [he' k (b l), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]
  have hexp : ∀ w ∈ W, w = ∑ k, Φ.β (e k) w • (b k : V) := by
    intro w hw
    have h : w = ∑ k, b.repr ⟨w, hw⟩ k • (b k : V) := by
      have h0 := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
      rw [Submodule.coe_sum] at h0
      exact h0.symm
    refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
    have h3 : Φ.β (e k) w = b.repr ⟨w, hw⟩ k :=
      (he' k ⟨w, hw⟩).trans (b.coord_apply k ⟨w, hw⟩)
    rw [h3]
  refine ⟨Fin (Module.finrank F W), inferInstance, inferInstance, fun k => (b k : V), e,
    fun k => (b k).2, he, hdual, hexp, fun y hy => ?_⟩
  have key : y - ∑ k, Φ.σ (Φ.β y (b k : V)) • e k = 0 := by
    apply split3_kernel_W' hS hW' _ (sub_mem hy (sum_mem fun k _ => W'.smul_mem _ (he k)))
    intro w hw
    apply Φ.refl
    have hf : ∀ l, Φ.β (y - ∑ k, Φ.σ (Φ.β y (b k : V)) • e k) (b l : V) = 0 := by
      intro l
      rw [Φ.β_sub_left, hsumL]
      simp only [Φ.smul_left, hσ, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, sub_self]
    rw [hexp w hw, hsumR]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Φ.smul_right, hf k, mul_zero]
  exact sub_eq_zero.mp key

end DualAPI

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
