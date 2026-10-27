module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTorus
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXClassicalTorus

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.LocalAnalysis.GorensteinLyons

variable {K : Type*} [Field K] {p : ℕ}

theorem torusVec_pow_eq_one {ζ : Kˣ} (hζ : ζ ^ p = 1) (i m j : Fin p) :
    torusVec ζ i m j ^ p = 1 := by
  rw [torusVec_apply, mul_pow]
  split_ifs <;> simp [hζ, inv_pow]

theorem torusHom_torusVec_mem_detOneTorus (P : GL (Fin p) K) {ζ : Kˣ} (hζ : ζ ^ p = 1)
    (i m : Fin p) : torusHom P (torusVec ζ i m) ∈ detOneTorus P := by
  rw [mem_detOneTorus_iff]
  refine ⟨fun j => ⟨torusVec ζ i m j, (mem_rootsOfUnity _ _).2 (torusVec_pow_eq_one hζ i m j)⟩,
    MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
  change ((∏ j, (⟨torusVec ζ i m j, _⟩ : rootsOfUnity p K) : rootsOfUnity p K) : Kˣ) = 1
  rw [Subgroup.val_finsetProd]
  exact prod_torusVec ζ i m

variable {S : Type*} [Group S]

theorem conj_apply_eq_mul_conj_mul_inv (σ : MulAut S) (a : S) :
    MulAut.conj (σ a) = σ * MulAut.conj a * σ⁻¹ := by
  apply MulEquiv.ext
  intro y
  change σ a * y * (σ a)⁻¹ = σ (a * σ.symm y * a⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem apply_eq_of_commute_conj
    (hinj : Function.Injective (MulAut.conj : S →* MulAut S)) {σ : MulAut S} {a : S}
    (h : σ * MulAut.conj a = MulAut.conj a * σ) : σ a = a := by
  apply hinj
  rw [conj_apply_eq_mul_conj_mul_inv, h, mul_inv_cancel_right]

theorem map_closure_range {S' : Type*} [Group S'] (f : S →* S') {ι : Type*} (c : ι → S) :
    (Subgroup.closure (Set.range c)).map f = Subgroup.closure (Set.range (f ∘ c)) := by
  rw [MonoidHom.map_closure, Set.range_comp]

theorem elementary_of_map {S' : Type*} [Group S'] (f : S →* S') (hf : Function.Injective f)
    {E : Subgroup S} (hab : ∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x)
    (hexp : ∀ x ∈ E.map f, x ^ p = 1) :
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) := by
  refine ⟨fun x hx y hy => hf ?_, fun x hx => hf ?_⟩
  · rw [map_mul, map_mul]
    exact hab _ (Subgroup.mem_map_of_mem f hx) _ (Subgroup.mem_map_of_mem f hy)
  · rw [map_pow, map_one]
    exact hexp _ (Subgroup.mem_map_of_mem f hx)

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
