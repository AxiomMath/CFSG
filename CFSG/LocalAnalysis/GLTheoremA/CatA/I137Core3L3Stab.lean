module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3L3Levi
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open Matrix Module

variable {K : Type*} [Field K]

@[expose] noncomputable def l3GLOfEquiv (c : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) : GL (Fin 3) K where
  val := LinearMap.toMatrix' (c : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
  inv := LinearMap.toMatrix' (c.symm : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : (c : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) ∘ₗ (c.symm : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) =
        LinearMap.id := by
      ext v
      simp
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have : (c.symm : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) ∘ₗ (c : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) =
        LinearMap.id := by
      ext v
      simp
    rw [this, LinearMap.toMatrix'_id]

theorem l3GLOfEquiv_mulVec (c : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : Fin 3 → K) :
    ((l3GLOfEquiv c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c v :=
  LinearMap.toMatrix'_mulVec _ _

theorem l3GLOfEquiv_inv_mulVec (c : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (v : Fin 3 → K) :
    (((l3GLOfEquiv c)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c.symm v :=
  LinearMap.toMatrix'_mulVec (c.symm : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) v

theorem l3_conj_mulVec (c : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K)) (g : GL (Fin 3) K) (v : Fin 3 → K) :
    ((l3GLOfEquiv c * g * (l3GLOfEquiv c)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      c ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ c.symm v) := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    l3GLOfEquiv_inv_mulVec, l3GLOfEquiv_mulVec]

theorem l3_entry_eq_mulVec (M : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    M i j = (M *ᵥ Pi.single j 1) i := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem l3_exists_conj_shape (D : Subgroup (GL (Fin 3) K)) {W : Submodule K (Fin 3 → K)}
    (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hDW : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) :
    ∃ C : GL (Fin 3) K, L3ParabShape D ((MulAut.conj C).toMonoidHom.comp D.subtype) := by
  have hpos : finrank K W ≠ 0 := fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  have hlt : finrank K W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  obtain hd | hd : finrank K W = 1 ∨ finrank K W = 2 := by omega
  ·
    set e0 : Fin 3 → K := Pi.single 0 1 with he0
    have he0ne : e0 ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [he0] at this
    have hdim : finrank K (K ∙ e0) = 1 := finrank_span_singleton he0ne
    let f : W ≃ₗ[K] (K ∙ e0) := LinearEquiv.ofFinrankEq W (K ∙ e0) (hd.trans hdim.symm)
    obtain ⟨c, hc⟩ := Submodule.exists_linearEquiv_restrict_eq f
    have hinW : c.symm e0 ∈ W := by
      have hmem : e0 ∈ (K ∙ e0) := Submodule.mem_span_singleton_self e0
      have h1 := hc (f.symm ⟨e0, hmem⟩)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : c.symm e0 = ((f.symm ⟨e0, hmem⟩ : W) : Fin 3 → K) := by
        rw [← c.symm_apply_apply ((f.symm ⟨e0, hmem⟩ : W) : Fin 3 → K), ← h1]
      rw [h2]
      exact (f.symm ⟨e0, hmem⟩).2
    have hmapW : ∀ w ∈ W, c w ∈ (K ∙ e0) := fun w hw => by
      rw [← hc ⟨w, hw⟩]
      exact (f ⟨w, hw⟩).2
    refine ⟨l3GLOfEquiv c, Or.inl fun x i => ?_⟩
    have hx : ((((MulAut.conj (l3GLOfEquiv c)).toMonoidHom.comp D.subtype) x : GL (Fin 3) K)) =
        l3GLOfEquiv c * (x : GL (Fin 3) K) * (l3GLOfEquiv c)⁻¹ := rfl
    rw [hx]
    refine (l3_entry_eq_mulVec _ _ _).trans ?_
    rw [l3_conj_mulVec]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (hmapW _ (hDW x x.2 _ hinW))
    rw [← ha]
    simp [he0, Fin.succ_ne_zero]
  ·
    let p : (Fin 3 → K) →ₗ[K] K := LinearMap.proj (0 : Fin 3)
    have hrange : LinearMap.range p = ⊤ :=
      LinearMap.range_eq_top.mpr fun a => ⟨Pi.single 0 a, by simp [p]⟩
    have hker := LinearMap.finrank_range_add_finrank_ker p
    rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hker
    have hdim : finrank K (LinearMap.ker p) = 2 := by omega
    let f : W ≃ₗ[K] (LinearMap.ker p) :=
      LinearEquiv.ofFinrankEq W (LinearMap.ker p) (hd.trans hdim.symm)
    obtain ⟨c, hc⟩ := Submodule.exists_linearEquiv_restrict_eq f
    have hinW : ∀ e ∈ LinearMap.ker p, c.symm e ∈ W := fun e he => by
      have h1 := hc (f.symm ⟨e, he⟩)
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 : c.symm e = ((f.symm ⟨e, he⟩ : W) : Fin 3 → K) := by
        rw [← c.symm_apply_apply ((f.symm ⟨e, he⟩ : W) : Fin 3 → K), ← h1]
      rw [h2]
      exact (f.symm ⟨e, he⟩).2
    have hmapW : ∀ w ∈ W, c w ∈ LinearMap.ker p := fun w hw => by
      rw [← hc ⟨w, hw⟩]
      exact (f ⟨w, hw⟩).2
    refine ⟨l3GLOfEquiv c, Or.inr fun x i => ?_⟩
    have hx : ((((MulAut.conj (l3GLOfEquiv c)).toMonoidHom.comp D.subtype) x : GL (Fin 3) K)) =
        l3GLOfEquiv c * (x : GL (Fin 3) K) * (l3GLOfEquiv c)⁻¹ := rfl
    have hei : (Pi.single i.succ (1 : K) : Fin 3 → K) ∈ LinearMap.ker p := by
      simp [p, Fin.succ_ne_zero]
    rw [hx]
    refine (l3_entry_eq_mulVec _ _ _).trans ?_
    rw [l3_conj_mulVec]
    have := hmapW _ (hDW x x.2 _ (hinW _ hei))
    simpa [p] using this

theorem l3_exists_levi_of_stable [CharP K 2] (D : Subgroup (GL (Fin 3) K))
    {W : Submodule K (Fin 3 → K)} (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hDW : ∀ g ∈ D, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W)
    (hdet : ∀ g ∈ D, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ ψ : D →* GL (Fin 2) K, ∀ x : D, ψ x = 1 → x ^ 2 = 1 := by
  obtain ⟨C, hs⟩ := l3_exists_conj_shape D hW0 hWt hDW
  refine ⟨l3LeviHom hs, fun x hx => ?_⟩
  have hdet' : ∀ y : D, ((((MulAut.conj C).toMonoidHom.comp D.subtype) y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).det = 1 := fun y => by
    have : ((((MulAut.conj C).toMonoidHom.comp D.subtype) y : GL (Fin 3) K)) =
        C * (y : GL (Fin 3) K) * C⁻¹ := rfl
    rw [this, Units.val_mul, Units.val_mul, Matrix.det_units_conj, hdet y y.2]
  have h2 := l3_sq_eq_one_of_levi_eq_one hs hdet' x hx
  have hinj : Function.Injective ((MulAut.conj C).toMonoidHom.comp D.subtype) :=
    (MulAut.conj C).injective.comp Subtype.val_injective
  apply hinj
  rw [map_pow, map_one]
  exact h2

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
