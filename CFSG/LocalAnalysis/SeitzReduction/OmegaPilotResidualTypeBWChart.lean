module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Dual

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (N : (Fin d → K) →ₗ[K] (Fin d → K))
  (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))

include hadj in
theorem orth_apply_wallDual (hB : (QuadraticMap.polarBilin Q).Nondegenerate) {z : Fin d → K}
    (hz : ∀ w ∈ LinearMap.range N, QuadraticMap.polar Q w z = sqrtTwo K (Q w))
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgN : ∀ x, g (N x) = N (g x)) : g (N z) = N z := by
  have hgi : ∀ x, g.symm (N x) = N (g.symm x) := fun x => by
    rw [LinearEquiv.symm_apply_eq, hgN, LinearEquiv.apply_symm_apply]
  have hgO' : ∀ v, Q (g.symm v) = Q v := fun v => by
    rw [← TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg (g.symm v),
      LinearEquiv.apply_symm_apply]
  have hker : g z - z ∈ LinearMap.ker N := by
    rw [mem_ker_iff_polar hB N hadj]
    intro x
    have h1 : QuadraticMap.polar Q (N x) (g z) = QuadraticMap.polar Q (g.symm (N x)) z := by
      rw [← polar_apply_of_mem_orth hg (g.symm (N x)) z, LinearEquiv.apply_symm_apply]
    rw [QuadraticMap.polar_sub_right, h1, hgi, hz _ (LinearMap.mem_range_self N _),
      hz _ (LinearMap.mem_range_self N x), ← hgi, hgO', sub_self]
  rw [hgN]
  have h2 := LinearMap.mem_ker.mp hker
  rw [map_sub, sub_eq_zero] at h2
  exact h2

end Dual

section Restrict

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  (hQ : ∃ v, Q v ≠ 0) (X : Subgroup (matrixProjectiveDerived Q)) (U : Submodule K (Fin d → K))

@[expose] noncomputable def subRestrictHom (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U) :
    ↥X →* Module.End K U where
  toFun x := (projLift hQ (x : matrixProjectiveDerived Q) :
    (Fin d → K) →ₗ[K] (Fin d → K)).restrict (hXU x x.2)
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [projLift_one']
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp [projLift_mul]

theorem subRestrictHom_apply (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U) (x : ↥X) (u : U) :
    ((subRestrictHom hQ X U hXU x u : U) : Fin d → K) =
      projLift hQ (x : matrixProjectiveDerived Q) u :=
  rfl

theorem mem_ker_subRestrictHom (hXU : ∀ x ∈ X, ∀ u ∈ U, projLift hQ x u ∈ U) (x : ↥X) :
    x ∈ (subRestrictHom hQ X U hXU).ker ↔
      ∀ u ∈ U, projLift hQ (x : matrixProjectiveDerived Q) u = u := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h u hu
    have h' := congrArg (fun f : Module.End K U => ((f ⟨u, hu⟩ : U) : Fin d → K)) h
    exact h'
  · intro h
    apply LinearMap.ext
    intro u
    exact Subtype.ext (h u u.2)

end Restrict

section Proj

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def wallProj (xs zy : Fin d → K) : (Fin d → K) →ₗ[K] (Fin d → K) :=
  LinearMap.id - ((QuadraticMap.polarBilin Q).flip zy).smulRight xs

omit [CharP K 2] in
theorem wallProj_apply (xs zy v : Fin d → K) :
    wallProj (Q := Q) xs zy v = v - QuadraticMap.polar Q v zy • xs :=
  rfl

variable (hQ : ∃ v, Q v ≠ 0) (X : Subgroup (matrixProjectiveDerived Q))
  (E U : Submodule K (Fin d → K)) (xs zy : Fin d → K)

@[expose] noncomputable def projRestrictHom (hXE : ∀ x ∈ X, ∀ e ∈ E, projLift hQ x e ∈ E)
    (hUE : U ≤ E) (hπE : ∀ e ∈ E, wallProj (Q := Q) xs zy e ∈ U)
    (hπU : ∀ u ∈ U, wallProj (Q := Q) xs zy u = u) (hπx : wallProj (Q := Q) xs zy xs = 0)
    (hXx : ∀ x ∈ X, projLift hQ x xs = xs) : ↥X →* Module.End K U where
  toFun x := (wallProj (Q := Q) xs zy ∘ₗ (projLift hQ (x : matrixProjectiveDerived Q) :
    (Fin d → K) →ₗ[K] (Fin d → K))).restrict fun u hu => hπE _ (hXE x x.2 u (hUE hu))
  map_one' := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply, OneMemClass.coe_one,
      projLift_one']
    exact hπU _ w.2
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply, Subgroup.coe_mul, projLift_mul,
      Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply]
    have e1 : wallProj (Q := Q) xs zy (projLift hQ (y : matrixProjectiveDerived Q) w) =
        projLift hQ (y : matrixProjectiveDerived Q) w -
          QuadraticMap.polar Q (projLift hQ (y : matrixProjectiveDerived Q) w) zy • xs :=
      wallProj_apply _ _ _
    rw [e1, map_sub, map_smul, hXx x x.2, map_sub, map_smul, hπx, smul_zero, sub_zero]

theorem projRestrictHom_apply (hXE : ∀ x ∈ X, ∀ e ∈ E, projLift hQ x e ∈ E)
    (hUE : U ≤ E) (hπE : ∀ e ∈ E, wallProj (Q := Q) xs zy e ∈ U)
    (hπU : ∀ u ∈ U, wallProj (Q := Q) xs zy u = u) (hπx : wallProj (Q := Q) xs zy xs = 0)
    (hXx : ∀ x ∈ X, projLift hQ x xs = xs) (x : ↥X) (u : U) :
    ((projRestrictHom hQ X E U xs zy hXE hUE hπE hπU hπx hXx x u : U) : Fin d → K) =
      wallProj (Q := Q) xs zy (projLift hQ (x : matrixProjectiveDerived Q) u) :=
  rfl

end Proj

section Trace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem isCompl_comap_subtype {E U C : Submodule K V} (hUE : U ≤ E) (hCE : C ≤ E)
    (hdisj : U ⊓ C = ⊥) (hsup : U ⊔ C = E) :
    IsCompl (U.comap E.subtype) (C.comap E.subtype) := by
  refine IsCompl.of_eq ?_ ?_
  · rw [← Submodule.comap_inf, hdisj, Submodule.comap_bot, Submodule.ker_subtype]
  · rw [eq_top_iff]
    intro z _
    have hz : (z : V) ∈ U ⊔ C := by
      rw [hsup]
      exact z.2
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp hz
    have e : z = ⟨u, hUE hu⟩ + ⟨c, hCE hc⟩ := Subtype.ext huc.symm
    rw [e]
    exact Submodule.add_mem_sup (show _ ∈ U.comap E.subtype from hu)
      (show _ ∈ C.comap E.subtype from hc)

theorem trace_restrict_eq_one_add {E U : Submodule K V} {x : V} (hx0 : x ≠ 0) (hUE : U ≤ E)
    (hxE : x ∈ E) (hdisj : U ⊓ K ∙ x = ⊥) (hsup : U ⊔ K ∙ x = E) (f : V →ₗ[K] V)
    (hfE : ∀ e ∈ E, f e ∈ E) (hfx : f x = x) (ψ : U →ₗ[K] U)
    (hψ : ∀ u : U, f u - (ψ u : V) ∈ K ∙ x) :
    LinearMap.trace K E (f.restrict hfE) = 1 + LinearMap.trace K U ψ := by
  have hLE : K ∙ x ≤ E := (Submodule.span_singleton_le_iff_mem x E).mpr hxE
  set L : Submodule K E := (K ∙ x).comap E.subtype with hL
  set U' : Submodule K E := U.comap E.subtype with hU'
  have hc : IsCompl L U' := (isCompl_comap_subtype hUE hLE hdisj hsup).symm
  have he : L ≤ L.comap (f.restrict hfE) := by
    intro l hl
    change (f l : V) ∈ K ∙ x
    obtain ⟨c, hcl⟩ := Submodule.mem_span_singleton.mp (show (l : V) ∈ K ∙ x from hl)
    rw [← hcl, map_smul, hfx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  rw [trace_eq_trace_restrict_add_trace_mapQ L (f.restrict hfE) he]
  congr 1
  ·
    have hid : (f.restrict hfE).restrict he = LinearMap.id := by
      apply LinearMap.ext
      intro l
      apply Subtype.ext
      apply Subtype.ext
      obtain ⟨c, hcl⟩ := Submodule.mem_span_singleton.mp (show ((l : E) : V) ∈ K ∙ x from l.2)
      change f ((l : E) : V) = (l : E)
      rw [← hcl, map_smul, hfx]
    rw [hid, LinearMap.trace_id]
    have h1 : finrank K L = finrank K (K ∙ x) :=
      (Submodule.comapSubtypeEquivOfLe hLE).finrank_eq
    rw [h1, finrank_span_singleton hx0, Nat.cast_one]
  ·
    set ι : U ≃ₗ[K] (E ⧸ L) :=
      (Submodule.comapSubtypeEquivOfLe hUE).symm.trans (Submodule.quotientEquivOfIsCompl L U' hc).symm
      with hι
    have hιu : ∀ u : U, ι u = Submodule.Quotient.mk ⟨u, hUE u.2⟩ := fun u => rfl
    have key : ∀ u : U, L.mapQ L (f.restrict hfE) he (ι u) = ι (ψ u) := by
      intro u
      rw [hιu, hιu, Submodule.mapQ_apply, Submodule.Quotient.eq]
      change f (u : V) - (ψ u : V) ∈ K ∙ x
      exact hψ u
    have hconj : L.mapQ L (f.restrict hfE) he = ι.conj ψ := by
      apply LinearMap.ext
      intro q
      obtain ⟨u, rfl⟩ := ι.surjective q
      rw [key, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    rw [hconj, LinearMap.trace_conj']

end Trace

end CFSG.SeitzReduction.OmegaPilot
