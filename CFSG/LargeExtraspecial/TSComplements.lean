module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LargeExtraspecial.DW

open Module Submodule QuadraticMap
open LinearMap (BilinForm)

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]


@[expose] def tsCompl (q : QuadraticForm (ZMod 2) E) (U : Submodule (ZMod 2) E) :
    Set (Submodule (ZMod 2) E) :=
  {W | IsCompl U W ∧ ∀ w ∈ W, q w = 0}

theorem map_mem_tsCompl [FiniteDimensional (ZMod 2) E] {q : QuadraticForm (ZMod 2) E}
    {U W : Submodule (ZMod 2) E} (e : E ≃ₗ[ZMod 2] E) (he : ∀ v, q (e v) = q v)
    (hU : ∀ u ∈ U, e u ∈ U) (hW : W ∈ tsCompl q U) :
    W.map (e : E →ₗ[ZMod 2] E) ∈ tsCompl q U := by
  have hUmap : U.map (e : E →ₗ[ZMod 2] E) = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (e.finrank_map_eq U)
    rintro _ ⟨u, hu, rfl⟩
    exact hU u hu
  have hcompl : IsCompl (U.map (e : E →ₗ[ZMod 2] E)) (W.map (e : E →ₗ[ZMod 2] E)) := by
    refine IsCompl.of_eq ?_ ?_
    · rw [← Submodule.map_inf (e : E →ₗ[ZMod 2] E) e.injective, hW.1.inf_eq_bot,
        Submodule.map_bot]
    · rw [← Submodule.map_sup, hW.1.sup_eq_top, Submodule.map_top]
      simp
  refine ⟨?_, ?_⟩
  · simpa only [hUmap] using hcompl
  · rintro _ ⟨w, hw, rfl⟩
    exact (he w).trans (hW.2 w hw)

private noncomputable def graph {U B : Submodule (ZMod 2) E} (f : B →ₗ[ZMod 2] U) :
    Submodule (ZMod 2) E :=
  LinearMap.range (B.subtype + U.subtype.comp f)

private theorem mem_graph {U B : Submodule (ZMod 2) E} (f : B →ₗ[ZMod 2] U) {x : E} :
    x ∈ graph f ↔ ∃ b : B, (b : E) + (f b : E) = x := by
  simp [graph, LinearMap.mem_range]

private theorem isCompl_graph {U B : Submodule (ZMod 2) E} (hUB : IsCompl U B)
    (f : B →ₗ[ZMod 2] U) : IsCompl U (graph f) := by
  let πB : E →ₗ[ZMod 2] B := B.projectionOnto U hUB.symm
  let g : E →ₗ[ZMod 2] U := U.projectionOnto B hUB - f.comp πB
  have hproj : ∀ u : U, g u = u := by
    intro u
    change U.projectionOnto B hUB (u : E) - f (πB (u : E)) = u
    rw [Submodule.projectionOnto_apply_left hUB u,
      Submodule.projectionOnto_apply_right hUB.symm u, map_zero, sub_zero]
  have hker : LinearMap.ker g = graph f := by
    ext x
    rw [LinearMap.mem_ker, mem_graph]
    constructor
    · intro hx
      refine ⟨πB x, ?_⟩
      have hx' : U.projectionOnto B hUB x = f (πB x) := sub_eq_zero.mp hx
      have hdec := Submodule.projection_add_projection_eq_self hUB x
      calc
        (πB x : E) + (f (πB x) : E) = (πB x : E) + (U.projectionOnto B hUB x : E) := by
          rw [hx']
        _ = x := by
          rw [add_comm]
          rw [Submodule.projection_apply, Submodule.projection_apply] at hdec
          exact hdec
    · rintro ⟨b, rfl⟩
      change U.projectionOnto B hUB ((b : E) + (f b : E)) -
        f (πB ((b : E) + (f b : E))) = 0
      have h1 : U.projectionOnto B hUB ((b : E) + (f b : E)) = f b := by
        rw [map_add, Submodule.projectionOnto_apply_right hUB b,
          Submodule.projectionOnto_apply_left hUB (f b), zero_add]
      have h2 : πB ((b : E) + (f b : E)) = b := by
        rw [map_add, Submodule.projectionOnto_apply_left hUB.symm b,
          Submodule.projectionOnto_apply_right hUB.symm (f b), add_zero]
      rw [h1, h2, sub_self]
  rw [← hker]
  exact LinearMap.isCompl_of_proj hproj

private theorem q_graph {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0)
    (f : B →ₗ[ZMod 2] U) (hf : ∀ b : B, polar q (b : E) (f b) = 0) :
    ∀ x ∈ graph f, q x = 0 := by
  intro x hx
  obtain ⟨b, rfl⟩ := (mem_graph f).mp hx
  rw [QuadraticMap.map_add (f := ⇑q)]
  simp only [hB b b.2, hU (f b) (f b).2, hf b, zero_add, add_zero]

private theorem projectionOnto_alt {q : QuadraticForm (ZMod 2) E}
    {U B W : Submodule (ZMod 2) E} (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) (hW : W ∈ tsCompl q U) :
    ∀ b : B, polar q (b : E) (((U.projectionOnto W hW.1).comp B.subtype) b) = 0 := by
  intro b
  let πU : E →ₗ[ZMod 2] U := U.projectionOnto W hW.1
  let πW : E →ₗ[ZMod 2] W := W.projectionOnto U hW.1.symm
  have hb : (b : E) = (πU b : E) + (πW b : E) := by
    simpa [πU, πW] using (Submodule.projection_add_projection_eq_self hW.1 (b : E)).symm
  have hqU : q (πU b : E) = 0 := hU _ (πU b).2
  have hqW : q (πW b : E) = 0 := hW.2 _ (πW b).2
  have hpolar : polar q (πU b : E) (πW b : E) = 0 := by
    have h := hB b b.2
    rw [hb, QuadraticMap.map_add (f := ⇑q), hqU, hqW, zero_add, zero_add] at h
    exact h
  calc
    polar q (b : E) (πU b : E)
        = polar q ((πU b : E) + (πW b : E)) (πU b : E) := by rw [← hb]
    _ = polar q (πU b : E) (πU b : E) + polar q (πW b : E) (πU b : E) := by
      rw [polar_add_left]
    _ = 0 := by
      have h0 : polar q (πU b : E) (πU b : E) = 0 := by
        have h := hU ((πU b : E) + (πU b : E)) (U.add_mem (πU b).2 (πU b).2)
        rw [QuadraticMap.map_add (f := ⇑q), hU _ (πU b).2] at h
        simpa using h
      have hc : polar q (πW b : E) (πU b : E) = polar q (πU b : E) (πW b : E) :=
        polar_comm q (πW b : E) (πU b : E)
      rw [h0, hc, hpolar, zero_add]

private theorem graph_projectionOnto_eq {q : QuadraticForm (ZMod 2) E}
    {U B W : Submodule (ZMod 2) E} (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) (hW : W ∈ tsCompl q U) :
    graph ((U.projectionOnto W hW.1).comp B.subtype) = W := by
  apply le_antisymm
  · rintro x ⟨b, rfl⟩
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hW.1]
    show (U.projectionOnto W hW.1) ((b : E) + (U.projectionOnto W hW.1 (b : E) : E)) = 0
    rw [map_add]
    have h1 : (U.projectionOnto W hW.1) (U.projectionOnto W hW.1 (b : E) : E) =
        U.projectionOnto W hW.1 (b : E) :=
      Submodule.projectionOnto_apply_left hW.1 _
    rw [h1, ZModModule.add_self]
  · intro w hw
    obtain ⟨u, hu, b, hb, hwb⟩ := (Submodule.mem_sup (p := U) (p' := B) (x := w)).mp (by
      rw [hUB.sup_eq_top]; exact Submodule.mem_top)
    rw [mem_graph]
    refine ⟨⟨b, hb⟩, ?_⟩
    have hbw : (b : E) = w + u := by
      calc (b : E) = ((u : E) + b) - u := by abel
        _ = w - u := by rw [hwb]
        _ = w + u := by rw [ZModModule.sub_eq_add]
    have hf : (((U.projectionOnto W hW.1).comp B.subtype) ⟨b, hb⟩ : E) = u := by
      change (U.projectionOnto W hW.1 (b : E) : E) = u
      rw [← Submodule.projection_apply, hbw]
      rw [map_add, Submodule.projection_apply_of_mem_right hW.1 hw,
        Submodule.projection_apply_of_mem_left hW.1 hu, zero_add]
    rw [hf, add_comm]
    exact hwb

private theorem projectionOnto_graph_eq {q : QuadraticForm (ZMod 2) E}
    {U B : Submodule (ZMod 2) E} (hUB : IsCompl U B)
    (f : B →ₗ[ZMod 2] U) (hf : ∀ b : B, polar q (b : E) (f b) = 0) :
    (U.projectionOnto (graph f) (isCompl_graph hUB f)).comp B.subtype = f := by
  apply LinearMap.ext
  intro b
  have hker : (U.projectionOnto (graph f) (isCompl_graph hUB f))
      ((b : E) + (f b : E)) = 0 :=
    Submodule.projectionOnto_apply_of_mem_right (isCompl_graph hUB f)
      ((mem_graph f).mpr ⟨b, rfl⟩)
  rw [map_add] at hker
  have hfb : (U.projectionOnto (graph f) (isCompl_graph hUB f)) (f b : E) = f b :=
    Submodule.projectionOnto_apply_left (isCompl_graph hUB f) (f b)
  rw [hfb] at hker
  have hU : (U.projectionOnto (graph f) (isCompl_graph hUB f)) (b : E) = f b :=
    (eq_neg_of_add_eq_zero_left hker).trans (ZModModule.neg_eq_self _)
  exact hU

noncomputable def tsComplEquiv {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    (hUB : IsCompl U B) (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) :
    tsCompl q U ≃ {f : B →ₗ[ZMod 2] U // ∀ b : B, polar q (b : E) (f b) = 0} where
  toFun W :=
    ⟨(U.projectionOnto W W.2.1).comp B.subtype,
      projectionOnto_alt hUB hU hB W.2⟩
  invFun f :=
    ⟨graph (U := U) (B := B) f, isCompl_graph (U := U) (B := B) hUB f,
      q_graph (U := U) (B := B) hU hB f f.2⟩
  left_inv W := Subtype.ext (graph_projectionOnto_eq hUB hU hB W.2)
  right_inv f := Subtype.ext (projectionOnto_graph_eq hUB f f.2)

private noncomputable def pairToDualB (q : QuadraticForm (ZMod 2) E)
    {U B : Submodule (ZMod 2) E} : B →ₗ[ZMod 2] Module.Dual (ZMod 2) U :=
  (q.polarBilin.compl₂ U.subtype).comp B.subtype

private noncomputable def pairToDualU (q : QuadraticForm (ZMod 2) E)
    {U B : Submodule (ZMod 2) E} : U →ₗ[ZMod 2] Module.Dual (ZMod 2) B :=
  (q.polarBilin.flip.compl₂ B.subtype).comp U.subtype

private theorem pairToDualB_injective (q : QuadraticForm (ZMod 2) E) {U B : Submodule (ZMod 2) E}
    (hq : q.polarBilin.Nondegenerate) (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) :
    Function.Injective (pairToDualB q (U := U) (B := B)) := by
  intro b b' h
  have hzero : pairToDualB q (U := U) (B := B) (b - b') = 0 := by
    rw [map_sub, h, sub_self]
  have hb0 : ((b - b' : B) : E) = 0 := by
    apply hq.1 ((b - b' : B) : E)
    intro x
    rw [polarBilin_apply_apply]
    obtain ⟨u, hu, b'', hb'', hxb⟩ := (Submodule.mem_sup (p := U) (p' := B) (x := x)).mp (by
      rw [hUB.sup_eq_top]; exact Submodule.mem_top)
    rw [← hxb, polar_add_right]
    have h1 : polar q ((b - b' : B) : E) u = 0 := by
      have := congrArg (fun f : Module.Dual (ZMod 2) U => f ⟨u, hu⟩) hzero
      simpa [pairToDualB, LinearMap.compl₂_apply] using this
    have h2 : polar q ((b - b' : B) : E) b'' = 0 := by
      have hmem : ((b - b' : B) : E) ∈ B := by
        show ((b - b' : B) : E) ∈ B
        exact Submodule.sub_mem (p := B) b.2 b'.2
      have h := hB (((b - b' : B) : E) + b'') (B.add_mem hmem hb'')
      rw [QuadraticMap.map_add (f := ⇑q), hB _ hmem, hB _ hb'', zero_add, zero_add] at h
      exact h
    rw [h1, h2, zero_add]
  apply Subtype.ext
  exact sub_eq_zero.mp hb0

private theorem pairToDualU_injective (q : QuadraticForm (ZMod 2) E) {U B : Submodule (ZMod 2) E}
    (hq : q.polarBilin.Nondegenerate) (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) :
    Function.Injective (pairToDualU q (U := U) (B := B)) := by
  intro u u' h
  have hzero : pairToDualU q (U := U) (B := B) (u - u') = 0 := by
    rw [map_sub, h, sub_self]
  have hu0 : ((u - u' : U) : E) = 0 := by
    apply hq.2 ((u - u' : U) : E)
    intro x
    rw [polarBilin_apply_apply]
    obtain ⟨u'', hu'', b'', hb'', hxb⟩ := (Submodule.mem_sup (p := U) (p' := B) (x := x)).mp (by
      rw [hUB.sup_eq_top]; exact Submodule.mem_top)
    rw [← hxb, polar_add_left]
    have h1 : polar q u'' ((u - u' : U) : E) = 0 := by
      have hmem : ((u - u' : U) : E) ∈ U := by
        show ((u - u' : U) : E) ∈ U
        exact Submodule.sub_mem (p := U) u.2 u'.2
      have h := hU (u'' + ((u - u' : U) : E)) (U.add_mem hu'' hmem)
      rw [QuadraticMap.map_add (f := ⇑q), hU _ hu'', hU _ hmem, zero_add, zero_add] at h
      exact h
    have h2 : polar q b'' ((u - u' : U) : E) = 0 := by
      have := congrArg (fun f : Module.Dual (ZMod 2) B => f ⟨b'', hb''⟩) hzero
      simpa [pairToDualU, LinearMap.compl₂_apply] using this
    rw [h1, h2, zero_add]
  apply Subtype.ext
  exact sub_eq_zero.mp hu0

private theorem finrank_eq_of_isCompl_of_totallySingular [FiniteDimensional (ZMod 2) E]
    (q : QuadraticForm (ZMod 2) E) {U B : Submodule (ZMod 2) E}
    (hq : q.polarBilin.Nondegenerate) (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) :
    finrank (ZMod 2) U = finrank (ZMod 2) B := by
  have h1 := LinearMap.finrank_le_finrank_of_injective (pairToDualU_injective q hq hUB hU hB)
  have h2 := LinearMap.finrank_le_finrank_of_injective (pairToDualB_injective q hq hUB hU hB)
  rw [Subspace.dual_finrank_eq] at h1 h2
  omega

private noncomputable def swapMap {U B : Submodule (ZMod 2) E}
    (e : Basis (Fin 3) (ZMod 2) B) (u : Basis (Fin 3) (ZMod 2) U) (i j : Fin 3) :
    B →ₗ[ZMod 2] U :=
  e.constr (ZMod 2) (fun k => if k = i then u j else if k = j then u i else 0)

private theorem swapMap_apply {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {i j : Fin 3} (hij : i ≠ j) (b : B) :
    swapMap e u i j b = (e.repr b j) • u i + (e.repr b i) • u j := by
  rw [swapMap, Basis.constr_apply_fintype]
  simp only [Basis.equivFun_apply]
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp_all <;> abel

private theorem swapMap_basis {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) :
    swapMap e u i j (e k) = if k = i then u j else if k = j then u i else 0 := by
  rw [swapMap, Basis.constr_basis]

private theorem polar_eq_coeff {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    (b : B) (i : Fin 3) :
    polar q (b : E) (u i) = e.repr b i := by
  have hb : (b : E) = ∑ k, e.repr b k • (e k : E) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using (congrArg Subtype.val (e.sum_repr b)).symm
  rw [hb, ← polarBilin_apply_apply]
  simp only [map_sum, map_smul, polarBilin_apply_apply]
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [hpair]

private theorem repr_u_eq_polar {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    (z : U) (k : Fin 3) :
    u.repr z k = polar q (e k) (z : E) := by
  have hz : (z : E) = ∑ i, u.repr z i • (u i : E) := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using (congrArg Subtype.val (u.sum_repr z)).symm
  rw [hz, ← polarBilin_apply_apply]
  simp only [map_sum, map_smul, polarBilin_apply_apply]
  rw [Fin.sum_univ_three]
  fin_cases k <;> simp [hpair]

private theorem swapMap_alt {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    {i j : Fin 3} (hij : i ≠ j) :
    ∀ b : B, polar q (b : E) (swapMap e u i j b) = 0 := by
  intro b
  rw [swapMap_apply hij]
  change polar q (b : E) ((e.repr b j) • (u i : E) + (e.repr b i) • (u j : E)) = 0
  rw [polar_add_right, polar_smul_right, polar_smul_right]
  rw [polar_eq_coeff (e := e) (u := u) (hpair := hpair) b i,
    polar_eq_coeff (e := e) (u := u) (hpair := hpair) b j]
  have h : (e.repr b j) * (e.repr b i) + (e.repr b i) * (e.repr b j) = 0 := by
    rw [mul_comm (e.repr b i) (e.repr b j)]
    exact ZModModule.add_self _
  exact h

private theorem polar_comm_of_alt {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {f : B →ₗ[ZMod 2] U} (hf : ∀ b : B, polar q (b : E) (f b) = 0) (b b' : B) :
    polar q (b : E) (f b') = polar q (b' : E) (f b) := by
  have h := hf (b + b')
  rw [map_add] at h
  change polar q ((b : E) + (b' : E)) ((f b : E) + (f b' : E)) = 0 at h
  rw [polar_add_left, polar_add_right, polar_add_right, hf b, hf b'] at h
  simp only [zero_add, add_zero] at h
  have h' : polar q (b : E) (f b') = -polar q (b' : E) (f b) :=
    eq_neg_of_add_eq_zero_left h
  rwa [ZModModule.neg_eq_self] at h'

private noncomputable def altMap {U B : Submodule (ZMod 2) E}
    (e : Basis (Fin 3) (ZMod 2) B) (u : Basis (Fin 3) (ZMod 2) U) (v : Fin 3 → ZMod 2) :
    B →ₗ[ZMod 2] U :=
  v 0 • swapMap e u 0 1 + v 1 • swapMap e u 0 2 + v 2 • swapMap e u 1 2

private theorem altMap_alt {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    (v : Fin 3 → ZMod 2) :
    ∀ b : B, polar q (b : E) (altMap e u v b) = 0 := by
  intro b
  have h01 := swapMap_alt (e := e) (u := u) (hpair := hpair) (i := 0) (j := 1) (by decide) b
  have h02 := swapMap_alt (e := e) (u := u) (hpair := hpair) (i := 0) (j := 2) (by decide) b
  have h12 := swapMap_alt (e := e) (u := u) (hpair := hpair) (i := 1) (j := 2) (by decide) b
  simp [altMap, polar_add_right, polar_smul_right, h01, h02, h12]

private noncomputable def altParams {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    (e : Basis (Fin 3) (ZMod 2) B) (f : B →ₗ[ZMod 2] U) : Fin 3 → ZMod 2 :=
  ![polar q (e 0) (f (e 1)), polar q (e 0) (f (e 2)), polar q (e 1) (f (e 2))]

private theorem altParams_altMap {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    (v : Fin 3 → ZMod 2) :
    altParams (q := q) e (altMap e u v) = v := by
  funext k
  fin_cases k <;>
    simp [altParams, altMap, swapMap_basis, hpair,
      polar_add_right, polar_smul_right]

private theorem altMap_altParams {q : QuadraticForm (ZMod 2) E} {U B : Submodule (ZMod 2) E}
    {e : Basis (Fin 3) (ZMod 2) B} {u : Basis (Fin 3) (ZMod 2) U}
    {hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0}
    {f : B →ₗ[ZMod 2] U} (hf : ∀ b : B, polar q (b : E) (f b) = 0) :
    altMap e u (altParams (q := q) e f) = f := by
  apply e.ext
  intro i
  apply u.ext_elem
  intro k
  rw [repr_u_eq_polar (e := e) (u := u) (hpair := hpair),
    repr_u_eq_polar (e := e) (u := u) (hpair := hpair)]
  fin_cases i <;> fin_cases k <;>
    simp [altMap, altParams, swapMap_basis, hpair, hf,
      polar_add_right, polar_smul_right]
  all_goals first
    | exact (polar_comm_of_alt hf (e 1) (e 0)).symm
    | exact (polar_comm_of_alt hf (e 2) (e 0)).symm
    | exact (polar_comm_of_alt hf (e 2) (e 1)).symm

theorem card_tsCompl_eq_eight [FiniteDimensional (ZMod 2) E] {q : QuadraticForm (ZMod 2) E}
    (hq : q.polarBilin.Nondegenerate) {U B : Submodule (ZMod 2) E} (hUB : IsCompl U B)
    (hU : ∀ u ∈ U, q u = 0) (hB : ∀ b ∈ B, q b = 0) (h3 : finrank (ZMod 2) U = 3) :
    Nat.card (tsCompl q U) = 8 := by
  have hB3 : finrank (ZMod 2) B = 3 := by
    rw [← finrank_eq_of_isCompl_of_totallySingular q hq hUB hU hB, h3]
  let e : Basis (Fin 3) (ZMod 2) B := Module.finBasisOfFinrankEq (ZMod 2) B hB3
  let φ : U →ₗ[ZMod 2] Module.Dual (ZMod 2) B := pairToDualU q (U := U) (B := B)
  have hφ : Function.Injective φ := pairToDualU_injective q hq hUB hU hB
  have hdim : finrank (ZMod 2) U = finrank (ZMod 2) (Module.Dual (ZMod 2) B) := by
    rw [Subspace.dual_finrank_eq, hB3, h3]
  let φEquiv : U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) B :=
    LinearMap.linearEquivOfInjective φ hφ hdim
  let u : Basis (Fin 3) (ZMod 2) U := e.dualBasis.map φEquiv.symm
  have hpair : ∀ i j : Fin 3, polar q (e i) (u j) = if i = j then 1 else 0 := by
    intro i j
    have h1 : φ (u j) = e.dualBasis j := by
      change φ (e.dualBasis.map φEquiv.symm j) = e.dualBasis j
      rw [Basis.map_apply]
      change φEquiv (φEquiv.symm (e.dualBasis j)) = e.dualBasis j
      exact φEquiv.apply_symm_apply _
    have h2 := congrArg (fun f : Module.Dual (ZMod 2) B => f (e i)) h1
    rw [show e.dualBasis j (e i) = if i = j then 1 else 0 by
      rw [Module.Basis.dualBasis_apply_self]] at h2
    change φ (u j) (e i) = if i = j then 1 else 0
    exact h2
  have hequiv : tsCompl q U ≃ (Fin 3 → ZMod 2) :=
    (tsComplEquiv hUB hU hB).trans
      { toFun := fun f => altParams (q := q) e f.1
        invFun := fun v => ⟨altMap e u v, altMap_alt (hpair := hpair) v⟩
        left_inv := fun f => by
          apply Subtype.ext
          exact altMap_altParams (e := e) (u := u) (hpair := hpair) f.2
        right_inv := fun v => altParams_altMap (e := e) (u := u) (hpair := hpair) v }
  rw [Nat.card_congr hequiv, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

end CFSG.LargeExtraspecial.DW

