module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelSL
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.ModelSpinPlus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviComponents
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classification

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi

private theorem diagramGraph_submatrix_connected {K : Type*} [Group K] {D : UniversalRootDatum K}
    {C : Set (Fin D.rank)} {e : Fin C.ncard → Fin D.rank} (he : Function.Injective e)
    (hrange : Set.range e = C) (hC : IsNodeConnected D C) :
    (TauCeti.diagramGraph (D.cartan.submatrix e e)).Connected := by
  rw [TauCeti.diagramGraph_submatrix he D.cartan, SimpleGraph.connected_iff]
  let g : Fin D.rank → Fin C.ncard := fun x =>
    if h : x ∈ Set.range e then (Equiv.ofInjective e he).symm ⟨x, h⟩
    else ⟨0, (Set.ncard_pos (Set.toFinite C)).2 hC.1⟩
  have hg : ∀ i, g (e i) = i := by
    intro i
    simp only [g, Set.mem_range_self, dite_true]
    exact Equiv.ofInjective_symm_apply he i
  refine ⟨fun a b => ?_, ⟨⟨0, (Set.ncard_pos (Set.toFinite C)).2 hC.1⟩⟩⟩
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hstep : ∀ x y, NodeAdj D C x y →
      ((TauCeti.diagramGraph D.cartan).comap e).Adj (g x) (g y) := by
    intro x y hxy
    obtain ⟨hx, hy, hadj⟩ := hxy
    obtain ⟨i, rfl⟩ := hrange.symm ▸ hx
    obtain ⟨j, rfl⟩ := hrange.symm ▸ hy
    rw [hg i, hg j, SimpleGraph.comap_adj]
    exact hadj
  have hpath := hC.2 (e a) (hrange ▸ Set.mem_range_self a) (e b)
    (hrange ▸ Set.mem_range_self b)
  have hwalk := Relation.ReflTransGen.lift g hstep (e a) (e b) hpath
  simpa only [Function.onFun, hg a, hg b] using hwalk

private theorem dynkinType_isSimplyLaced_of_isFiniteType_isSymm {t : TauCeti.DynkinType}
    {A : Matrix (Fin t.rank) (Fin t.rank) ℤ} (hA : TauCeti.IsFiniteType A)
    (hs : Matrix.IsSymm A) (ht : t.Valid) (hAt : A = t.cartanMatrix) : t.IsSimplyLaced := by
  have hsl : Matrix.IsSimplyLaced A := by
    refine (TauCeti.IsFiniteType.isSimplyLaced_iff hA).mpr fun i j hij => ?_
    have hmem := TauCeti.IsFiniteType.apply_mul_apply_mem_of_ne hA hij
    have hsym := hs.apply i j
    rw [hsym] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hsq : A i j ^ 2 ≤ 3 := by
      rw [pow_two]
      omega
    have hsq1 : A i j ^ 2 ≤ 1 := by
      by_cases h0 : A i j = 0
      · rw [h0]
        norm_num
      · rw [Int.sq_eq_one_of_sq_le_three hsq h0]
    rw [hsym]
    simpa [pow_two] using hsq1
  exact (TauCeti.DynkinType.isSimplyLaced_cartanMatrix_iff_of_valid ht).mp (hAt ▸ hsl)

private theorem exists_valid_isSimplyLaced_dynkinType {K : Type*} [Group K]
    {D : UniversalRootDatum K} {C : Set (Fin D.rank)} (hsym : D.cartan.IsSymm)
    (hC : IsNodeConnected D C) :
    ∃ (t : TauCeti.DynkinType) (e : Fin t.rank → Fin D.rank), t.Valid ∧ t.IsSimplyLaced ∧
      t.rank = C.ncard ∧ Function.Injective e ∧ Set.range e = C ∧
      D.cartan.submatrix e e = t.cartanMatrix := by
  classical
  let e : Fin C.ncard → Fin D.rank :=
    C.toFinset.orderEmbOfFin (Set.ncard_eq_toFinset_card' C).symm
  have he : Function.Injective e := (C.toFinset.orderEmbOfFin _).injective
  have hrange : Set.range e = C :=
    (Finset.range_orderEmbOfFin C.toFinset _).trans (Set.coe_toFinset C)
  obtain ⟨t, ⟨ht, eσ, hAσ⟩, -⟩ :=
    (D.isFiniteType.submatrix he).existsUnique_dynkinType
      (diagramGraph_submatrix_connected he hrange hC)
  have hcard : t.rank = C.ncard := by
    simpa using Fintype.card_congr eσ.symm
  have he' : Function.Injective (fun i => e (eσ.symm i)) := he.comp eσ.symm.injective
  have hrange' : Set.range (fun i => e (eσ.symm i)) = C := by
    rw [show (fun i => e (eσ.symm i)) = e ∘ eσ.symm from rfl, eσ.symm.surjective.range_comp e]
    exact hrange
  have hcart' : D.cartan.submatrix (fun i => e (eσ.symm i)) (fun i => e (eσ.symm i)) =
      t.cartanMatrix := by
    ext i j
    change D.cartan (e (eσ.symm i)) (e (eσ.symm j)) = t.cartanMatrix i j
    simpa using hAσ (eσ.symm i) (eσ.symm j)
  have hsl : t.IsSimplyLaced :=
    dynkinType_isSimplyLaced_of_isFiniteType_isSymm (D.isFiniteType.submatrix he')
      (hsym.submatrix (fun i => e (eσ.symm i))) ht hcart'
  exact ⟨t, fun i => e (eσ.symm i), ht, hsl, hcard, he', hrange', hcart'⟩

theorem gomiLeviFactor_leviM_of_isSymm {K k : Type} [Group K] [Finite K] [Field k]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) {x : (Fin D.rank → ℤ) → k → K}
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (hsym : D.cartan.IsSymm) (hx : IsCharTwoSteinberg D.roots x) {C : Set (Fin D.rank)}
    (hmodel : ∀ t : TauCeti.DynkinType, t.Valid → t.IsSimplyLaced → t.rank = C.ncard →
      HasCharTwoModel k t.cartanMatrix)
    (hC : IsNodeConnected D C) (h2 : 2 ≤ C.ncard) : GomiLeviFactor ↥(leviM D C) := by
  obtain ⟨t, e', ht, hsl, hcard, he', hrange', hcart'⟩ :=
    exists_valid_isSimplyLaced_dynkinType hsym hC
  obtain ⟨G, grp, DT, xT, σT, hσT, hM⟩ := hmodel t ht hsl hcard
  let e'' : Fin DT.rank → Fin D.rank := fun i => e' (σT.symm i)
  have he'' : Function.Injective e'' := he'.comp σT.symm.injective
  have hcart'' : D.cartan.submatrix e'' e'' = DT.cartan := by
    ext i j
    change D.cartan (e' (σT.symm i)) (e' (σT.symm j)) = DT.cartan i j
    rw [show D.cartan (e' (σT.symm i)) (e' (σT.symm j)) =
      t.cartanMatrix (σT.symm i) (σT.symm j) from congrFun₂ hcart' _ _]
    simpa using (hσT (σT.symm i) (σT.symm j)).symm
  have hr : 1 ≤ DT.rank := by
    have htr : t.rank = DT.rank := by simpa using Fintype.card_congr σT
    omega
  have hx'' : IsCharTwoSteinberg
      (CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he'') ∅)
      (fun γ c => x (CFSG.LieType.RootSystem.Restrict.ext e'' γ) c) := by
    have hx0 : IsCharTwoSteinberg (CFSG.LieType.RootSystem.roots D.isFiniteType ∅) x := by
      rw [← hdiv]
      exact hx
    exact IsCharTwoSteinberg.ext he'' hx0
  have hrange'' : Set.range e'' = C := by
    rw [show e'' = e' ∘ σT.symm from rfl, σT.symm.surjective.range_comp e']
    exact hrange'
  have hmain := gomiLeviFactor_leviM_of_model hM hct hdiv hpar he'' hcart'' hr hx''
  rwa [hrange''] at hmain

theorem hasCharTwoModel_of_isSimplyLaced (k : Type) [Field k] [Finite k] [CharP k 2]
    (hSL : ∀ m, 2 ≤ m → IsChevTwo (Matrix.SpecialLinearGroup (Fin (m + 1)) k ⧸
      center (Matrix.SpecialLinearGroup (Fin (m + 1)) k)))
    {t : TauCeti.DynkinType} (ht : t.Valid) (hsl : t.IsSimplyLaced) (h2 : 2 ≤ t.rank)
    (hE6 : t = .E6 → HasCharTwoModel k (CartanMatrix.E 6))
    (hE7 : t = .E7 → HasCharTwoModel k (CartanMatrix.E 7)) (hE8 : t ≠ .E8) :
    HasCharTwoModel k t.cartanMatrix := by
  cases t with
  | A n =>
    have hn : 2 ≤ n := by simpa using h2
    simpa using hasCharTwoModel_A k hn (hSL n hn)
  | B n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_B n)
  | C n => exact absurd hsl (TauCeti.DynkinType.not_isSimplyLaced_C n)
  | D n =>
    have hn : 4 ≤ n := by simpa using ht
    simpa using hasCharTwoModel_D k hn
  | E6 => simpa using hE6 rfl
  | E7 => simpa using hE7 rfl
  | E8 => exact absurd rfl hE8
  | F4 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_F4
  | G2 => exact absurd hsl TauCeti.DynkinType.not_isSimplyLaced_G2

end CFSG.GroupTheory.GomiLeviExc
