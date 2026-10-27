module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfGap
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleSplit

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen
open scoped Pointwise commutatorElement


section Coords

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem coordTuple_fixed_of_rootChar_fixed {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔroot : ∀ β ∈ Δ, IsRoot τ β)
    (hdet : (Matrix.of fun β γ : Δ => corootPair (β : Fin τ.rank → ℤ) γ).det = 4)
    (σ : L ≃+* L) (c : (Fin τ.rank → ℤ) → Lˣ)
    (h : ∀ β ∈ Δ, σ ((rootChar (coordTuple Δ c) β : Lˣ) : L) =
      ((rootChar (coordTuple Δ c) β : Lˣ) : L)) :
    ∀ β ∈ Δ, σ ((c β : Lˣ) : L) = ((c β : Lˣ) : L) := by
  classical
  let σu : Lˣ →* Lˣ := Units.map σ.toRingHom.toMonoidHom
  let c' : (Fin τ.rank → ℤ) → Lˣ := fun i => σu (c i) / c i
  let A : Matrix ↥Δ ↥Δ ℤ := Matrix.of fun i j =>
    corootPair (i : Fin τ.rank → ℤ) (j : Fin τ.rank → ℤ)
  have hc' : ∀ i : Fin τ.rank → ℤ, c' i = σu (c i) / c i := fun i => rfl
  have hdetA : A.det = 4 := hdet
  have h2 : ∀ j : ↥Δ, ∏ i : ↥Δ, c' (i : Fin τ.rank → ℤ) ^ A i j = 1 := by
    intro j
    have hj := h (j : Fin τ.rank → ℤ) j.2
    rw [rootChar_coordTuple hΔroot c (j : Fin τ.rank → ℤ)] at hj
    have huj : (∏ i ∈ Δ, σu (c i) ^ corootPair i (j : Fin τ.rank → ℤ)) =
        ∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ) := by
      have hmap : σu (∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ)) =
          ∏ i ∈ Δ, σu (c i) ^ corootPair i (j : Fin τ.rank → ℤ) := by
        rw [map_prod]
        exact Finset.prod_congr rfl fun i _ => by rw [map_zpow]
      rw [← hmap]
      apply Units.ext
      exact hj
    have e3 : (∏ i : ↥Δ, c' (i : Fin τ.rank → ℤ) ^ A i j) =
        ∏ i ∈ Δ, c' i ^ corootPair i (j : Fin τ.rank → ℤ) :=
      Finset.prod_coe_sort (s := Δ)
        (f := fun i : Fin τ.rank → ℤ => c' i ^ corootPair i (j : Fin τ.rank → ℤ))
    rw [e3]
    calc ∏ i ∈ Δ, c' i ^ corootPair i (j : Fin τ.rank → ℤ)
        = ∏ i ∈ Δ, (σu (c i) ^ corootPair i (j : Fin τ.rank → ℤ) *
            (c i ^ corootPair i (j : Fin τ.rank → ℤ))⁻¹) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [hc' i, div_eq_mul_inv, mul_zpow, inv_zpow]
      _ = (∏ i ∈ Δ, σu (c i) ^ corootPair i (j : Fin τ.rank → ℤ)) *
          (∏ i ∈ Δ, c i ^ corootPair i (j : Fin τ.rank → ℤ))⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      _ = 1 := by rw [huj, mul_inv_cancel]
  have h3 : (fun i : ↥Δ => c' (i : Fin τ.rank → ℤ)) = 1 :=
    eq_one_of_pow_tuple_eq_one (L := L) hdetA h2
  intro β hβ
  have h4 : c' β = 1 := congrFun h3 ⟨β, hβ⟩
  have h5 : σu (c β) = c β := by
    have h4' : σu (c β) / c β = 1 := h4
    exact div_eq_one.mp h4'
  exact congrArg Units.val h5

end Coords

section HSLProd

variable {L : Type} [Field L]

theorem innerD4Fix_HSL_eq_prod (u : Lˣ) :
    (HSL u : SL2 L) = uSL (u : L) * vSL (-(((u⁻¹ : Lˣ) : L))) * uSL (u : L) *
      (uSL (-1) * vSL (1 : L) * uSL (-1)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, Units.mul_inv, Units.inv_mul]

end HSLProd

section Unipotent

variable {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}

theorem rootSL2_HSL_mem_CQ {β : Fin τ.rank → ℤ} (hβ : β ∈ componentRoots χ i) (σ : L ≃+* L)
    {u : Lˣ} (hu : σ (u : L) = (u : L)) :
    rootSL2 τ L β (HSL u) ∈ CQ σ i := by
  have hβroot : IsRoot τ β := isRoot_of_mem_componentRoots hβ
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβroot
  have hεσ : σ ε = ε := sq_eq_one_fixed σ hε
  have hβΨ : β ∈ unionRoots χ ({i} : Set (KernelComponent χ)) := by
    rw [unionRoots_singleton]; exact hβ
  have hnegβΨ : -β ∈ unionRoots χ ({i} : Set (KernelComponent χ)) := by
    rw [unionRoots_singleton]
    exact (isRootComponent_componentRoots i).neg_mem β hβ
  have huσ : σ ((u⁻¹ : Lˣ) : L) = ((u⁻¹ : Lˣ) : L) := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hu]
  have hku : σ ((pinnedData τ β).2.2 • (u : L)) = (pinnedData τ β).2.2 • (u : L) := by
    rw [map_zsmul, hu]
  have hkm1 : σ ((pinnedData τ β).2.2 • (-1 : L)) = (pinnedData τ β).2.2 • (-1 : L) := by
    rw [map_zsmul]; norm_num
  have hvu : σ (ε * (-((u⁻¹ : Lˣ) : L))) = ε * (-((u⁻¹ : Lˣ) : L)) := by
    rw [map_mul, hεσ, map_neg, huσ]
  have hv1 : σ (ε * (1 : L)) = ε * (1 : L) := by
    rw [map_mul, hεσ, map_one]
  rw [innerD4Fix_HSL_eq_prod, map_mul, map_mul, map_mul, map_mul, map_mul]
  simp only [rootSL2_uSL_eq, hv]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) (mul_mem (mul_mem ?_ ?_) ?_)
  · exact pinnedX_mem_CQ hβΨ hku
  · exact pinnedX_mem_CQ hnegβΨ hvu
  · exact pinnedX_mem_CQ hβΨ hku
  · exact pinnedX_mem_CQ hβΨ hkm1
  · exact pinnedX_mem_CQ hnegβΨ hv1
  · exact pinnedX_mem_CQ hβΨ hkm1

theorem rootDiagUnit_coordTuple_mem_CQ {Δ : Finset (Fin τ.rank → ℤ)}
    (hΔ : ∀ β ∈ Δ, β ∈ componentRoots χ i) (σ : L ≃+* L) (c : (Fin τ.rank → ℤ) → Lˣ)
    (hc : ∀ β ∈ Δ, σ ((c β : Lˣ) : L) = ((c β : Lˣ) : L)) :
    rootDiagUnit τ (coordTuple Δ c) ∈ CQ σ i := by
  classical
  induction Δ using Finset.induction with
  | empty =>
      have h : coordTuple (∅ : Finset (Fin τ.rank → ℤ)) c = 1 := by
        funext i
        simp [coordTuple]
      rw [h, rootDiagUnit_one]
      exact one_mem _
  | insert β s hβs ih =>
      have hcoord : coordTuple (insert β s) c =
          (fun i => c β ^ corootPair β (Pi.single i 1)) * coordTuple s c := by
        funext i
        simp [coordTuple, Finset.prod_insert hβs, Pi.mul_apply]
      have hβmem : β ∈ componentRoots χ i := hΔ β (Finset.mem_insert_self β s)
      rw [hcoord, rootDiagUnit_mul, ← rootSL2_HSL_eq (isRoot_of_mem_componentRoots hβmem)]
      refine mul_mem (rootSL2_HSL_mem_CQ hβmem σ
        (hc β (Finset.mem_insert_self β s))) ?_
      exact ih (fun γ hγ => hΔ γ (Finset.mem_insert_of_mem hγ))
        (fun γ hγ => hc γ (Finset.mem_insert_of_mem hγ))

end Unipotent

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
