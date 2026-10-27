module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKindDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem exc_closure_sub_mem {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {v : WeylGroup τ}
    (hv : v ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (y : Fin τ.rank → ℤ) :
    excToQ (v • y - y) ∈ Submodule.span ℚ (excToQ '' Ψ) := by
  revert y
  refine Subgroup.closure_induction
    (k := {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (p := fun w _ => ∀ y : Fin τ.rank → ℤ,
      excToQ (w • y - y) ∈ Submodule.span ℚ (excToQ '' Ψ)) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨γ, hγΨ, rfl⟩ y
    have hγ : IsRoot τ γ := hΨ.isRoot γ hγΨ
    have hmem : excToQ γ ∈ Submodule.span ℚ (excToQ '' Ψ) :=
      Submodule.subset_span (show excToQ γ ∈ excToQ '' Ψ from ⟨γ, hγΨ, rfl⟩)
    have hsub : (y - corootPair γ y • γ) - y = -(corootPair γ y • γ) := by abel
    rw [rootReflection_smul hγ, hsub, excToQ_neg, excToQ_zsmul]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (corootPair γ y : ℚ) hmem)
  · intro y
    rw [one_smul, sub_self, excToQ_zero]
    exact Submodule.zero_mem _
  · rintro a b _ _ iha ihb y
    have key : (a * b) • y - y =
        (a • (b • y - y) - (b • y - y)) + (b • y - y) + (a • y - y) := by
      rw [mul_smul, smul_sub]
      abel
    rw [key, excToQ_add, excToQ_add]
    exact Submodule.add_mem _ (Submodule.add_mem _ (iha _) (ihb _)) (iha _)
  · rintro a _ iha y
    have key : a⁻¹ • y - y = -(a • (a⁻¹ • y) - a⁻¹ • y) := by
      rw [← mul_smul, mul_inv_cancel, one_smul]
      abel
    rw [key, excToQ_neg]
    exact Submodule.neg_mem _ (iha (a⁻¹ • y))

private theorem exc_det_neg_element_aux1 {τ : Tag} (x : Fin τ.rank → ℚ) :
    x = ∑ i, x i • excToQ (Pi.single i 1 : Fin τ.rank → ℤ) := by
  have hbase : (∑ i, (Pi.single i (x i) : Fin τ.rank → ℚ)) = x := by
    funext j
    simpa using Finset.sum_pi_single j (fun i => x i) Finset.univ
  have hsingle : (∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℚ)) =
      ∑ i, (Pi.single i (x i) : Fin τ.rank → ℚ) :=
    Finset.sum_congr rfl fun i _ => by
      simpa using (Pi.single_smul' i (x i) (1 : ℚ)).symm
  have htoQ : (∑ i, x i • excToQ (Pi.single i 1 : Fin τ.rank → ℤ)) =
      ∑ i, x i • (Pi.single i 1 : Fin τ.rank → ℚ) :=
    Finset.sum_congr rfl fun i _ => by rw [excToQ_single]
  rw [htoQ, hsingle, hbase]

private theorem exc_det_neg_element_aux2 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) {v : WeylGroup τ}
    (hv : v ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (L : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ))
    (hL : ∀ x : Fin τ.rank → ℤ, L (excToQ x) = excToQ (v • x)) (x : Fin τ.rank → ℚ) :
    L x - x ∈ Submodule.span ℚ (excToQ '' Ψ) := by
  have hx : L x - x = ∑ i, x i • (L (excToQ (Pi.single i 1 : Fin τ.rank → ℤ)) -
      excToQ (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [exc_det_neg_element_aux1 x]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_sub]
  rw [hx]
  refine Submodule.sum_mem _ fun i _ => ?_
  refine Submodule.smul_mem _ (x i) ?_
  rw [hL (Pi.single i 1), ← excToQ_sub]
  exact exc_closure_sub_mem hΨ hv (Pi.single i 1)

theorem exc_det_neg_element {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {v : WeylGroup τ}
    (hv : v ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ})
    (hneg : ∀ γ ∈ Ψ, v • γ = -γ) (L : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ))
    (hL : ∀ x : Fin τ.rank → ℤ, L (excToQ x) = excToQ (v • x)) :
    LinearMap.det L = (-1) ^ compRank Ψ := by
  let U : Submodule ℚ (Fin τ.rank → ℚ) := Submodule.span ℚ (excToQ '' Ψ)
  have hUdef : U = Submodule.span ℚ (excToQ '' Ψ) := rfl
  have hLneg : ∀ u ∈ U, L u = -u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨γ, hγΨ, hγx⟩ := hx
        rw [← hγx, hL γ, hneg γ hγΨ, excToQ_neg]
    | zero => simp
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, neg_add]
    | smul a x _ ih => rw [map_smul, ih, smul_neg]
  have hU : U ≤ U.comap L := by
    intro u hu
    rw [Submodule.mem_comap, hLneg u hu]
    exact U.neg_mem hu
  have hdiff : ∀ x : Fin τ.rank → ℚ, L x - x ∈ U := by
    intro x
    rw [hUdef]
    exact exc_det_neg_element_aux2 hΨ hv L hL x
  have hrestr : (L.restrict (p := U) (q := U) hU) = (-1 : ℚ) • LinearMap.id := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simpa only [LinearMap.coe_restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
      neg_one_smul, Submodule.coe_neg] using hLneg u.1 u.2
  have hdetU : (L.restrict (p := U) (q := U) hU).det = (-1 : ℚ) ^ Module.finrank ℚ U := by
    rw [hrestr]
    simp
  have hquot : U.mapQ U L hU = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | _ w => simpa [Submodule.Quotient.eq] using hdiff w
  have hdetQ : (U.mapQ U L hU).det = 1 := by rw [hquot, LinearMap.det_id]
  have hfin : compRank Ψ = Module.finrank ℚ U := by
    unfold compRank
    rw [hUdef]
    unfold excToQ
    rfl
  rw [L.det_eq_det_mul_det U hU, hdetU, hdetQ, mul_one, hfin]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
