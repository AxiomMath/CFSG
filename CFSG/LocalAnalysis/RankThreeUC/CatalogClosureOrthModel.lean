module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOrthMain
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureSymplectic
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup Matrix

theorem exists_invariant_singular {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (Φ : QuadForm K (ι → K))
    {R E : Subgroup (StatedOmega Φ.Q)} (hR : R ≠ ⊥) (hRp : IsPGroup p R)
    (hE : E ≤ Subgroup.normalizer (R : Set (StatedOmega Φ.Q))) :
    ∃ W : Submodule K (ι → K), W ≠ ⊥ ∧ (∀ w ∈ W, Φ.Q w = 0) ∧
      ∀ e ∈ E, ∀ w ∈ W, ((e : GL ι K) : Matrix ι ι K) *ᵥ w ∈ W := by
  have hQ : ∀ h v, Φ.Q (natRep (StatedOmega Φ.Q) h v) = Φ.Q v := fun h v => by
    rw [natRep_apply]
    exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
  have hstar : NoQuotientReflection Φ (natRep (StatedOmega Φ.Q)) := fun h Z hZ a ha hQa => by
    simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega Φ h.2 hZ ha hQa
  have hinj : Function.Injective (natRep (StatedOmega Φ.Q)) := natRep_injective _
  refine ⟨singSeq Φ (natRep (StatedOmega Φ.Q)) R (Module.finrank K (ι → K)), ?_,
    fun w hw => isTotallySingular_singSeq Φ _ R _ w hw, fun e he w hw => ?_⟩
  · intro h0
    refine hR ((Subgroup.eq_bot_iff_forall R).mpr fun g hg => hinj ?_)
    refine LinearMap.ext fun v => ?_
    have := (le_flagKernel_singFlag p hQ hstar R hRp hg).2 (Module.finrank K (ι → K)) v
      (by rw [singFlag_finrank_succ, h0, Φ.polar.perp_bot]; trivial)
    rw [singFlag_finrank, h0, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, map_one, Module.End.one_apply]
  · have := apply_mem_singSeq hQ R (Module.finrank K (ι → K)) (hE he) hw
    rwa [natRep_apply] at this

section Closure

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem twoLocalClosure_eq_top_statedOmega (Q : QuadraticForm K (ι → K))
    (Φ : QuadForm K (ι → K)) (hΦ : ⇑Q = Φ.Q)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 3 ≤ Module.finrank K (ι → K))
    (β₀ : LinearMap.BilinForm K (ι → K)) (hβ₀ : ∀ x, β₀ x x = Q x)
    (E P : Subgroup (StatedOmega Φ.Q)) (hEodd : Odd (Nat.card E)) (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hEN : E ≤ Subgroup.normalizer (P : Set (StatedOmega Φ.Q))) :
    twoLocalClosure E = ⊤ := by
  obtain ⟨W, hW0, hWs, hWE⟩ := exists_invariant_singular 2 Φ hP hP2 hEN
  let ψ := statedOmegaEquiv hΦ hE
  refine twoLocalClosure_eq_top_of_equiv ψ E ?_
  refine OrthClosure.twoLocalClosure_eq_top_elementary hnd hd β₀ hβ₀ (E.map ψ.toMonoidHom) ?_
    hW0 (fun w hw => by rw [congrFun hΦ w]; exact hWs w hw) ?_
  · rwa [Subgroup.card_map_of_injective ψ.injective]
  · rintro _ ⟨e, he, rfl⟩ x hx
    exact hWE e he x hx

theorem not_rankThreeUC_of_orthogonal {G : Type} [Group G] [Finite G] (hS : Standing G)
    (Q : QuadraticForm K (ι → K)) (Φ : QuadForm K (ι → K)) (hΦ : ⇑Q = Φ.Q)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 3 ≤ Module.finrank K (ι → K))
    (β₀ : LinearMap.BilinForm K (ι → K)) (hβ₀ : ∀ x, β₀ x x = Q x)
    (e : G ≃* StatedProj (StatedOmega Φ.Q)) : ¬ rankThreeUC G :=
  not_rankThreeUC_of_proj hS (StatedOmega Φ.Q) e (fun E P hE' hP hP2 hEN =>
    twoLocalClosure_eq_top_statedOmega Q Φ hΦ hE hnd hd β₀ hβ₀ E P hE' hP hP2 hEN)

end Closure

theorem not_rankThreeUC_of_POmegaPlus {G : Type} [Group G] [Finite G] (hS : Standing G)
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_orthogonal hS (quadPlus n K) (quadPlusForm n K) (coe_quadPlus n K)
    (commutator_orthogonalGroup_quadPlus (by omega)) (nondegenerate_polarBilin_quadPlus n K) ?_
    (SpClosure.spB₀ n K) (fun x => ?_) e
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [quadPlus_apply, SpClosure.spB₀, Matrix.toBilin'_apply', SpClosure.dotProduct_spU_mulVec]
    rfl

@[expose] noncomputable def orthB₀Minus (n : ℕ) (K : Type) [Field K] (b c : K) :
    LinearMap.BilinForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
  LinearMap.mk₂ K
    (fun v w => ∑ i, v (.inl i) * w (.inr (.inl i)) + v (.inr (.inr 0)) * w (.inr (.inr 0)) +
      b * v (.inr (.inr 0)) * w (.inr (.inr 1)) + c * v (.inr (.inr 1)) * w (.inr (.inr 1)))
    (fun v₁ v₂ w => by simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]; ring)
    (fun c' v w => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, mul_add]; ring)
    (fun v w₁ w₂ => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)
    (fun c' v w => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm c'])

theorem not_rankThreeUC_of_POmegaMinus {G : Type} [Group G] [Finite G] (hS : Standing G)
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_orthogonal hS (quadMinus n K b c) (quadMinusForm n K b c hirr)
    (coe_quadMinus n K b c) (commutator_orthogonalGroup_quadMinus hn hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) ?_ (orthB₀Minus n K b c)
    (fun x => ?_) e
  · rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [quadMinus_apply]
    simp only [orthB₀Minus, LinearMap.mk₂_apply, sq]
    ring

end CFSG.LocalAnalysis.RankThreeUC
