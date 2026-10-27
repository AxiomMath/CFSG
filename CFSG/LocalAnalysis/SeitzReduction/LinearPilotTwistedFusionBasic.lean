module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

section Fusion

variable {X : Type*} [Group X]

@[expose] def PerfectTwistedFusionIn (α : MulAut X) (Q : X → Prop) : Prop :=
  ∃ m y : X, y ≠ 1 ∧ (α m)⁻¹ * m = y ∧ Q y ∧
    ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ y ∈ P ∧ ∀ p ∈ P, α p = p

theorem PerfectTwistedFusionIn.perfectTwistedFusion {α : MulAut X} {Q : X → Prop}
    (h : PerfectTwistedFusionIn α Q) : PerfectTwistedFusion α := by
  obtain ⟨m, y, hy, hmy, -, P, hP, hyP, hPα⟩ := h
  exact ⟨m, y, hy, hmy, P, hP, hyP, hPα⟩

theorem PerfectTwistedFusionIn.mono {α : MulAut X} {Q Q' : X → Prop} (hQ : ∀ x, Q x → Q' x)
    (h : PerfectTwistedFusionIn α Q) : PerfectTwistedFusionIn α Q' := by
  obtain ⟨m, y, hy, hmy, hQy, P, hP, hyP, hPα⟩ := h
  exact ⟨m, y, hy, hmy, hQ y hQy, P, hP, hyP, hPα⟩

theorem apply_inv_apply_eq_of_conj_eq {α β ψ : MulAut X} (h : ψ * α * ψ⁻¹ = β) (x : X) :
    α (ψ⁻¹ x) = ψ⁻¹ (β x) := by
  rw [← h]
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem PerfectTwistedFusionIn.of_conj {α β ψ : MulAut X} {Q : X → Prop}
    (h : ψ * α * ψ⁻¹ = β) (hQ : ∀ x, Q x → Q (ψ⁻¹ x)) (hβ : PerfectTwistedFusionIn β Q) :
    PerfectTwistedFusionIn α Q := by
  obtain ⟨m, y, hy, hmy, hQy, P, hP, hyP, hPβ⟩ := hβ
  have h' := apply_inv_apply_eq_of_conj_eq h
  refine ⟨ψ⁻¹ m, ψ⁻¹ y, fun h1 => hy ?_, ?_, hQ y hQy,
    P.map (ψ⁻¹ : MulAut X).toMonoidHom, ?_, ⟨y, hyP, rfl⟩, ?_⟩
  · rw [← map_one (ψ⁻¹ : MulAut X)] at h1
    exact (ψ⁻¹ : MulAut X).injective h1
  · rw [h', ← map_inv, ← map_mul, hmy]
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    exact (h' p).trans (congrArg _ (hPβ p hp))

theorem inv_apply_mul_eq_of_sq_eq_one {α : MulAut X} (hα : α ^ 2 = 1) (m : X) :
    α ((α m)⁻¹ * m) = ((α m)⁻¹ * m)⁻¹ := by
  have hαα : α (α m) = m := by
    rw [← MulAut.mul_apply, ← sq, hα, MulAut.one_apply]
  rw [map_mul, map_inv, hαα, _root_.mul_inv_rev, inv_inv]

theorem mulAut_mul_conj_mul_inv_eq_conj (ψ : MulAut X) (c : X) :
    ψ * MulAut.conj c * ψ⁻¹ = MulAut.conj (ψ c) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem perfectTwistedFusionIn_of_inner
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X)) {α : MulAut X} {Q : X → Prop}
    {N : Subgroup (MulAut X)} (hNinn : N ≤ (MulAut.conj : X →* MulAut X).range)
    (hNα : N ≤ centralizer {α}) (hN : ⁅N, N⁆ = N) (m : X) (hy : (α m)⁻¹ * m ≠ 1)
    (hyN : MulAut.conj ((α m)⁻¹ * m) ∈ N) (hQ : Q ((α m)⁻¹ * m)) :
    PerfectTwistedFusionIn α Q := by
  set P := N.comap (MulAut.conj : X →* MulAut X) with hPdef
  have hPN : P.map (MulAut.conj : X →* MulAut X) = N := by
    rw [hPdef, Subgroup.map_comap_eq, inf_eq_right.mpr hNinn]
  refine ⟨m, _, hy, rfl, hQ, P, ?_, hyN, fun p hp => ?_⟩
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hPN, hN]
  · have hc : MulAut.conj p * α = α * MulAut.conj p := mem_centralizer_singleton_iff.mp (hNα hp)
    apply hinj
    rw [← mulAut_mul_conj_mul_inv_eq_conj, ← hc, mul_inv_cancel_right]

end Fusion

section Rank

variable {K : Type*} [Field K] {n : ℕ}

theorem rank_eq_one_of_col_mem {M : Matrix (Fin n) (Fin n) K} {v : Fin n → K} (hv : v ≠ 0)
    (hcol : ∀ j, M.col j ∈ K ∙ v) {j₀ : Fin n} (hj₀ : M.col j₀ = v) : M.rank = 1 := by
  rw [rank_eq_finrank_span_cols]
  have hspan : Submodule.span K (Set.range M.col) = K ∙ v := by
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨j, rfl⟩
      exact hcol j
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.subset_span ⟨j₀, hj₀⟩
  rw [hspan, finrank_span_singleton hv]

theorem rank_eq_two_of_col_mem {M : Matrix (Fin n) (Fin n) K} {v w : Fin n → K}
    (hvw : LinearIndependent K ![v, w]) (hcol : ∀ j, M.col j ∈ Submodule.span K {v, w})
    {j₁ j₂ : Fin n} (hj₁ : M.col j₁ = v) (hj₂ : M.col j₂ = w) : M.rank = 2 := by
  rw [rank_eq_finrank_span_cols]
  have hspan : Submodule.span K (Set.range M.col) = Submodule.span K {v, w} := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      exact hcol j
    · rintro x (rfl | rfl)
      · exact Submodule.subset_span ⟨j₁, hj₁⟩
      · exact Submodule.subset_span ⟨j₂, hj₂⟩
  have hrange : Set.range ![v, w] = {v, w} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [hspan, ← hrange, finrank_span_eq_card hvw, Fintype.card_fin]

theorem linearIndependent_pi_single_pair {a b : Fin n} (hab : a ≠ b) :
    LinearIndependent K ![(Pi.single a 1 : Fin n → K), Pi.single b 1] := by
  have h := (Pi.basisFun K (Fin n)).linearIndependent.comp ![a, b] (by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm])
  convert h using 1
  ext i : 1
  fin_cases i <;> simp

end Rank

section Classes

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def IsInvolutionClass (k : ℕ) (y : projectiveSL n K) : Prop :=
  ∃ g : SpecialLinearGroup (Fin n) K, proj n K g = y ∧ g * g = 1 ∧
    ((g : Matrix (Fin n) (Fin n) K) - 1).rank = k

theorem IsInvolutionClass.conjAut {k : ℕ} {y : projectiveSL n K} (h : IsInvolutionClass k y)
    (A : GL (Fin n) K) : IsInvolutionClass k (conjAut n K A y) := by
  obtain ⟨g, rfl, hg, hrk⟩ := h
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K A g,
    (conjAut_proj A g).symm, ?_, ?_⟩
  · rw [← map_mul, hg, map_one]
  · rw [coe_slConjugation]
    have hAA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hsub : (A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        (A : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAA]
    rw [hsub, Matrix.rank_mul_eq_left_of_isUnit_det _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp (A⁻¹).isUnit),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit),
      hrk]

theorem IsInvolutionClass.conjAut_inv {k : ℕ} {y : projectiveSL n K} (h : IsInvolutionClass k y)
    (A : GL (Fin n) K) : IsInvolutionClass k ((LinearFlag.conjAut n K A)⁻¹ y) := by
  rw [← map_inv]
  exact h.conjAut A⁻¹

theorem IsInvolutionClass.ne_one [CharP K 2] {k : ℕ} (hk : k ≠ 0) {y : projectiveSL n K}
    (h : IsInvolutionClass k y) : y ≠ 1 := by
  rintro rfl
  obtain ⟨g, hg1, hgg, hrk⟩ := h
  obtain ⟨c, -, hc⟩ := (proj_eq_one_iff.mp hg1)
  have hcc : (c : K) * c = 1 := by
    have h1 : (g : Matrix (Fin n) (Fin n) K) * g = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hgg, Matrix.SpecialLinearGroup.coe_one]
    rw [hc, ← map_mul] at h1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Matrix.rank_le_width ((g : Matrix (Fin 0) (Fin 0) K) - 1)
      omega
    · have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, hn⟩ ⟨0, hn⟩) h1
      simpa [Matrix.scalar_apply] using h2
  have hc1 : (c : K) = 1 := by
    have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h1 : ((c : K) + 1) ^ 2 = 0 := by linear_combination hcc + ((c : K) + 1) * h22
    have h2 : (c : K) + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h1
    rwa [CharTwo.add_eq_zero] at h2
  rw [hc, hc1, map_one, sub_self, Matrix.rank_zero] at hrk
  exact hk hrk.symm

theorem IsInvolutionClass.orderOf_eq_two [CharP K 2] {k : ℕ} (hk : k ≠ 0)
    {y : projectiveSL n K} (h : IsInvolutionClass k y) : orderOf y = 2 := by
  have hy1 := h.ne_one hk
  obtain ⟨g, rfl, hg, -⟩ := h
  refine orderOf_eq_prime ?_ hy1
  rw [sq, ← map_mul, hg, map_one]

end Classes

end CFSG.SeitzReduction.LinearPilot
