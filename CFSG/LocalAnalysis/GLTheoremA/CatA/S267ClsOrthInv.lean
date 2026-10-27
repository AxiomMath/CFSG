module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsInv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsOmegaInv
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped IsMulCommutative

private theorem sum_orth_expansion {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {W : Submodule K V} {n : ℕ} (b : Module.Basis (Fin n) K W)
    (hbo : ∀ i j, i ≠ j → polar Q (b i : V) (b j : V) = 0) (hbQ : ∀ i, Q (b i : V) ≠ 0)
    {w : V} (hw : w ∈ W) :
    ∑ k, ((Q (b k : V))⁻¹ * polar Q (b k : V) w) • (b k : V) = (2 : K) • w := by
  have hsum := b.sum_repr ⟨w, hw⟩
  have hw' : w = ∑ k, b.repr ⟨w, hw⟩ k • (b k : V) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simpa using this.symm
  have hpol : ∀ j, polar Q (b j : V) w = b.repr ⟨w, hw⟩ j * (2 * Q (b j : V)) := by
    intro j
    conv_lhs => rw [hw']
    rw [← polarBilin_apply_apply, map_sum, Finset.sum_eq_single j]
    · rw [map_smul, polarBilin_apply_apply, polar_self, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat]
    · intro k _ hkj
      rw [map_smul, polarBilin_apply_apply, hbo j k (Ne.symm hkj), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  conv_rhs => rw [hw', Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpol k, smul_smul]
  congr 1
  field_simp [hbQ k]

variable {K : Type} [Field K] {p : ℕ} {d : ℕ}

private theorem quad_glRep_apply (h2 : (2 : K) ≠ 0) (Q : QuadraticForm K (Fin d → K))
    {Aε : Subgroup (GL (Fin d) K)} (hAεβ : Aε ≤ isomGL (polarBilin Q)) (a : ↥Aε)
    (v : Fin d → K) : Q (glRep Aε a v) = Q v := by
  have h1 := mem_isomGL.1 (hAεβ a.2) v v
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, glRep_apply] at *
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h1
  exact mul_left_cancel₀ h2 h1

theorem invol_mem_matrixDerived_of_three [Finite K] (h2 : (2 : K) ≠ 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (Q : QuadraticForm K (Fin d → K))
    (hQ : (polarBilin Q).Nondegenerate) {Aε : Subgroup (GL (Fin d) K)} [IsMulCommutative Aε]
    (hAεβ : Aε ≤ isomGL (polarBilin Q)) (hA : ∀ a : ↥Aε, a ^ p = 1)
    [DecidableEq (Hyperplane ↥Aε p)] (H₁ H₂ H₃ : Hyperplane ↥Aε p) (h12 : H₁ ≠ H₂)
    (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃) :
    glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₂}) ∈ matrixDerived Q ∨
      glEquiv.symm (invol (glRep Aε) hp hA hpK {H₁, H₃}) ∈ matrixDerived Q ∨
      glEquiv.symm (invol (glRep Aε) hp hA hpK {H₂, H₃}) ∈ matrixDerived Q := by
  classical
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  haveI : Fintype K := Fintype.ofFinite K
  set ρ := glRep Aε with hρdef
  have hρQ : ∀ (a : ↥Aε) (v : Fin d → K), Q (ρ a v) = Q v := quad_glRep_apply h2 Q hAεβ
  have hbasis : ∀ H : Hyperplane ↥Aε p, ∃ b : Module.Basis
      (Fin (Module.finrank K (weightSpace ρ H.1))) K (weightSpace ρ H.1),
      (∀ i j, i ≠ j → polar Q (b i : Fin d → K) (b j : Fin d → K) = 0) ∧
        ∀ i, Q (b i : Fin d → K) ≠ 0 := by
    intro H
    set U := weightSpace ρ H.1 with hUdef
    have hQU : (polarBilin (Q.comp U.subtype)).Nondegenerate := by
      have key : ∀ u : U, (∀ w : U, polar Q (u : Fin d → K) (w : Fin d → K) = 0) → u = 0 :=
        fun u hu => Subtype.ext (nondegenerate_weightFamily ρ hp hA hpK Q hQ hρQ (some H) u.2
          fun w hw => hu ⟨w, hw⟩)
      refine ⟨fun u hu => key u fun w => ?_, fun u hu => key u fun w => ?_⟩
      · have := hu w
        rwa [polarBilin_apply_apply, CFSG.LocalAnalysis.GLTheoremA.H81Orth.polar_comp_subtype' Q]
          at this
      · have := hu w
        rwa [polarBilin_apply_apply, CFSG.LocalAnalysis.GLTheoremA.H81Orth.polar_comp_subtype' Q,
          polar_comm] at this
    obtain ⟨b, hbo, hbQ⟩ := (QuadraticMap.nondegenerate_polar_iff.1 hQU).exists_orthogonal_basis
    refine ⟨b, fun i j hij => ?_, fun i => hbQ i⟩
    have := (hbo i j hij).polar_eq_zero
    rwa [CFSG.LocalAnalysis.GLTheoremA.H81Orth.polar_comp_subtype' Q] at this
  choose bas hbo hbQ using hbasis
  set D : Hyperplane ↥Aε p → K := fun H => ∏ k, Q (bas H k : Fin d → K) with hDdef
  have hD0 : ∀ H, D H ≠ 0 := fun H => Finset.prod_ne_zero_iff.2 fun k _ => hbQ H k
  have hexp : ∀ (H : Hyperplane ↥Aε p) (v : Fin d → K),
      ∑ k, ((Q (bas H k : Fin d → K))⁻¹ * polar Q (bas H k : Fin d → K) v) •
        (bas H k : Fin d → K) = (2 : K) • ρ.asAlgebraHom (eps K ↥Aε p (some H)) v := by
    intro H v
    have hmem : ρ.asAlgebraHom (eps K ↥Aε p (some H)) v ∈ weightSpace ρ H.1 := ⟨v, rfl⟩
    rw [← sum_orth_expansion Q (bas H) (hbo H) (hbQ H) hmem]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2
    have hk : ρ.asAlgebraHom (eps K ↥Aε p (some H)) (bas H k : Fin d → K) = bas H k :=
      eps_apply_of_mem ρ hp hA hpK (some H) (by rw [weightFamily_some]; exact (bas H k).2)
    conv_lhs => rw [← hk]
    exact polar_asAlgebraHom_eps_left ρ Q hρQ (some H) _ v
  have hpair : ∀ Ha Hb : Hyperplane ↥Aε p, Ha ≠ Hb → IsSquare (D Ha * D Hb) →
      glEquiv.symm (invol ρ hp hA hpK {Ha, Hb}) ∈ matrixDerived Q := by
    intro Ha Hb hab hsq
    set na := Module.finrank K (weightSpace ρ Ha.1)
    set nb := Module.finrank K (weightSpace ρ Hb.1)
    set e : Fin (na + nb) → Fin d → K :=
      Fin.append (fun k => (bas Ha k : Fin d → K)) (fun k => (bas Hb k : Fin d → K)) with hedef
    have hab' : (some Ha : Option (Hyperplane ↥Aε p)) ≠ some Hb := fun h =>
      hab (Option.some_injective _ h)
    have hcross : ∀ k l, polar Q (bas Ha k : Fin d → K) (bas Hb l : Fin d → K) = 0 :=
      fun k l => polar_eq_zero_of_mem_weightFamily ρ hp hA hpK Q hρQ hab'
        (by rw [weightFamily_some]; exact (bas Ha k).2)
        (by rw [weightFamily_some]; exact (bas Hb l).2)
    refine mem_matrixDerived_of_orthogonal_family h2 Q e ?_ ?_ ?_ ?_ ?_
    · intro i
      refine Fin.addCases (fun k => ?_) (fun l => ?_) i
      · rw [hedef, Fin.append_left]; exact hbQ Ha k
      · rw [hedef, Fin.append_right]; exact hbQ Hb l
    · intro i j hij
      induction i using Fin.addCases with
      | left k =>
        induction j using Fin.addCases with
        | left l =>
          rw [hedef, Fin.append_left, Fin.append_left]
          exact hbo Ha k l fun h => hij (by rw [h])
        | right l =>
          rw [hedef, Fin.append_left, Fin.append_right]
          exact hcross k l
      | right k =>
        induction j using Fin.addCases with
        | left l =>
          rw [hedef, Fin.append_right, Fin.append_left, polar_comm]
          exact hcross l k
        | right l =>
          rw [hedef, Fin.append_right, Fin.append_right]
          exact hbo Hb k l fun h => hij (by rw [h])
    · exact (even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 Ha).add
        (even_finrank_weightSpace ρ hp hA hpK Q hQ h2 hρQ hp2 Hb)
    · rw [Fin.prod_univ_add]
      simp only [hedef, Fin.append_left, Fin.append_right]
      exact hsq
    · intro v
      rw [MulEquiv.apply_symm_apply, invol_apply, projI_apply, Finset.sum_pair hab,
        Fin.sum_univ_add]
      simp only [hedef, Fin.append_left, Fin.append_right]
      rw [hexp Ha v, hexp Hb v, smul_add]
  have hsq : ∀ Ha Hb : Hyperplane ↥Aε p, quadraticChar K (D Ha) = quadraticChar K (D Hb) →
      IsSquare (D Ha * D Hb) := by
    intro Ha Hb h
    rw [← quadraticChar_one_iff_isSquare (mul_ne_zero (hD0 Ha) (hD0 Hb)), map_mul, ← h]
    rcases quadraticChar_dichotomy (hD0 Ha) with h1 | h1 <;> rw [h1] <;> norm_num
  by_cases e12 : quadraticChar K (D H₁) = quadraticChar K (D H₂)
  · exact Or.inl (hpair H₁ H₂ h12 (hsq H₁ H₂ e12))
  by_cases e13 : quadraticChar K (D H₁) = quadraticChar K (D H₃)
  · exact Or.inr (Or.inl (hpair H₁ H₃ h13 (hsq H₁ H₃ e13)))
  refine Or.inr (Or.inr (hpair H₂ H₃ h23 (hsq H₂ H₃ ?_)))
  rcases quadraticChar_dichotomy (hD0 H₁) with h1 | h1 <;>
    rcases quadraticChar_dichotomy (hD0 H₂) with h2' | h2' <;>
    rcases quadraticChar_dichotomy (hD0 H₃) with h3 | h3 <;>
    simp only [h1, h2', h3] at e12 e13 ⊢ <;> simp at e12 e13

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
