module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighClassical
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus StatedLieAdmissible
  StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut (matrixProjectiveImage_eq_top_minus)

theorem exists_descent_om {n ℓ e : ℕ} (hn : 4 ≤ n) (hn1 : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hℓ : ℓ.Prime) (hℓ3 : (3 : ℕ) ≠ ℓ) (he : 1 ≤ e) {k : Subfield K} (hk : Nat.card k = ℓ ^ e)
    (hK : Nat.card K = ℓ ^ (e * 3)) {σ₀ : K ≃+* K} (hσ₀ : orderOf σ₀ = 3)
    (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)))}
    (hα : IsOuterOfOrder 3 α) :
    ∃ ι : matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c) →*
        matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)),
      Function.Injective ι ∧ (∀ v, α (ι v) = ι v) ∧ (∀ x, α x = x → x ∈ ι.range) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ e * 3 := Nat.mul_pos he (by norm_num)
  have hfixall := fun σ (h : orderOf σ = 3) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * 3) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * 3) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * 3) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ (e * 3) 3 hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, hDlin, σ, hσ, hαeq⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) (by
      intro U Q₀ hord hdisp
      obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      have hfixV := hfixall U.val.right hord
      have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
        fun x => RingHom.mem_eqLocusField
      have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
      have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
      have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
        hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
      have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
        intro s hs hz
        have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
        exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
      obtain ⟨μ, hμk, hμQ⟩ :=
        SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
      have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
        Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
      refine ⟨μ * S, ν', fun v => ?_, ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (hμQ _).trans (hSQ v)
      · rw [mul_assoc, hSA, map_mul, hμσ])
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ e 3 ⟨hℓ, he, hn⟩ hp hp2 hℓ3 hn1 K k hk hK σ hσ (hfixall σ hσ)
      b c hirr
  have hNJ' := subfieldFixedGroup_le_minus ⟨hℓ, he, hn⟩ hp hp2 hn1 k hk hK σ hσ (hfixall σ hσ)
    b c hirr
  obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
  have hrange : fixedSubgroup (fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
      (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c)) =
      (incl k (coordinateQuadMinus_isExtension k n hn1 b c)).range :=
    (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
  have hfixι : ∀ y ∈ (incl k (coordinateQuadMinus_isExtension k n hn1 b c)).range,
      fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
        (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c) y = y := fun y hy =>
    mem_fixedSubgroup.1 (hrange ▸ hy)
  refine ⟨D.toMonoidHom.comp (incl k (coordinateQuadMinus_isExtension k n hn1 b c)),
    D.injective.comp hinj, ?_, ?_⟩
  · intro v
    show α (D (incl k (coordinateQuadMinus_isExtension k n hn1 b c) v)) =
      D (incl k (coordinateQuadMinus_isExtension k n hn1 b c) v)
    rw [hαeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hfixι _ ⟨v, rfl⟩]
  · intro x hx
    have h1 : fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
        (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c) (D⁻¹ x) = D⁻¹ x := by
      rw [hαeq, MulAut.mul_apply, MulAut.mul_apply] at hx
      have h2 : D (fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
          (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c) (D⁻¹ x)) = D (D⁻¹ x) := by
        rw [hx, MulAut.apply_inv_self]
      exact D.injective h2
    have h3 : D⁻¹ x ∈ (incl k (coordinateQuadMinus_isExtension k n hn1 b c)).range :=
      hrange ▸ mem_fixedSubgroup.2 h1
    obtain ⟨v, hv⟩ := h3
    refine ⟨v, ?_⟩
    show D (incl k (coordinateQuadMinus_isExtension k n hn1 b c) v) = x
    rw [hv, MulAut.apply_inv_self]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
