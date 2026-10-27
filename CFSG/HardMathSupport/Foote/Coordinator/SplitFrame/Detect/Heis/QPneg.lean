module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalOpposite

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false



variable (τ : Tag) (K : Type) [Field K]

private theorem eq_highRoot_of_height_le (τ : Tag) :
    ∀ α ∈ rootFinset τ, height (highRoot τ) ≤ height α → α = highRoot τ := by
  cases τ <;> decide +kernel

private theorem Qθ_inf_Pneg_of_conj {n : ModGL τ K} (hnC : n ∈ adjointGroup τ K)
    (hnU : conjSub n (Uθ τ K) = Uneg τ K)
    (hle : (Qθ τ K).map (MulAut.conj n⁻¹).toMonoidHom ≤
      EvenOddRadical.oppRadical τ K (Jθ τ)) :
    Qθ τ K ⊓ Pneg τ K = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, hgP⟩ := hg
  obtain ⟨hgC, hgN⟩ : g ∈ adjointGroup τ K ∧
      g ∈ Subgroup.normalizer (Uneg τ K : Set (ModGL τ K)) := hgP
  have hhC : n⁻¹ * g * n ∈ adjointGroup τ K := mul_mem (mul_mem (inv_mem hnC) hgC) hnC
  have hgU : conjSub g (Uneg τ K) = Uneg τ K := map_conj_eq_of_mem_normalizer hgN
  have hhU : conjSub (n⁻¹ * g * n) (Uθ τ K) = Uθ τ K := by
    rw [conjSub_mul, conjSub_mul, hnU, hgU, ← hnU, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hhP : n⁻¹ * g * n ∈ Pθ τ K :=
    normalizer_Uθ_le_Pθ τ K hhC (mem_normalizer_of_conjSub_eq hhU)
  have hhQ : n⁻¹ * g * n ∈ EvenOddRadical.oppRadical τ K (Jθ τ) := by
    simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hgQ)
  have h1 : n⁻¹ * g * n ∈
      parabolicSubgroup τ K (Jθ τ) ⊓ EvenOddRadical.oppRadical τ K (Jθ τ) := ⟨hhP, hhQ⟩
  rw [EvenOddRadical.parabolicSubgroup_inf_oppRadical, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem Qθ_inf_Pneg : Qθ τ K ⊓ Pneg τ K = ⊥ := by
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := EvenOddRadical.exists_longest τ
  have hht : ∀ v : Fin τ.rank → ℤ, height (w₀ • v) = -height v := fun v => by
    simpa [parabolicDegree, height] using EvenOddRadical.parabolicDegree_longest hinj hδ ∅ v
  have hθ : w₀ • highRoot τ = -highRoot τ :=
    neg_eq_iff_eq_neg.1 (eq_highRoot_of_height_le τ _
      (mem_rootFinset.2 (IsRoot.neg (IsRoot.smul (isRoot_highRoot τ) w₀)))
      (le_of_eq (by rw [height_neg, hht, neg_neg])))
  have hflip : ∀ v : Fin τ.rank → ℤ, (w₀ • v) (iθ τ) = -v (iθ τ) := fun v => by
    have h1 := iform_smul w₀ (highRoot τ) v
    rw [hθ, ← neg_one_smul ℤ (highRoot τ), iform_smul_left, iform_highRoot_apply,
      iform_highRoot_apply] at h1
    exact mul_left_cancel₀ (cθ_ne_zero τ) (by linear_combination (-1 : ℤ) * h1)
  have hδiθ : δ (iθ τ) = iθ τ := by
    have h := hflip (Pi.single (iθ τ) 1)
    rw [hδ] at h
    by_contra hne
    simp [Pi.single_apply, Ne.symm hne] at h
  have hδJ : δ '' Jθ τ = Jθ τ := by
    have hsurj : Function.Surjective δ := Finite.injective_iff_surjective.1 hinj
    ext k
    constructor
    · rintro ⟨i, hi, rfl⟩ h
      exact hi (hinj (h.trans hδiθ.symm))
    · intro hk
      obtain ⟨i, rfl⟩ := hsurj k
      exact ⟨i, fun h => hk (by rw [h]; exact hδiθ), rfl⟩
  obtain ⟨-, hRS, -⟩ := canonical_weyl_root_transport τ K
  have hle := EvenOddRadical.map_conj_longest_parabolicRadical_le (K := K) hinj hδ hsq h₀ (Jθ τ)
  rw [hδJ] at hle
  refine Qθ_inf_Pneg_of_conj τ K (canonicalRep_mem_adjointGroup _ K w₀) ?_ hle
  show (rootSubgroup τ K (highRoot τ)).map _ = _
  rw [hRS w₀ _ (isRoot_highRoot τ), hθ]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
