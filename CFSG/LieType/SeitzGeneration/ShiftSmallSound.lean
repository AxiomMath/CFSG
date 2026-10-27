module

public import CFSG.LieType.SeitzGeneration.OuterSmallSound
public import CFSG.LieType.SeitzGeneration.ShiftSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

variable (ℓ f K) in
@[expose] def GoodInS (H : Subgroup (unitarySU ℓ f K 3)) (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ g ∈ H, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A

theorem goodInS_one (H : Subgroup (unitarySU ℓ f K 3)) : GoodInS ℓ f K H 1 :=
  ⟨1, H.one_mem, rfl⟩

theorem goodInS_mul {H : Subgroup (unitarySU ℓ f K 3)} {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : GoodInS ℓ f K H A) (hB : GoodInS ℓ f K H B) : GoodInS ℓ f K H (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := hB
  exact ⟨g * g', H.mul_mem hg hg', rfl⟩

theorem goodInS_evalW {L : Type} [Field L] {H : Subgroup (unitarySU ℓ f K 3)} (ι : L →+* K)
    {letters : List (M3 L)} (hl : ∀ x ∈ letters, GoodInS ℓ f K H (toMat ι x)) :
    ∀ w : List ℕ, GoodInS ℓ f K H (toMat ι (evalW letters w))
  | [] => by simpa [evalW, toMat_one] using goodInS_one H
  | i :: w => by
    rw [evalW, toMat_mul]
    refine goodInS_mul ?_ (goodInS_evalW ι hl w)
    by_cases hi : i < letters.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hl _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
      exact goodInS_one H

theorem goodIn_exact_of_gen (h : UnitaryFieldData ℓ f K) {ω α : K}
    {A M : Matrix (Fin 3) (Fin 3) K} (hdet : A.det = 1) (hu : (A.map h.bar)ᵀ * A = 1)
    (hM : M ∈ outerHeisLines ω α) (hc : A * M = M * A) :
    GoodInS ℓ f K (Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ outerHeisLines ω α,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)}) A := by
  let g : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL ⟨A, hdet⟩
  have hg : g ∈ unitarySU ℓ f K 3 := (mem_unitarySU_iff h).2 ⟨hdet, hu⟩
  exact ⟨⟨g, hg⟩, Subgroup.subset_closure ⟨M, hM, hc⟩, rfl⟩

theorem shift_mem_exact_of_check {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData ℓ f K) {ω₀ : L} {ω α : K} (ι : L →+* K) (hι : Function.Surjective ι)
    (hιω : ι ω₀ = ω) {q : ℕ} (hq : ℓ ^ f = q) (hα : α ^ (ℓ ^ f + 1) = 1)
    (hαc : ¬ ∃ μ : K, μ ^ 3 = α) {table : List (OuterEntry L)}
    (hcheck : shiftCheck q ω₀ table = true) :
    ∃ s : unitarySU ℓ f K 3, ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = hS ∧
      s ∈ Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ outerHeisLines ω α,
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
          M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)} := by
  subst hιω hq
  unfold shiftCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨htab, hcovα⟩ := hcheck
  rw [List.all_eq_true] at htab
  obtain ⟨α₀, rfl⟩ := hι α
  have hα₀ : α₀ ^ (ℓ ^ f + 1) = 1 := by
    apply ι.injective
    rw [map_pow, map_one]
    exact hα
  have hαc₀ : ¬ ∃ μ : L, μ ^ 3 = α₀ := by
    rintro ⟨μ, hμ⟩
    exact hαc ⟨ι μ, by rw [← map_pow, hμ]⟩
  obtain ⟨e, he, heα⟩ := of_decide_eq_true hcovα α₀ hα₀ hαc₀
  have hent := htab e he
  unfold shiftEntryOk at hent
  rw [Bool.and_eq_true, List.all_eq_true] at hent
  obtain ⟨hgens, hwords⟩ := hent
  rw [heα] at hgens
  have hG : ∀ G ∈ e.gens, GoodInS ℓ f K
      (Subgroup.closure {g : unitarySU ℓ f K 3 | ∃ M ∈ outerHeisLines (ι ω₀) (ι α₀),
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
          M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)}) (toMat ι G) := by
    intro G hG
    obtain ⟨hdet, hu, M, hM, hc⟩ := of_decide_eq_true (hgens G hG)
    have hM' : toMat ι M ∈ outerHeisLines (ι ω₀) (ι α₀) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl
      · simp [outerHeisLines, toMat_cM3]
      · simp [outerHeisLines, toMat_dM3_heisD]
    refine goodIn_exact_of_gen h ?_ ?_ hM' ?_
    · rw [toMat_det, hdet, map_one]
    · rw [← toMat_transpose_map h, ← toMat_mul, hu, toMat_one]
    · have := congrArg (toMat ι) hc
      rwa [toMat_mul, toMat_mul] at this
  have hwords' : e.words.map (evalW e.gens) = [sM3] := of_decide_eq_true hwords
  have hmem : sM3 ∈ e.words.map (evalW e.gens) := by
    rw [hwords']
    exact List.mem_singleton_self _
  obtain ⟨w, -, hw⟩ := List.mem_map.1 hmem
  have hgood := goodInS_evalW ι hG w
  rw [hw, toMat_sM3] at hgood
  obtain ⟨s, hs, hsmat⟩ := hgood
  exact ⟨s, hsmat, hs⟩

end CFSG.LieType.SeitzGeneration.HeisSmall
