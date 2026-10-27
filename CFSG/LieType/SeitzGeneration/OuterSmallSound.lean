module

public import CFSG.LieType.SeitzGeneration.HeisSmallSound
public import CFSG.LieType.SeitzGeneration.UnitaryOuterB12
public import CFSG.LieType.SeitzGeneration.OuterSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

variable (ℓ f K) in
def GoodIn (H : Subgroup (unitarySU ℓ f K 3)) (A : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∃ g ∈ H, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = A

theorem goodIn_one (H : Subgroup (unitarySU ℓ f K 3)) : GoodIn ℓ f K H 1 := ⟨1, H.one_mem, rfl⟩

theorem goodIn_mul {H : Subgroup (unitarySU ℓ f K 3)} {A B : Matrix (Fin 3) (Fin 3) K}
    (hA : GoodIn ℓ f K H A) (hB : GoodIn ℓ f K H B) : GoodIn ℓ f K H (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := hB
  exact ⟨g * g', H.mul_mem hg hg', rfl⟩

section EvalW

variable {L : Type} [Field L]

theorem goodIn_evalW {H : Subgroup (unitarySU ℓ f K 3)} (ι : L →+* K) {letters : List (M3 L)}
    (hl : ∀ x ∈ letters, GoodIn ℓ f K H (toMat ι x)) :
    ∀ w : List ℕ, GoodIn ℓ f K H (toMat ι (evalW letters w))
  | [] => by simpa [evalW, toMat_one] using goodIn_one H
  | i :: w => by
    rw [evalW, toMat_mul]
    refine goodIn_mul ?_ (goodIn_evalW ι hl w)
    by_cases hi : i < letters.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hl _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
      exact goodIn_one H

end EvalW

theorem heisB12_le_of_cover {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData ℓ f K) (ι : L →+* K) (hι : Function.Surjective ι) {q : ℕ}
    (hq : ℓ ^ f = q) {H : Subgroup (unitarySU ℓ f K 3)} {letters : List (M3 L)}
    {ws₂ : List (List ℕ)} (hl : ∀ x ∈ letters, GoodIn ℓ f K H (toMat ι x))
    (hcov : CoverOk q (ws₂.map (evalW letters))) : heisB12 ℓ f K ≤ H := by
  subst hq
  have hL2 : ∀ x ∈ ws₂.map (evalW letters), GoodIn ℓ f K H (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodIn_evalW ι hl w
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hA
  obtain ⟨e10, e11, enorm⟩ := su2_entries h hdet hu
  obtain ⟨a, ha⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 0)
  obtain ⟨b, hb⟩ := hι ((A : Matrix (Fin 2) (Fin 2) K) 0 1)
  have hn : a * a ^ ℓ ^ f + b * b ^ ℓ ^ f = 1 := by
    apply ι.injective
    simp only [map_add, map_mul, map_pow, ha, hb, enorm, map_one]
  obtain ⟨g', hg', hgg⟩ := hL2 _ (hcov a b hn)
  have hmat : toMat ι (blockM3 (ℓ ^ f) a b) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hgA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, blockM3, ha, hb, e10, e11]
  have : g' = g := Subtype.ext (Units.ext (hgg.trans hmat))
  exact this ▸ hg'

section Lines

variable {L : Type} [Field L]

theorem toMat_cM3 (ι : L →+* K) (α₀ : L) : toMat ι (cM3 α₀) = heisC (ι α₀) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, cM3, heisC]

theorem toMat_dM3_heisD (ι : L →+* K) (ω₀ : L) : toMat ι (dM3 ω₀) = heisD (ι ω₀) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, dM3, heisD, Matrix.diagonal]

theorem toMat_mem_outerHeisLines (ι : L →+* K) {ω₀ α₀ : L} {M : M3 L}
    (hM : M ∈ outerLineList ω₀ α₀) : toMat ι M ∈ outerHeisLines (ι ω₀) (ι α₀) := by
  simp only [outerLineList, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · simp [outerHeisLines, toMat_cM3]
  · simp [outerHeisLines, toMat_dM3_heisD]
  · simp [outerHeisLines, toMat_mul, toMat_cM3, toMat_dM3_heisD]
  · simp [outerHeisLines, toMat_mul, toMat_cM3, toMat_dM3_heisD, sq]

end Lines

theorem goodIn_outer_of_gen (h : UnitaryFieldData ℓ f K) {ω α : K}
    {A M : Matrix (Fin 3) (Fin 3) K} (hdet : A.det = 1) (hu : (A.map h.bar)ᵀ * A = 1)
    (hM : M ∈ outerHeisLines ω α) {c : K} (hc : A * M = c • (M * A)) :
    GoodIn ℓ f K (outerHeisClosure ℓ f K ω α) A := by
  let g : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL ⟨A, hdet⟩
  have hg : g ∈ unitarySU ℓ f K 3 := (mem_unitarySU_iff h).2 ⟨hdet, hu⟩
  exact ⟨⟨g, hg⟩, Subgroup.subset_closure ⟨M, hM, c, hc⟩, rfl⟩

theorem outerB12_le_of_check {L : Type} [Field L] [DecidableEq L] [Fintype L]
    (h : UnitaryFieldData ℓ f K) {ω₀ : L} {ω α : K} (ι : L →+* K) (hι : Function.Surjective ι)
    (hιω : ι ω₀ = ω) {q : ℕ} (hq : ℓ ^ f = q) (hα : α ^ (ℓ ^ f + 1) = 1)
    (hαc : ¬ ∃ μ : K, μ ^ 3 = α) {letters : List (M3 L)} {ws₂ : List (List ℕ)}
    {table : List (OuterEntry L)} (hcheck : outerCheck q ω₀ letters ws₂ table = true) :
    heisB12 ℓ f K ≤ outerHeisClosure ℓ f K ω α := by
  subst hιω hq
  unfold outerCheck at hcheck
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
  obtain ⟨⟨hcov, htab⟩, hcovα⟩ := hcheck
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
  unfold entryOk at hent
  rw [Bool.and_eq_true, List.all_eq_true] at hent
  obtain ⟨hgens, hwords⟩ := hent
  rw [heα] at hgens
  have hG : ∀ G ∈ e.gens, GoodIn ℓ f K (outerHeisClosure ℓ f K (ι ω₀) (ι α₀)) (toMat ι G) := by
    intro G hG
    obtain ⟨hdet, hu, M, hM, c, hc⟩ := of_decide_eq_true (hgens G hG)
    refine goodIn_outer_of_gen h (c := ι c) ?_ ?_ (toMat_mem_outerHeisLines ι hM) ?_
    · rw [toMat_det, hdet, map_one]
    · rw [← toMat_transpose_map h, ← toMat_mul, hu, toMat_one]
    · have := congrArg (toMat ι) hc
      rwa [toMat_mul, toMat_smul, toMat_mul] at this
  have hwords' : e.words.map (evalW e.gens) = letters := of_decide_eq_true hwords
  have hl : ∀ x ∈ letters, GoodIn ℓ f K (outerHeisClosure ℓ f K (ι ω₀) (ι α₀)) (toMat ι x) := by
    intro x hx
    rw [← hwords'] at hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact goodIn_evalW ι hG w
  exact heisB12_le_of_cover h ι hι rfl hl (of_decide_eq_true hcov)

end CFSG.LieType.SeitzGeneration.HeisSmall
