module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusCuts
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniCuts

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix QuadraticMap CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def plusFlagStab (r : ℕ) (D : Finset ℕ) :
    Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :=
  orthElementaryGroup (quadPlus r K) ⊓
    ⨅ d ∈ D, MulAction.stabilizer ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K d)

theorem mem_plusFlagStab {D : Finset ℕ} {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} :
    g ∈ plusFlagStab K r D ↔ g ∈ orthElementaryGroup (quadPlus r K) ∧
      ∀ d ∈ D, g • flag r K d = flag r K d := by
  simp only [plusFlagStab, Subgroup.mem_inf, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem mem_orthogonalGroup_of_mem_plusFlagStab {D : Finset ℕ}
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hg : g ∈ plusFlagStab K r D) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K) :=
  orthElementaryGroup_le _ (mem_plusFlagStab.1 hg).1

theorem smul_flag_of_mem_plusFlagStab {D : Finset ℕ}
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hg : g ∈ plusFlagStab K r D) {c : ℕ}
    (hc : c = 0 ∨ c ∈ D) : g • flag r K c = flag r K c := by
  rcases hc with rfl | hc
  · change Submodule.map (g : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) (flag r K 0) = _
    rw [flag_zero, Submodule.map_bot]
  · exact (mem_plusFlagStab.1 hg).2 c hc

theorem plusCut_of_mem_plusFlagStab {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r)
    {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hg : g ∈ plusFlagStab K r D) {c : ℕ}
    (hc : c = 0 ∨ c ∈ D) : PlusCut g c ∧ PlusCut g (2 * r - c) := by
  have hcr : c ≤ r := hc.elim (fun h => by omega) (hD c)
  have hs := smul_flag_of_mem_plusFlagStab hg hc
  exact ⟨plusCut_of_smul_flag hcr hs,
    plusCut_of_smul_flag_orthogonal (mem_orthogonalGroup_of_mem_plusFlagStab hg) hcr hs⟩

@[expose] def plusEIdx {a b : ℕ} (hb : b ≤ r) (k : Fin (b - a)) : Fin r ⊕ Fin r :=
  Sum.inl ⟨a + k, by have := k.isLt; omega⟩

theorem plusEIdx_injective {a b : ℕ} (hb : b ≤ r) : Function.Injective (plusEIdx (a := a) hb) := by
  intro k k' h
  have := congrArg Fin.val (Sum.inl_injective h)
  exact Fin.ext (by simpa using this)

theorem mem_range_plusEIdx {a b : ℕ} (hb : b ≤ r) (x : Fin r ⊕ Fin r) :
    x ∈ Set.range (plusEIdx (a := a) hb) ↔ a ≤ plusPos r x ∧ plusPos r x < b := by
  constructor
  · rintro ⟨k, rfl⟩
    simp only [plusEIdx, plusPos_inl]
    have := k.isLt
    omega
  · intro h
    rcases x with j | j
    · rw [plusPos_inl] at h
      exact ⟨⟨j - a, by omega⟩, by simp only [plusEIdx]; congr 1; ext; simp; omega⟩
    · rw [plusPos_inr] at h
      have := j.isLt
      omega

@[expose] noncomputable def plusEBlockHom {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ}
    (hb : b ∈ D) : ↥(plusFlagStab K r D) →* GL (Fin (b - predCut D b)) K :=
  plusBlockHom _ (plusEIdx_injective (hD b hb))
    (mem_range_plusEIdx (hD b hb))
    (fun _ hg => (plusCut_of_mem_plusFlagStab hD hg ((predCut_eq_zero_or_mem D b))).1)
    (fun _ hg => (plusCut_of_mem_plusFlagStab hD hg (Or.inr hb)).1)

theorem coe_plusEBlockHom {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {b : ℕ} (hb : b ∈ D)
    (g : ↥(plusFlagStab K r D)) :
    ((plusEBlockHom hD hb g : GL (Fin (b - predCut D b)) K) :
      Matrix (Fin (b - predCut D b)) (Fin (b - predCut D b)) K) =
      (autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _)).submatrix (plusEIdx (hD b hb))
        (plusEIdx (hD b hb)) :=
  rfl

@[expose] def plusResIdx {t m : ℕ} (htm : t + m = r) : Fin m ⊕ Fin m → Fin r ⊕ Fin r :=
  Sum.map (fun s => ⟨t + s, by have := s.isLt; omega⟩) (fun s => ⟨t + s, by have := s.isLt; omega⟩)

theorem plusResIdx_inl {t m : ℕ} (htm : t + m = r) (s : Fin m) :
    plusResIdx htm (Sum.inl s) = Sum.inl ⟨t + s, by have := s.isLt; omega⟩ := rfl

theorem plusResIdx_inr {t m : ℕ} (htm : t + m = r) (s : Fin m) :
    plusResIdx htm (Sum.inr s) = Sum.inr ⟨t + s, by have := s.isLt; omega⟩ := rfl

theorem plusResIdx_injective {t m : ℕ} (htm : t + m = r) :
    Function.Injective (plusResIdx htm) := by
  refine Sum.map_injective.2 ⟨fun s s' h => ?_, fun s s' h => ?_⟩ <;>
  · have := congrArg Fin.val h
    exact Fin.ext (by simpa using this)

theorem mem_range_plusResIdx {t m : ℕ} (htm : t + m = r) (x : Fin r ⊕ Fin r) :
    x ∈ Set.range (plusResIdx htm) ↔ t ≤ plusPos r x ∧ plusPos r x < 2 * r - t := by
  constructor
  · rintro ⟨s | s, rfl⟩
    · rw [plusResIdx_inl, plusPos_inl]
      have := s.isLt
      simp only
      omega
    · rw [plusResIdx_inr, plusPos_inr]
      have := s.isLt
      simp only
      omega
  · intro h
    rcases x with j | j
    · rw [plusPos_inl] at h
      exact ⟨Sum.inl ⟨j - t, by omega⟩, by rw [plusResIdx_inl]; congr 1; ext; simp; omega⟩
    · rw [plusPos_inr] at h
      have := j.isLt
      exact ⟨Sum.inr ⟨j - t, by omega⟩, by rw [plusResIdx_inr]; congr 1; ext; simp; omega⟩

@[expose] noncomputable def plusResBlockHom {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) :
    ↥(plusFlagStab K r D) →* GL (Fin m ⊕ Fin m) K :=
  plusBlockHom _ (plusResIdx_injective htm) (mem_range_plusResIdx htm)
    (fun _ hg => (plusCut_of_mem_plusFlagStab hD hg ht).1)
    (fun _ hg => (plusCut_of_mem_plusFlagStab hD hg ht).2)

theorem coe_plusResBlockHom {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D)
    (htm : t + m = r) (g : ↥(plusFlagStab K r D)) :
    ((plusResBlockHom hD ht htm g : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      (autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _)).submatrix (plusResIdx htm) (plusResIdx htm) :=
  rfl

end CFSG.AGLEmbedding.LeviBlock
