module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus7
public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusSix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {Q : QuadraticForm F W}

private def b0 (k : ℕ) (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

private def b1 (k : ℕ) (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

private theorem b0_ne_b1 (k : ℕ) (j : Fin k) : b0 k j ≠ b1 k j := by
  intro h
  have := congrArg Fin.val h
  simp [b0, b1] at this

private theorem b0_ne_b0 {k : ℕ} {i j : Fin k} (hij : i ≠ j) : b0 k i ≠ b0 k j := by
  intro h
  apply hij
  apply Fin.ext
  have := congrArg Fin.val h
  simp [b0] at this
  omega

private theorem b0_ne_b1' {k : ℕ} {i j : Fin k} (hij : i ≠ j) : b0 k i ≠ b1 k j := by
  intro h
  have := congrArg Fin.val h
  simp [b0, b1] at this
  omega

private theorem b1_ne_b1 {k : ℕ} {i j : Fin k} (hij : i ≠ j) : b1 k i ≠ b1 k j := by
  intro h
  apply hij
  apply Fin.ext
  have := congrArg Fin.val h
  simp [b1] at this
  omega

private noncomputable def blockPlane {k : ℕ} (P : Fin (2 * k) → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    Fin k × Fin 2 → PlaneFrame Q := fun i =>
  if hi : i.2 = 0 then
    plusPlaneA (P (b0 k i.1)) (P (b1 k i.1)) (hP _ _ (b0_ne_b1 k i.1)) c hc
  else
    plusPlaneB (P (b0 k i.1)) (P (b1 k i.1)) (hP _ _ (b0_ne_b1 k i.1)) c hc

private theorem blockPlane_zero {k : ℕ} (P : Fin (2 * k) → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0)
    (i : Fin k × Fin 2) (hi : i.2 = 0) :
    blockPlane P hP c hc i =
      plusPlaneA (P (b0 k i.1)) (P (b1 k i.1)) (hP _ _ (b0_ne_b1 k i.1)) c hc := by
  simp [blockPlane, hi]

private theorem blockPlane_one {k : ℕ} (P : Fin (2 * k) → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0)
    (i : Fin k × Fin 2) (hi : i.2 ≠ 0) :
    blockPlane P hP c hc i =
      plusPlaneB (P (b0 k i.1)) (P (b1 k i.1)) (hP _ _ (b0_ne_b1 k i.1)) c hc := by
  simp [blockPlane, hi]

private theorem blockPlane_orthogonal {k : ℕ} (P : Fin (2 * k) → HypPair Q)
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (c : F)
    (hc : ∀ s t : F, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    ∀ i j : Fin k × Fin 2, i ≠ j → (blockPlane P hP c hc i).A ≤
      perp Q (blockPlane P hP c hc j).A := by
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ hij
  by_cases hsame : i₁ = j₁
  · subst hsame
    by_cases hi : i₂ = 0
    · have hj : j₂ ≠ 0 := by
        intro hj0
        apply hij
        rw [hi, hj0]
      rw [blockPlane_zero P hP c hc (i₁, i₂) hi,
        blockPlane_one P hP c hc (i₁, j₂) hj]
      exact plusPlane_orthogonal _ _ _ _ _
    · have hj : j₂ = 0 := by
        by_contra hj0
        apply hij
        have hi1 : i₂ = 1 := by
          apply Fin.ext
          have h0 : i₂.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
          have := i₂.isLt
          omega
        have hj1 : j₂ = 1 := by
          apply Fin.ext
          have h0 : j₂.val ≠ 0 := fun h => hj0 (Fin.ext (by simpa using h))
          have := j₂.isLt
          omega
        rw [hi1, hj1]
      rw [blockPlane_one P hP c hc (i₁, i₂) hi,
        blockPlane_zero P hP c hc (i₁, j₂) hj]
      intro x hx
      rw [mem_perp]
      intro y hy
      rw [polar_comm]
      exact mem_perp.mp (plusPlane_orthogonal _ _ _ _ _ hy) x hx
  · have hb00 := b0_ne_b0 hsame
    have hb01 := b0_ne_b1' hsame
    have hb10 : b1 k i₁ ≠ b0 k j₁ := (b0_ne_b1' (Ne.symm hsame)).symm
    have hb11 := b1_ne_b1 hsame
    have hcross : blockSpan (P (b0 k i₁)) (P (b1 k i₁)) ≤
        perp Q (blockSpan (P (b0 k j₁)) (P (b1 k j₁))) :=
      blockSpan_orthogonal (hP _ _ hb00) (hP _ _ hb01) (hP _ _ hb10) (hP _ _ hb11)
    have hDi : (blockPlane P hP c hc (i₁, i₂)).A ≤
        blockSpan (P (b0 k i₁)) (P (b1 k i₁)) := by
      by_cases hi : i₂ = 0
      · rw [blockPlane_zero P hP c hc (i₁, i₂) hi]
        exact plusPlaneA_subset _ _ _ _ _
      · rw [blockPlane_one P hP c hc (i₁, i₂) hi]
        exact plusPlaneB_subset _ _ _ _ _
    have hDj : (blockPlane P hP c hc (j₁, j₂)).A ≤
        blockSpan (P (b0 k j₁)) (P (b1 k j₁)) := by
      by_cases hj : j₂ = 0
      · rw [blockPlane_zero P hP c hc (j₁, j₂) hj]
        exact plusPlaneA_subset _ _ _ _ _
      · rw [blockPlane_one P hP c hc (j₁, j₂) hj]
        exact plusPlaneB_subset _ _ _ _ _
    exact hDi.trans (hcross.trans (perp_anti hDj))

theorem omHypRankLower_holds : OmHypRankLower := by
  intro F W _ _ _ _ _ _ Q k P hP r hr hr2 hrdvd
  classical
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.exists_anisotropic_form F
  let D : Fin k × Fin 2 → PlaneFrame Q := blockPlane P hP c hc
  have horth : ∀ i j, i ≠ j → (D i).A ≤ perp Q (D j).A :=
    blockPlane_orthogonal P hP c hc
  obtain ⟨T, hTelem, hTrank⟩ :=
    exists_elemAbelian_of_planeFrames_in (Q := Q) hr hr2 hrdvd D horth
  have hcard : Nat.card (Fin k × Fin 2) = 2 * k := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_fin]
    ring
  have hle : 2 * k ≤ CFSG.Open.pRank r T := by
    rw [← hcard]
    exact hTrank
  exact le_trans hle (CFSG.SectionRank.pRank_mono hr.one_lt le_top)

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F
