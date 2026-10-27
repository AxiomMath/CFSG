module

public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusSix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmTorus7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open QuadraticMap CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2

namespace OmTorus

variable {F W : Type} [Field F] [Finite F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W] {Q : QuadraticForm F W}

private noncomputable def tailFrame (u v : W) (hQu : Q u = 1) (hbv : polar Q u v ≠ 0)
    (hirr : ∀ s : F, s ^ 2 + polar Q u v * s + Q v ≠ 0) : PlaneFrame Q where
  A := Submodule.span F {u, v}
  u := u
  v := v
  hu := Submodule.subset_span (Set.mem_insert _ _)
  hv := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  hQu := hQu
  hbv := hbv
  hirr := hirr
  hspan := rfl

private def fin3OfFin {n : ℕ} (hn : 3 ≤ n) (i : Fin 3) : Fin n :=
  ⟨i.val, by have := i.isLt; omega⟩

private theorem fin3OfFin_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (fin3OfFin hn) := by
  intro i j h
  apply Fin.ext
  simpa [fin3OfFin] using congrArg Fin.val h

private theorem pairSpan_le_perp_of_tail {P : HypPair Q} {u v : W}
    (hu : u ∈ P.perp) (hv : v ∈ P.perp) :
    Submodule.span F {u, v} ≤ perp Q (Submodule.span F {P.e, P.f}) := by
  intro x hx
  rw [Submodule.mem_span_pair] at hx
  obtain ⟨α, β, rfl⟩ := hx
  rw [mem_perp]
  intro y hy
  rw [Submodule.mem_span_pair] at hy
  obtain ⟨γ, δ, rfl⟩ := hy
  obtain ⟨hu1, hu2⟩ := HypPair.mem_perp.mp hu
  obtain ⟨hv1, hv2⟩ := HypPair.mem_perp.mp hv
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq]
  rw [hu1, hu2, hv1, hv2]
  ring

theorem omTorusThree_holds : OmTorusThree := by
  intro F W _ _ _ _ _ _ Q hQ h8 q hq hq2 hqF
  classical
  obtain ⟨n, hn0⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hn : Module.finrank F W = 2 * n := by omega
  have hn4 : 4 ≤ n := by
    have := h8
    omega
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.exists_anisotropic_form F
  rcases CFSG.ComponentClassification.UnbalancedCatalog.exists_hypPairs_normal (Q := Q) n ⊤
      (polarNondegOn_top hQ) (by rw [finrank_top]; exact hn) with
    ⟨P, hPmem, hPorth⟩ | ⟨m, hm, P, u, v, hPmem, hPorth, hu, hv, huperp, hQu, hbuv, hirr⟩
  ·
    have hn3 : 3 ≤ n := by omega
    rcases hqF with hqminus | hqplus
    ·
      let P3 : Fin 3 → HypPair Q := fun i => P (fin3OfFin hn3 i)
      refine omTorusThree_hyp hQ q hq hq2 hqminus P3 ?_
      intro i j hij
      exact hPorth _ _ (fun h => hij (fin3OfFin_injective hn3 h))
    ·
      have h01 : (P ⟨0, by omega⟩).Orth (P ⟨1, by omega⟩) :=
        hPorth _ _ (by intro h; have := congrArg Fin.val h; simp at this)
      have h23 : (P ⟨2, by omega⟩).Orth (P ⟨3, by omega⟩) :=
        hPorth _ _ (by intro h; have := congrArg Fin.val h; simp at this)
      let A1 := plusPlaneA (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
      let A2 := plusPlaneB (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
      let A3 := plusPlaneA (P ⟨2, by omega⟩) (P ⟨3, by omega⟩) h23 c hc
      have hA1 : A1.A ≤ blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) :=
        plusPlaneA_subset _ _ _ _ _
      have hA2 : A2.A ≤ blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) :=
        plusPlaneB_subset _ _ _ _ _
      have hA3 : A3.A ≤ blockSpan (P ⟨2, by omega⟩) (P ⟨3, by omega⟩) :=
        plusPlaneA_subset _ _ _ _ _
      have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      have h03 : (⟨0, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      have h13' : (⟨1, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      have hb0 : blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) ≤
          perp Q (blockSpan (P ⟨2, by omega⟩) (P ⟨3, by omega⟩)) :=
        blockSpan_orthogonal (hPorth _ _ h02) (hPorth _ _ h03)
          (hPorth _ _ h12) (hPorth _ _ h13')
      have hblock : blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) ≤
          perp Q (blockSpan (P ⟨2, by omega⟩) (P ⟨3, by omega⟩)) := hb0
      have h13 : A1.A ≤ perp Q A3.A := hA1.trans (hblock.trans (perp_anti hA3))
      have h23' : A2.A ≤ perp Q A3.A := hA2.trans (hblock.trans (perp_anti hA3))
      have h31 : A3.A ≤ perp Q A1.A := by
        intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
        exact mem_perp.mp (h13 hy) x hx
      have h32 : A3.A ≤ perp Q A2.A := by
        intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
        exact mem_perp.mp (h23' hy) x hx
      let D : Fin 3 → PlaneFrame Q := fun i =>
        if i = 0 then A1 else if i = 1 then A2 else A3
      have horth : ∀ i j, i ≠ j → (D i).A ≤ perp Q (D j).A := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact plusPlane_orthogonal (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
        · exact h13
        · intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
          exact mem_perp.mp
            (plusPlane_orthogonal (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc hy) x hx
        · exact absurd rfl hij
        · exact h23'
        · exact h31
        · exact h32
        · exact absurd rfl hij
      obtain ⟨T, hTH, hTelem, hTrank⟩ :=
        exists_elemAbelian_of_planeFrames hq hq2 hqplus D horth
      refine ⟨T, hTH, hTelem, ?_⟩
      simpa [Nat.card_fin] using hTrank
  ·
    have hm3 : 3 ≤ m := by omega
    rcases hqF with hqminus | hqplus
    ·
      let P3 : Fin 3 → HypPair Q := fun i => P (fin3OfFin hm3 i)
      refine omTorusThree_hyp hQ q hq hq2 hqminus P3 ?_
      intro i j hij
      exact hPorth _ _ (fun h => hij (fin3OfFin_injective hm3 h))
    ·
      have h01 : (P ⟨0, by omega⟩).Orth (P ⟨1, by omega⟩) :=
        hPorth _ _ (by intro h; have := congrArg Fin.val h; simp at this)
      let A1 := plusPlaneA (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
      let A2 := plusPlaneB (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
      let A3 := tailFrame u v hQu hbuv hirr
      have hA1 : A1.A ≤ blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) :=
        plusPlaneA_subset _ _ _ _ _
      have hA2 : A2.A ≤ blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) :=
        plusPlaneB_subset _ _ _ _ _
      have hu0 : u ∈ (P ⟨0, by omega⟩).perp := (huperp ⟨0, by omega⟩).1
      have hv0 : v ∈ (P ⟨0, by omega⟩).perp := (huperp ⟨0, by omega⟩).2
      have hu1 : u ∈ (P ⟨1, by omega⟩).perp := (huperp ⟨1, by omega⟩).1
      have hv1 : v ∈ (P ⟨1, by omega⟩).perp := (huperp ⟨1, by omega⟩).2
      have htail0 : Submodule.span F {u, v} ≤
          perp Q (pairSpan (P ⟨0, by omega⟩)) :=
        pairSpan_le_perp_of_tail hu0 hv0
      have htail1 : Submodule.span F {u, v} ≤
          perp Q (pairSpan (P ⟨1, by omega⟩)) :=
        pairSpan_le_perp_of_tail hu1 hv1
      have htailblock : Submodule.span F {u, v} ≤
          perp Q (blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩)) := by
        intro x hx
        rw [mem_perp]
        intro y hy
        rw [blockSpan, Submodule.mem_sup] at hy
        obtain ⟨a, ha, b, hb, rfl⟩ := hy
        rw [polar_comm, polar_add_right, polar_comm Q x a, polar_comm Q x b,
          mem_perp.mp (htail0 hx) a ha, mem_perp.mp (htail1 hx) b hb, add_zero]
      have hblock_tail : blockSpan (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) ≤
          perp Q (Submodule.span F {u, v}) := by
        intro x hx
        rw [mem_perp]
        intro y hy
        rw [polar_comm]
        exact mem_perp.mp (htailblock hy) x hx
      have h13 : A1.A ≤ perp Q A3.A := hA1.trans (hblock_tail.trans (perp_anti (le_refl _)))
      have h23' : A2.A ≤ perp Q A3.A := hA2.trans (hblock_tail.trans (perp_anti (le_refl _)))
      have h31 : A3.A ≤ perp Q A1.A := by
        intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
        exact mem_perp.mp (h13 hy) x hx
      have h32 : A3.A ≤ perp Q A2.A := by
        intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
        exact mem_perp.mp (h23' hy) x hx
      let D : Fin 3 → PlaneFrame Q := fun i =>
        if i = 0 then A1 else if i = 1 then A2 else A3
      have horth : ∀ i j, i ≠ j → (D i).A ≤ perp Q (D j).A := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact absurd rfl hij
        · exact plusPlane_orthogonal (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc
        · exact h13
        · intro x hx; rw [mem_perp]; intro y hy; rw [polar_comm]
          exact mem_perp.mp
            (plusPlane_orthogonal (P ⟨0, by omega⟩) (P ⟨1, by omega⟩) h01 c hc hy) x hx
        · exact absurd rfl hij
        · exact h23'
        · exact h31
        · exact h32
        · exact absurd rfl hij
      obtain ⟨T, hTH, hTelem, hTrank⟩ :=
        exists_elemAbelian_of_planeFrames hq hq2 hqplus D horth
      refine ⟨T, hTH, hTelem, ?_⟩
      simpa [Nat.card_fin] using hTrank

end OmTorus

end CFSG.LocalAnalysis.GLTheoremA.Y10F
