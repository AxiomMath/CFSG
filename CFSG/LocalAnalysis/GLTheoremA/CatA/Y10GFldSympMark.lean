module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {m : ℕ} {K : Type} [Field K]

theorem mem_gsp_of_mem_largeEvenGSpSet {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ LargeEvenGSpSet K m) : A ∈ gsp m K := by
  obtain ⟨μ, hμ, h⟩ := hA
  refine mem_gsp.mpr ⟨Units.mk0 μ hμ, ?_⟩
  simpa [largeEvenSpForm_def, formJ] using h

theorem exists_conjAut_eq_of_mem_matConjImage {i : MulAut (StatedProj (StatedSp m K))}
    (hi : i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m)) :
    ∃ A : gsp m K, conjAut m K A = i := by
  obtain ⟨A, hA, hgraph⟩ := hi
  refine ⟨⟨A, mem_gsp_of_mem_largeEvenGSpSet hA⟩, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : (↑y : StatedProj (StatedSp m K)) = proj m K y := rfl
  rw [hy, conjAut_proj]
  exact (hgraph y (conjSp m K ⟨A, mem_gsp_of_mem_largeEvenGSpSet hA⟩ y)
    (coe_conjSp _ y)).symm

theorem conjAut_mem_matConjImage (A : gsp m K) :
    conjAut m K A ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  refine ⟨(A : GL (Fin m ⊕ Fin m) K), ⟨(μ : K), μ.ne_zero, ?_⟩, ?_⟩
  · simpa [largeEvenSpForm_def, formJ] using hμ
  · intro h h' hh'
    have hproj : LargeEvenProjMk (LargeEvenSpGroup K m) h = proj m K h := rfl
    have hproj' : LargeEvenProjMk (LargeEvenSpGroup K m) h' = proj m K h' := rfl
    rw [hproj, hproj', conjAut_proj]
    have hcoe : ((conjSp m K A h : StatedSp m K) : GL (Fin m ⊕ Fin m) K) =
        (h' : GL (Fin m ⊕ Fin m) K) := by
      rw [coe_conjSp]
      exact hh'.symm
    exact congrArg (proj m K) (Subtype.ext hcoe)

theorem exists_fieldAut_eq_of_mem_matFieldImage {f : MulAut (StatedProj (StatedSp m K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) :
    ∃ σ : K ≃+* K, fieldAut m K σ = f := by
  obtain ⟨σ, hgraph⟩ := hf
  refine ⟨σ, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : (↑y : StatedProj (StatedSp m K)) = proj m K y := rfl
  rw [hy, fieldAut_proj]
  exact (hgraph y (fieldSp m K σ y) (coe_fieldSp σ y)).symm

theorem ringEquiv_eq_one_of_card_eq_two [Finite K] (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = 1 := by
  classical
  letI := Fintype.ofFinite K
  have hcard : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton, Fintype.card_eq_nat_card, hK]
    simp
  have huniv : ({0, 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hmem : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    have hx : x ∈ ({0, 1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
    simpa using hx
  ext x
  rcases hmem x with rfl | rfl <;> simp

theorem fieldKind_symp_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamSymp labK) (hfld : FieldKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (m : ℕ), 2 ≤ m ∧ 1 ≤ (canonLabel labK).n ∧
      Nat.card K = 2 ^ (canonLabel labK).n ∧ (canonLabel labK).tag = .B ∧
      (canonLabel labK).rank = m ∧
      ∃ (e : S ≃* StatedProj (StatedSp m K)) (u : MulAut (StatedProj (StatedSp m K))),
        (∀ l : S, e (α l) = u (e l)) ∧ u ∈ spSemilinearAutGroup m K ∧
          u ∉ spLinearAutGroup m K := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam, hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ht | ht
  pick_goal 3
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, ⟨i, hi, f, hf, hind⟩, hnot⟩ := hQ'
    obtain ⟨σ, hfσ⟩ := hf
    have hσ1 : σ = 1 := ringEquiv_eq_one_of_card_eq_two hcard σ
    let H : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
      ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆
    have hfix : ∀ r : LargeEvenProj H, f r = r := by
      intro r
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
      have hx : (↑x : LargeEvenProj H) = LargeEvenProjMk H x := rfl
      rw [hx]
      apply hfσ x x
      rw [hσ1]
      simp
    have hf1 : f = 1 := by
      ext r
      rw [hfix r]
      rfl
    have hind' : LargeEvenInduces θ (fun l l' => l' = α l) i := by
      simpa [hf1] using hind
    exact absurd ⟨i, hi, hind'⟩ hnot
  all_goals
    have hn : 1 ≤ labK.n := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.1
    have hm : 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, ⟨i, hi, f, hf, hind⟩, hnot⟩ := hQ'
    obtain ⟨A, hA⟩ := exists_conjAut_eq_of_mem_matConjImage hi
    obtain ⟨σ, hσ⟩ := exists_fieldAut_eq_of_mem_matFieldImage hf
    let u : MulAut (StatedProj (StatedSp labK.rank K)) := i * f
    let e : S ≃* StatedProj (StatedSp labK.rank K) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans
        QuotientGroup.quotientBot).symm.trans θ
    have hαu : ∀ l : S, e (α l) = u (e l) := fun l => (hind l (α l) rfl).symm
    have huf : u = conjAut labK.rank K A * fieldAut labK.rank K σ := by
      simp [u, ← hA, ← hσ]
    have hopen : u ∈ spSemilinearAutGroup labK.rank K := by
      rw [huf]
      exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup
        (conjAut_mem_spLinearAutGroup A)) (fieldAut_mem_spSemilinearAutGroup σ)
    have hclosed : u ∉ spLinearAutGroup labK.rank K := by
      intro hu
      obtain ⟨B, hB⟩ := mem_spLinearAutGroup_iff.mp hu
      apply hnot
      refine ⟨conjAut labK.rank K B, conjAut_mem_matConjImage B, ?_⟩
      have hBu : conjAut labK.rank K B = i * f := by simpa [u] using hB
      simpa [← hBu] using hind
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    refine ⟨K, hK, hKf, labK.rank, hm, ?_, ?_, by simp [canonLabel, ht],
      by simp [canonLabel, ht], e, u, hαu, hopen, hclosed⟩
    · rw [hc]; exact hn
    · rw [hc]; exact hcard

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark

end
