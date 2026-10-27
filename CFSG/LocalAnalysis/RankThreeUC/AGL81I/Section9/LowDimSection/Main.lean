module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Core
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Inputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Solvable

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

theorem isLowDimSimpleSection_of_mulEquiv {q : ℕ} [Fact q.Prime] {S T : Type} [Group S]
    [Group T] (e : S ≃* T) (h : IsLowDimSimpleSection q T) : IsLowDimSimpleSection q S := by
  unfold IsLowDimSimpleSection at h ⊢
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨e.trans f⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨e.trans f⟩

private lemma lowDim_core (hout : LowDimOutSolvable) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    (hlow : ∀ d < Fintype.card ι, SimpleSectionsIn (IsLowDimSimpleSection q) (GL (Fin d) (ZMod q)))
    (X : Subgroup (GL ι (ZMod q)))
    (hq : ∀ Y : Subgroup (GL ι (ZMod q)), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      IsLowDimSimpleSection q (↥Y ⧸ Subgroup.center ↥Y)) :
    SimpleSectionsIn (IsLowDimSimpleSection q) X :=
  simpleSectionsIn_of_core (fun e h => isLowDimSimpleSection_of_mulEquiv e h)
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨MulEquiv.refl _⟩)
    (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨MulEquiv.refl _⟩)
    (fun T _ _ _ hT hP => hout q hq2 T hT hP) hι hlow X hq

private lemma gl_mul_comm_of_le_one {K : Type} [Field K] {d : ℕ} (hd : d ≤ 1)
    (a b : GL (Fin d) K) : a * b = b * a := by
  ext i j
  have hi : ∀ k : Fin d, k = i := fun k => Fin.ext (by omega)
  simp only [Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun k _ hk => absurd (hi k) hk) (by simp),
    Finset.sum_eq_single i (fun k _ hk => absurd (hi k) hk) (by simp), hi j, mul_comm]

theorem simpleSectionsIn_gl_of (h2 : GLTwoLowDimSections) (h3 : GLThreeQuasisimpleLowDim)
    (hout : LowDimOutSolvable) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {d : ℕ} (hd : d ≤ 3) :
    SimpleSectionsIn (IsLowDimSimpleSection q) (GL (Fin d) (ZMod q)) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases (by omega : d ≤ 1 ∨ d = 2 ∨ d = 3) with h1 | rfl | rfl
    · have : IsMulCommutative (GL (Fin d) (ZMod q)) :=
        ⟨⟨fun a b => gl_mul_comm_of_le_one h1 a b⟩⟩
      exact SimpleSectionsIn.of_isMulCommutative
    · exact h2 q hq2
    · refine SimpleSectionsIn.of_injective
        (Subgroup.topEquiv (G := GL (Fin 3) (ZMod q))).symm.toMonoidHom
        (Subgroup.topEquiv (G := GL (Fin 3) (ZMod q))).symm.injective ?_
      refine lowDim_core hout hq2 (ι := Fin 3) (by simp) ?_ ⊤ ?_
      · intro d' hd'
        rw [Fintype.card_fin] at hd'
        exact ih d' hd' (by omega)
      · intro Y _ hYq hYi
        exact h3 q hq2 Y hYq hYi

theorem simpleSectionsIn_gsp_of (h2 : GLTwoLowDimSections) (h3 : GLThreeQuasisimpleLowDim)
    (h4 : SpFourQuasisimpleLowDim) (hout : LowDimOutSolvable) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (X : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q)))
    (hX : ∀ x ∈ X, ∃ μ : ZMod q, (x : Matrix _ _ (ZMod q))ᵀ * spFourJ (ZMod q) *
      (x : Matrix _ _ (ZMod q)) = μ • spFourJ (ZMod q)) :
    SimpleSectionsIn (IsLowDimSimpleSection q) X := by
  refine lowDim_core hout hq2 (by simp) ?_ X ?_
  · intro d hd
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    exact simpleSectionsIn_gl_of h2 h3 hout hq2 (by omega)
  · intro Y hYX hYq _
    exact h4 q hq2 Y (le_statedSp_of_isPerfect hX hYX hYq.1) hYq

theorem lowDimMulAutSection_of (h2 : GLTwoLowDimSections) (h3 : GLThreeQuasisimpleLowDim)
    (h4 : SpFourQuasisimpleLowDim) (hout : LowDimOutSolvable) : LowDimMulAutSection := by
  intro q _ hq2 V _ _ hV hrk A S _ _ hS φ hφ
  have hsec : SimpleSectionsIn (IsLowDimSimpleSection q) A := by
    rcases exists_linear_of_pRank_le_three hq2 hV hrk A with ⟨d, hd, f, hf⟩ | ⟨f, hf, hJ⟩
    · have := hf.isNilpotent
      exact SimpleSectionsIn.of_isSolvable_ker f inferInstance
        (simpleSectionsIn_gl_of h2 h3 hout hq2 hd)
    · have := hf.isNilpotent
      refine SimpleSectionsIn.of_isSolvable_ker f.rangeRestrict
        (by rw [MonoidHom.ker_rangeRestrict]; infer_instance)
        (simpleSectionsIn_gsp_of h2 h3 h4 hout hq2 f.range ?_)
      rintro _ ⟨b, rfl⟩
      exact hJ b
  exact hsec ⊤ S hS (φ.comp (Subgroup.topEquiv (G := A)).toMonoidHom)
    (hφ.comp (Subgroup.topEquiv (G := A)).surjective)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
