module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup

variable {n : ℕ} {F : Type*} [Field F]

private theorem blockSpecialLinear_inf_centralizer_eq_sdiff_of_diag
    (I J : Finset (Fin n)) (hJ : 2 ≤ J.card)
    (hDiag : ∀ g : SpecialLinearGroup (Fin n) F,
      g ∈ blockSpecialLinear (K := F) I ⊓
        centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) →
      TPattern J (g : Matrix (Fin n) (Fin n) F) →
      ∀ i ∈ J, (g : Matrix (Fin n) (Fin n) F) i i = 1) :
    blockSpecialLinear (K := F) I ⊓
        centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) =
      blockSpecialLinear (K := F) (I \ J) := by
  classical
  apply le_antisymm
  · intro g hg
    obtain ⟨hgI, hgC⟩ := hg
    have hpat : TPattern J (g : Matrix (Fin n) (Fin n) F) :=
      pattern_of_commute_transvections hJ fun i hi j hj hij =>
        (mem_centralizer_iff.mp hgC (SpecialLinearGroup.transvection hij 1)
          (transvection_mem_blockSpecialLinear hij hi hj (1 : F))).symm
    have hdiag : ∀ i ∈ J, (g : Matrix (Fin n) (Fin n) F) i i = 1 :=
      hDiag g ⟨hgI, hgC⟩ hpat
    have hfix : ∀ i j, i ∈ J ∨ j ∈ J →
        (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
      intro i j hijJ
      rcases hijJ with hi | hj
      · by_cases hji : j = i
        · subst j
          simpa only [Matrix.one_apply_eq] using hdiag i hi
        · rw [(hpat.1 i hi j hji).2, Matrix.one_apply_ne (Ne.symm hji)]
      · by_cases hij : i = j
        · subst i
          simpa only [Matrix.one_apply_eq] using hdiag j hj
        · rw [(hpat.1 j hj i hij).1, Matrix.one_apply_ne hij]
    apply mem_blockSpecialLinear.mpr
    intro i j hij
    rcases hij with hi | hj
    · by_cases hiI : i ∈ I
      · have hiJ : i ∈ J := by
          by_contra hiJ
          exact hi (Finset.mem_sdiff.mpr ⟨hiI, hiJ⟩)
        exact hfix i j (Or.inl hiJ)
      · exact hgI i j (Or.inl hiI)
    · by_cases hjI : j ∈ I
      · have hjJ : j ∈ J := by
          by_contra hjJ
          exact hj (Finset.mem_sdiff.mpr ⟨hjI, hjJ⟩)
        exact hfix i j (Or.inr hjJ)
      · exact hgI i j (Or.inr hjI)
  · intro g hg
    refine ⟨blockSpecialLinear_mono Finset.sdiff_subset hg, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    have hdis : Disjoint (I \ J) J :=
      Finset.disjoint_left.mpr fun i hi hj => (Finset.mem_sdiff.mp hi).2 hj
    exact (commute_blockSpecialLinear_of_disjoint hdis hg hb).eq.symm

theorem blockSpecialLinear_inf_centralizer_eq_sdiff (I J : Finset (Fin n))
    (hJ : 2 ≤ J.card) (hJI : ∃ d ∈ J, d ∉ I) :
    blockSpecialLinear (K := F) I ⊓
        centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) =
      blockSpecialLinear (K := F) (I \ J) := by
  obtain ⟨d, hdJ, hdI⟩ := hJI
  refine blockSpecialLinear_inf_centralizer_eq_sdiff_of_diag I J hJ ?_
  intro g hg hpat i hi
  have hd : (g : Matrix (Fin n) (Fin n) F) d d = 1 := by
    simpa only [Matrix.one_apply_eq] using hg.1 d d (Or.inl hdI)
  exact (hpat.2 i hi d hdJ).trans hd

theorem blockSpecialLinear_inf_centralizer_eq_sdiff_of_card_two [Finite F]
    (hF : Nat.card F = 2) (I J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    blockSpecialLinear (K := F) I ⊓
        centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) =
      blockSpecialLinear (K := F) (I \ J) := by
  classical
  let _ := Fintype.ofFinite F
  have hall : ({0, 1} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hF]
    simp
  have hscalar (a : F) (ha : a ≠ 0) : a = 1 := by
    have hmem : a ∈ ({0, 1} : Finset F) := hall.symm ▸ Finset.mem_univ a
    simpa [ha] using hmem
  refine blockSpecialLinear_inf_centralizer_eq_sdiff_of_diag I J hJ ?_
  intro g hg hpat i hi
  have hinv : (g : Matrix (Fin n) (Fin n) F) i i *
      ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
    rw [← mul_apply_self_of_pattern hpat hi, ← coe_mul_specialLinear, mul_inv_cancel,
      coe_one_specialLinear, Matrix.one_apply_eq]
  exact hscalar _ (left_ne_zero_of_mul_eq_one hinv)

private theorem blockSpecialLinear_map_inf_centralizer_eq_sdiff_of_native
    {G : Type*} [Group G] (κ : SpecialLinearGroup (Fin n) F →* G) (hκ : Function.Injective κ)
    (I J : Finset (Fin n))
    (hnative : blockSpecialLinear (K := F) I ⊓
      centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) =
        blockSpecialLinear (K := F) (I \ J)) :
    (blockSpecialLinear (K := F) I).map κ ⊓
        centralizer ((blockSpecialLinear (K := F) J).map κ : Set G) =
      (blockSpecialLinear (K := F) (I \ J)).map κ := by
  apply le_antisymm
  · rintro x ⟨⟨g, hgI, rfl⟩, hgC⟩
    refine ⟨g, ?_, rfl⟩
    rw [← hnative]
    refine ⟨hgI, mem_centralizer_iff.mpr ?_⟩
    intro b hb
    apply hκ
    simpa only [map_mul] using mem_centralizer_iff.mp hgC (κ b) ⟨b, hb, rfl⟩
  · rintro x ⟨g, hg, rfl⟩
    have hg' : g ∈ blockSpecialLinear (K := F) I ⊓
        centralizer (blockSpecialLinear (K := F) J : Set (SpecialLinearGroup (Fin n) F)) := by
      rw [hnative]
      exact hg
    refine ⟨⟨g, hg'.1, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro x ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hg'.2 b hb]

theorem blockSpecialLinear_map_inf_centralizer_eq_sdiff {G : Type*} [Group G]
    (κ : SpecialLinearGroup (Fin n) F →* G) (hκ : Function.Injective κ)
    (I J : Finset (Fin n)) (hJ : 2 ≤ J.card) (hJI : ∃ d ∈ J, d ∉ I) :
    (blockSpecialLinear (K := F) I).map κ ⊓
        centralizer ((blockSpecialLinear (K := F) J).map κ : Set G) =
      (blockSpecialLinear (K := F) (I \ J)).map κ :=
  blockSpecialLinear_map_inf_centralizer_eq_sdiff_of_native κ hκ I J
    (blockSpecialLinear_inf_centralizer_eq_sdiff I J hJ hJI)

theorem blockSpecialLinear_map_inf_centralizer_eq_sdiff_of_card_two [Finite F]
    (hF : Nat.card F = 2) {G : Type*} [Group G]
    (κ : SpecialLinearGroup (Fin n) F →* G) (hκ : Function.Injective κ)
    (I J : Finset (Fin n)) (hJ : 2 ≤ J.card) :
    (blockSpecialLinear (K := F) I).map κ ⊓
        centralizer ((blockSpecialLinear (K := F) J).map κ : Set G) =
      (blockSpecialLinear (K := F) (I \ J)).map κ :=
  blockSpecialLinear_map_inf_centralizer_eq_sdiff_of_native κ hκ I J
    (blockSpecialLinear_inf_centralizer_eq_sdiff_of_card_two hF I J hJ)

end CFSG.SeitzReduction.LinearPilot

end
