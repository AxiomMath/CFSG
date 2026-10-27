module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PartStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisLinearRuns

public section

namespace CFSG.AGLEmbeddingD2.HeisLinear

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareLinear

variable {m : ℕ} {F : Type} [Field F]

theorem blockMat_apply_of_not_pair (i : Fin m) (A : Matrix (Fin 2) (Fin 2) F) {a b : Fin (m + 1)}
    (h : ¬ ((a = i.castSucc ∨ a = i.succ) ∧ (b = i.castSucc ∨ b = i.succ))) :
    SL.blockMat i A a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b := by
  obtain ⟨p, rfl⟩ := (SL.blockEquiv i).surjective a
  obtain ⟨q, rfl⟩ := (SL.blockEquiv i).surjective b
  rw [SL.blockMat_apply]
  rcases p with p | ⟨a, ha⟩ <;> rcases q with q | ⟨b, hb⟩
  · exfalso
    apply h
    fin_cases p <;> fin_cases q <;> simp [SL.blockEquiv_zero, SL.blockEquiv_one]
  · push Not at hb
    fin_cases p <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, Ne.symm hb.1, Ne.symm hb.2]
  · push Not at ha
    fin_cases q <;>
      simp [SL.blockEquiv_zero, SL.blockEquiv_one, SL.blockEquiv_inr, ha.1, ha.2]
  · rw [Matrix.fromBlocks_apply₂₂, SL.blockEquiv_inr, SL.blockEquiv_inr]
    simp [Matrix.one_apply]

variable [Finite F]

theorem isMulCommutative_of_le_torus_sup_leviM {f : ℕ} (hF : Nat.card F = 2 ^ f)
    {I : Set (Fin m)} {n : ℕ} (hn : ¬ ∃ a, RunIn I a n)
    (hfm : (Odd f ∧ n < 20) ∨ (f % 4 = 2 ∧ n < 10) ∨ (4 ∣ f ∧ n < 5))
    {Q : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)}
    (hQ : Q ≤ (⨆ k, torus m F k) ⊔ leviM (rootDatum m F) I) (hQp : IsPGroup 5 Q) :
    IsMulCommutative Q := by
  classical
  let s : Fin (m + 1) → ℕ := blockIndex I
  have hle : (⨆ k, torus m F k) ⊔ leviM (rootDatum m F) I ≤
      (PartStab.partStab F s).comap Matrix.SpecialLinearGroup.toGL := by
    refine sup_le (iSup_le fun k => ?_) (iSup₂_le fun i hi => ?_)
    · rw [torus, Subgroup.closure_le]
      rintro g ⟨t, ht⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, PartStab.mem_partStab]
      intro a b hab
      have hne : a ≠ b := fun h => hab (h ▸ rfl)
      change (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b = 0
      rw [ht]
      exact Matrix.diagonal_apply_ne _ hne
    · rw [rankOne_eq_range_blockHom (m := m) (F := F) i]
      rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_comap, PartStab.mem_partStab]
      intro a b hab
      change SL.blockMat i (A : Matrix (Fin 2) (Fin 2) F) a b = 0
      by_cases hp : (a = i.castSucc ∨ a = i.succ) ∧ (b = i.castSucc ∨ b = i.succ)
      · exfalso
        apply hab
        have h1 : s i.succ = s i.castSucc := blockIndex_succ_of_mem hi
        rcases hp with ⟨ha | ha, hb | hb⟩ <;> subst ha <;> subst hb <;> simp [h1]
      · rw [blockMat_apply_of_not_pair i _ hp]
        exact Matrix.one_apply_ne (fun h => hab (h ▸ rfl))
  have hQ' : Q.map Matrix.SpecialLinearGroup.toGL ≤ PartStab.partStab F s := by
    rintro _ ⟨g, hg, rfl⟩
    exact hle (hQ hg)
  have hcard : ∀ c : ℕ, Fintype.card {b : Fin (m + 1) // s b = c} ≤ n := card_blockIndex_le hn
  have hcomm : IsMulCommutative (Q.map Matrix.SpecialLinearGroup.toGL) := by
    refine PartStab.isMulCommutative_of_le_partStab s (fun c P hP => ?_) hQ' (hQp.map _)
    refine PartStab.isMulCommutative_of_isPGroup_five_GL_fintype hF ?_ P hP
    rcases hfm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, lt_of_le_of_lt (hcard c) h2⟩
    · exact Or.inr (Or.inl ⟨h1, lt_of_le_of_lt (hcard c) h2⟩)
    · exact Or.inr (Or.inr ⟨h1, lt_of_le_of_lt (hcard c) h2⟩)
  refine IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    Matrix.SpecialLinearGroup.toGL_injective ?_
  rw [map_mul, map_mul]
  exact setLike_mul_comm (Subgroup.mem_map_of_mem _ ha) (Subgroup.mem_map_of_mem _ hb)

end CFSG.AGLEmbeddingD2.HeisLinear
