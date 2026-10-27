module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldLinTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinMark

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinTw (scalar_eq_smul_one)

variable {K : Type} [Field K]

theorem fld_apply_mk {d : ℕ} (A : GL (Fin d) K) (σ : K ≃+* K)
    (i f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hA : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
      (fun h h' : ↥(LargeEvenSLGroup (Fin d) K) => (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹) i)
    (hfσ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
      (fun h h' : ↥(LargeEvenSLGroup (Fin d) K) =>
        ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ) f)
    (x : ↥(slGL (Fin d) K)) :
    (i * f) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x) := by
  have hm1 : glMap σ (x : GL (Fin d) K) ∈ slGL (Fin d) K := by
    rw [mem_slGL, det_glMap, (mem_slGL.1 x.2), map_one]
  have hm2 : A * glMap σ (x : GL (Fin d) K) * A⁻¹ ∈ slGL (Fin d) K := conj_mem_slGL A hm1
  have hf := hfσ x ⟨glMap σ (x : GL (Fin d) K), hm1⟩ rfl
  have hi := hA ⟨glMap σ (x : GL (Fin d) K), hm1⟩ ⟨A * glMap σ (x : GL (Fin d) K) * A⁻¹, hm2⟩ rfl
  rw [MulAut.mul_apply, hf, hi]
  rfl

theorem fld_fix_of_one {d : ℕ} (f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))
      (fun h h' : ↥(LargeEvenSLGroup (Fin d) K) =>
        ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map (⇑(1 : K ≃+* K))) f)
    (r : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) : f r = r := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
  have hrel : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map (⇑(1 : K ≃+* K)) := by
    ext i j
    simp
  exact hf x x hrel

theorem fieldKind_data_of_recipe {S : Type} [Group S] {α : MulAut S} {d : ℕ} {K : Type} [Field K]
    (hcen : Subgroup.center S = ⊥)
    (hQ : ∃ θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K),
      (∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
        ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)),
          LargeEvenInduces θ (fun s s' => s' = α s) (i * f)) ∧
      ¬ ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
          LargeEvenInduces θ (fun s s' => s' = α s) i) :
    ∃ (A : GL (Fin d) K) (σ : K ≃+* K) (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
      (e : S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      (∀ l : S, e (α l) = u (e l)) ∧
      (∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) ∧ σ ≠ 1 := by
  obtain ⟨θ, ⟨⟨i, hi, f, hf, hind⟩, hnot⟩⟩ := hQ
  obtain ⟨A, -, hA⟩ := hi
  obtain ⟨σ, hfσ⟩ := hf
  have hσ : σ ≠ 1 := by
    intro hσ1
    subst hσ1
    apply hnot
    refine ⟨i, ⟨A, Set.mem_univ _, hA⟩, fun l l' hll' => ?_⟩
    have h1 := hind l l' hll'
    rw [MulAut.mul_apply, fld_fix_of_one f hfσ] at h1
    exact h1
  refine ⟨A, σ, i * f, ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans θ,
    fun l => (hind l (α l) rfl).symm, fun x => fld_apply_mk A σ i f hA hfσ x, hσ⟩

theorem fieldKind_linear_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hfld : FieldKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ), 2 ≤ d ∧ Nat.card K = 2 ^ (canonLabel labK).n ∧
      (canonLabel labK).tag = .A ∧ (canonLabel labK).rank + 1 = d ∧
      ∃ (A : GL (Fin d) K) (σ : K ≃+* K) (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
        (e : S ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
        (∀ l : S, e (α l) = u (e l)) ∧
        (∀ x : ↥(slGL (Fin d) K), u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
          LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x)) ∧ σ ≠ 1 := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam, hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ⟨ht, hr⟩ | ⟨ht, hr⟩
  ·
    have hrank : 1 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, hB, hC⟩ := hQ'
    obtain ⟨A, σ, u, e, hαu, hgraph, hσ⟩ := fieldKind_data_of_recipe hcen ⟨θ, hB, hC⟩
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    exact ⟨K, hK, hKf, labK.rank + 1, by omega, by rw [hc]; exact hcard,
      by simp [canonLabel, ht], by simp [canonLabel, ht], A, σ, u, e, hαu, hgraph, hσ⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, hB, hC⟩ := hQ'
    obtain ⟨A, σ, u, e, hαu, hgraph, hσ⟩ := fieldKind_data_of_recipe hcen ⟨θ, hB, hC⟩
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht, hr]
    exact ⟨K, hK, hKf, 4, by norm_num, by rw [hc]; exact hcard,
      by simp [canonLabel, ht, hr], by simp [canonLabel, ht, hr], A, σ, u, e, hαu, hgraph, hσ⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeLinear at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, hB, hC⟩ := hQ'
    obtain ⟨A, σ, u, e, hαu, hgraph, hσ⟩ := fieldKind_data_of_recipe hcen ⟨θ, hB, hC⟩
    have hc : (canonLabel labK).n = 2 * labK.n := by simp [canonLabel, ht, hr]
    refine ⟨K, hK, hKf, 2, le_refl _, ?_, by simp [canonLabel, ht, hr], by simp [canonLabel, ht, hr],
      A, σ, u, e, hαu, hgraph, hσ⟩
    rw [hc, hcard, ← pow_mul, mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldLinMark

end
