module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LieType.Universal.Unitary CFSG.Open.StatedAPI
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU heldGU mem_heldGU hct_heldSU_eq_statedSU)

theorem statedSU_eq_SUid {d n : ℕ} {K : Type} [Field K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) : StatedSU d (2 ^ n) K = SUid τ d := by
  rw [← hct_heldSU_eq_statedSU hτq (hτ := hτ)]
  ext x
  simp only [heldSU, Subgroup.mem_inf, mem_heldGU, mem_SUid, mem_statedSL_iff, conjTr, and_comm]

theorem conj_mem_statedSU {d n : ℕ} {K : Type} [Field K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) {A x : GL (Fin d) K} (hA : A ∈ heldGU d K τ hτ)
    (hx : x ∈ StatedSU d (2 ^ n) K) : A * x * A⁻¹ ∈ StatedSU d (2 ^ n) K := by
  rw [statedSU_eq_SUid hτ hτq] at hx ⊢
  exact conj_mem_SUid hτ (show IsIso τ A from mem_heldGU.1 hA) hx

theorem glMap_mem_statedSU {d n : ℕ} {K : Type} [Field K] {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x)
    (hτq : ∀ x, τ x = x ^ 2 ^ n) (σ : K ≃+* K) {x : GL (Fin d) K} (hx : x ∈ StatedSU d (2 ^ n) K) :
    glMap σ x ∈ StatedSU d (2 ^ n) K := by
  rw [statedSU_eq_SUid hτ hτq] at hx ⊢
  refine glMap_mem_SUid (σ := σ) (fun y => ?_) hx
  rw [hτq, hτq, map_pow]

theorem fld_fix_of_one_uni {d n : ℕ} {K : Type} [Field K]
    (f : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K)))
    (hf : LargeEvenGraphAut (LargeEvenProjMk (StatedSU d (2 ^ n) K))
      (fun h h' : ↥(StatedSU d (2 ^ n) K) =>
        ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map (⇑(1 : K ≃+* K))) f)
    (r : LargeEvenProj (StatedSU d (2 ^ n) K)) : f r = r := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective r
  have hrel : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map (⇑(1 : K ≃+* K)) := by
    ext i j
    simp
  exact hf x x hrel

theorem fieldKind_unitary_core {S : Type} [Group S] {α : MulAut S} {d n : ℕ}
    (hcen : Subgroup.center S = ⊥) {K : Type} [Field K] [Finite K] (hcard : Nat.card K = (2 ^ n) ^ 2)
    (θ : S ⧸ Subgroup.center S ≃* LargeEvenProj (StatedSU d (2 ^ n) K))
    (hB : ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (StatedSU d (2 ^ n) K)) (LargeEvenGUSet (Fin d) K (2 ^ n)),
      ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (StatedSU d (2 ^ n) K)),
        LargeEvenInduces θ (fun s s' => s' = α s) (i * f))
    (hC : ¬ ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (StatedSU d (2 ^ n) K)) (LargeEvenGUSet (Fin d) K (2 ^ n)),
      LargeEvenInduces θ (fun s s' => s' = α s) i) :
    ∃ (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x), (∀ x, τ x = x ^ 2 ^ n) ∧
      ∃ (A : GL (Fin d) K) (σ : K ≃+* K) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ n) K)))
        (e : S ≃* LargeEvenProj (StatedSU d (2 ^ n) K)),
        A ∈ heldGU d K τ hτ ∧ (∀ l : S, e (α l) = u (e l)) ∧
        (∀ h h' : ↥(StatedSU d (2 ^ n) K), (h' : GL (Fin d) K) = A * glMap σ (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU d (2 ^ n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ n) K) h') ∧
        σ ≠ 1 := by
  obtain ⟨τ, hτq, hτ⟩ := exists_frob_equiv hcard
  obtain ⟨i, ⟨A₀, hA₀, hAi⟩, f, ⟨σ, hfσ⟩, hind⟩ := hB
  obtain ⟨A, hA, hAconj⟩ := exists_heldGU_of_GUSet hτq hcard hτ A₀ hA₀
  have hσ : σ ≠ 1 := by
    intro hσ1
    subst hσ1
    apply hC
    refine ⟨i, ⟨A₀, hA₀, hAi⟩, fun l l' hll' => ?_⟩
    have h1 := hind l l' hll'
    rw [MulAut.mul_apply, fld_fix_of_one_uni f hfσ] at h1
    exact h1
  refine ⟨τ, hτ, hτq, A, σ, i * f, ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).symm.trans θ, hA, fun l => (hind l (α l) rfl).symm, ?_, hσ⟩
  intro h h' hh'
  have hmσ : glMap σ (h : GL (Fin d) K) ∈ StatedSU d (2 ^ n) K := glMap_mem_statedSU hτ hτq σ h.2
  have hmA : A * glMap σ (h : GL (Fin d) K) * A⁻¹ ∈ StatedSU d (2 ^ n) K :=
    conj_mem_statedSU hτ hτq hA hmσ
  have hf := hfσ h ⟨glMap σ (h : GL (Fin d) K), hmσ⟩ (coe_glMap σ (h : GL (Fin d) K))
  have hi := hAi ⟨glMap σ (h : GL (Fin d) K), hmσ⟩ ⟨A * glMap σ (h : GL (Fin d) K) * A⁻¹, hmA⟩
    (hAconj (glMap σ (h : GL (Fin d) K)))
  rw [MulAut.mul_apply, hf, hi]
  congr 1
  exact Subtype.ext hh'.symm

theorem fieldKind_unitary_data {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamUni labK) (hfld : FieldKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ 2 ^ labK.n) ∧ Nat.card K = (2 ^ labK.n) ^ 2 ∧ 3 ≤ d ∧ (d = 3 → 2 ≤ labK.n) ∧
      (canonLabel labK).tag = .twA ∧ (canonLabel labK).rank + 1 = d ∧ (canonLabel labK).n = labK.n ∧
      ∃ (A : GL (Fin d) K) (σ : K ≃+* K) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ labK.n) K)))
        (e : S ≃* LargeEvenProj (StatedSU d (2 ^ labK.n) K)),
        A ∈ heldGU d K τ hτ ∧ (∀ l : S, e (α l) = u (e l)) ∧
        (∀ h h' : ↥(StatedSU d (2 ^ labK.n) K), (h' : GL (Fin d) K) = A * glMap σ (h : GL (Fin d) K) * A⁻¹ →
          u (LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h) = LargeEvenProjMk (StatedSU d (2 ^ labK.n) K) h') ∧
        σ ≠ 1 := by
  unfold FieldKind CFSG.Assembly.LargeEvenMarking at hfld
  obtain ⟨-, lab', hlam, hraw⟩ := hfld
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ⟨ht, hr⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeUnitary at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, hB, hC⟩ := hQ'
    obtain ⟨τ, hτ, hτq, A, σ, u, e, hA, hαu, hgraph, hσ⟩ := fieldKind_unitary_core hcen hcard θ hB hC
    simp only [LargeEvenInLambda2, ht] at hlam
    refine ⟨K, hK, hKf, labK.rank + 1, τ, hτ, hτq, hcard, by omega, fun h3 => hlam.2.2 (by omega),
      by simp [canonLabel, ht], by simp [canonLabel, ht], by simp [canonLabel, ht],
      A, σ, u, e, hA, hαu, hgraph, hσ⟩
  ·
    unfold LargeEvenRawDatum at hraw
    simp only [ht, hr, if_true] at hraw
    unfold LargeEvenRecipeUnitary at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, hB, hC⟩ := hQ'
    obtain ⟨τ, hτ, hτq, A, σ, u, e, hA, hαu, hgraph, hσ⟩ :=
      fieldKind_unitary_core (d := 4) hcen hcard θ hB hC
    refine ⟨K, hK, hKf, 4, τ, hτ, hτq, hcard, by norm_num, fun h => absurd h (by norm_num),
      by simp [canonLabel, ht, hr], by simp [canonLabel, ht, hr], by simp [canonLabel, ht, hr],
      A, σ, u, e, hA, hαu, hgraph, hσ⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniMark

end
