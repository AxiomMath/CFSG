module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsLin

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem unitaryData_two {K : Type} [Field K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2) :
    UnitaryFieldData 2 m K :=
  UnitaryFieldData.mk Nat.prime_two hm (by rw [hK, ← pow_mul, mul_comm])

section Uni

variable {K : Type} [Field K] {m d : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = (2 ^ m) ^ 2)

include hm hK

theorem uni_aut_decomp (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ m = 2))
    (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))) :
    ∃ (A : uU (unitaryData_two hm hK) d) (φ : K ≃+* K),
      α = uConjAut (unitaryData_two hm hK) (by omega) A *
        uFieldAut (unitaryData_two hm hK) (by omega) φ :=
  exists_uConjAut_mul_uFieldAut (unitaryData_two hm hK) hd hq α

theorem mem_conjGU (hd : 3 ≤ d) (A : uU (unitaryData_two hm hK) d) :
    uConjAut (unitaryData_two hm hK) (by omega) A ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
        (LargeEvenGUSet (Fin d) K (2 ^ m)) := by
  refine ⟨(A : GL (Fin d) K), ⟨1, one_ne_zero, one_pow _, ?_⟩, fun x y hxy => ?_⟩
  · rw [one_smul]
    exact (mem_uU _).1 A.2
  · have hxy' : (y : GL (Fin d) K) = (A : GL (Fin d) K) * (x : GL (Fin d) K) *
        (A : GL (Fin d) K)⁻¹ := hxy
    exact (uConjAut_proj (unitaryData_two hm hK) (by omega) A x).trans
      (congrArg (projH (StatedSU d (2 ^ m) K)) (Subtype.ext hxy'.symm))

theorem mem_fieldGU (hd : 3 ≤ d) (σ : K ≃+* K) :
    uFieldAut (unitaryData_two hm hK) (by omega) σ ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))) := by
  refine ⟨σ, fun x y hxy => ?_⟩
  have hxy' : ((y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ := hxy
  refine (uFieldAut_proj (unitaryData_two hm hK) (by omega) σ x).trans
    (congrArg (projH (StatedSU d (2 ^ m) K)) ?_)
  apply Subtype.ext
  apply Units.ext
  exact (coe_glAut σ (x : GL (Fin d) K)).trans hxy'.symm

theorem uni_mem_mul_field (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ m = 2))
    (φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))) :
    ∃ i ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
        (LargeEvenGUSet (Fin d) K (2 ^ m)),
      ∃ f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m))),
        φ = i * f := by
  obtain ⟨A, σ, rfl⟩ := uni_aut_decomp hm hK hd hq φ
  exact ⟨_, mem_conjGU hm hK hd A, _, mem_fieldGU hm hK hd σ, rfl⟩

end Uni

theorem famUni_recipe {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) (hfam : FamUni lab) :
    ∃ (d m : ℕ), 3 ≤ d ∧ 1 ≤ m ∧ ¬(d = 3 ∧ 2 ^ m = 2) ∧
      ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q ↔ LargeEvenRecipeUnitary d (2 ^ m) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hT⟩ := hΛ
  dsimp only at hn
  rcases hfam with h | ⟨h, hr⟩
  · subst h
    dsimp only [LargeEvenInLambda2] at hT
    refine ⟨rank + 1, n, by omega, hn, ?_, fun Q => Iff.rfl⟩
    rintro ⟨h3, h2⟩
    have hn2 : 2 ≤ n := hT.2 (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at h4
    omega
  · subst h
    dsimp only at hr
    subst hr
    exact ⟨4, n, by norm_num, hn, by norm_num, fun Q => by simp [LargeEvenRawDatum]⟩

theorem ClsUni_holds : ClsUni := by
  intro S _ _ p α labK hfam hp hp2 _ hlab hα
  have hlab' : LargeEvenMarking S (fun lab _ _ _ _ _ => lab = labK) := hlab
  obtain ⟨hcomm, lab, hΛ, hraw⟩ := hlab'
  obtain ⟨_, _, _, _, hQ0⟩ := rawDatum_exists hraw
  obtain ⟨_, _, θ0, hlabEq⟩ := hQ0
  subst hlabEq
  obtain ⟨d, m, hd, hm, hq, hiff⟩ := famUni_recipe hΛ hfam
  obtain ⟨K, instF, instFin, hK, hQ⟩ := (hiff _).1 hraw
  obtain ⟨hsimple, hnonab, θ, -⟩ := hQ
  set φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m))) :=
    MulAut.congr θ (centerQuotAut S α) with hφdef
  have hind : LargeEvenInduces θ (fun s s' => s' = α s) φ := by
    intro l l' hll'
    subst hll'
    simp [hφdef, MulAut.congr_apply, centerQuotAut_mk]
  have hrec : ∀ Q : LargeEvenRawCont,
      Q (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ m)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
          (LargeEvenGUSet (Fin d) K (2 ^ m)))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))) →
      LargeEvenRecipeUnitary d (2 ^ m) Q := by
    intro Q hQK
    unfold LargeEvenRecipeUnitary
    exact ⟨K, instF, instFin, hK, hQK⟩
  by_cases hI : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
      (LargeEvenGUSet (Fin d) K (2 ^ m))
  · left
    unfold InnDiagKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _
      ⟨hsimple, hnonab, θ, rfl, φ, hI, hind⟩)⟩
  · right
    obtain ⟨i, hi, f, hf, hφif⟩ := uni_mem_mul_field hm hK hd hq φ
    have hnotI : ¬ ∃ i' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ m)))
        (LargeEvenGUSet (Fin d) K (2 ^ m)),
        LargeEvenInduces θ (fun s s' => s' = α s) i' := by
      rintro ⟨i', hi', hind'⟩
      apply hI
      rw [← induces_unique hind' hind]
      exact hi'
    have hindif : LargeEvenInduces θ (fun s s' => s' = α s) (i * f) := by
      rw [← hφif]
      exact hind
    unfold FieldKind CFSG.Assembly.LargeEvenMarking
    exact ⟨hcomm, lab, hΛ, (hiff _).2 (hrec _
      ⟨hsimple, hnonab, θ, rfl, ⟨i, hi, f, hf, hindif⟩, hnotI⟩)⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GField
