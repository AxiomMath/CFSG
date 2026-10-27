module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldLang
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.BalanceLp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Assembly
open CFSG.LieType.SemisimpleCentralizers.HeldLang (glMap)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU mem_heldGU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp
  (statedProjEquivPrimeFormP statedProjEquivPrimeFormP_mk statedSU_eq_gramSU)

variable {f : ℕ} {K : Type} [Field K]

theorem mem_primeFormUnitary_of_heldGU (h : UnitaryFieldData 2 f K) {d : ℕ} {τ : K ≃+* K}
    {hτ : ∀ x, τ (τ x) = x} (hτq : ∀ x, τ x = x ^ 2 ^ f) {A : GL (Fin d) K}
    (hA : A ∈ heldGU d K τ hτ) : A ∈ primeFormUnitary h (idGram K d) := by
  rw [mem_primeFormUnitary]
  have hmap : (A : Matrix (Fin d) (Fin d) K).map h.bar = (A : Matrix (Fin d) (Fin d) K).map τ :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, Matrix.map_apply, h.bar_apply, hτq]
  simp only [idGram, Units.val_one, Matrix.mul_one, hmap]
  exact mem_heldGU.1 hA

theorem congr_statedProj_twist (h : UnitaryFieldData 2 f K) {d : ℕ} (hd : 1 ≤ d)
    (A : primeFormUnitary h (idGram K d)) (σ : K ≃+* K)
    {u : MulAut (LargeEvenProj (StatedSU d (2 ^ f) K))}
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ f) K),
      (g' : GL (Fin d) K) = (A : GL (Fin d) K) * glMap σ (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ f) K) g) = LargeEvenProjMk (StatedSU d (2 ^ f) K) g') :
    MulAut.congr (statedProjEquivPrimeFormP h hd) u =
      primeFormConjHom h (idGram K d) A *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := d)) σ := by
  ext y
  obtain ⟨z, rfl⟩ := (statedProjEquivPrimeFormP h hd).surjective y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  have hg : (g : GL (Fin d) K) ∈ gramSU h (idGram K d) :=
    (SetLike.ext_iff.1 (statedSU_eq_gramSU h d) _).1 g.2
  have hmσ : glAut σ (g : GL (Fin d) K) ∈ gramSU h (idGram K d) :=
    glAut_mem_gramSU h (isPrimeFormGram_idGram (K := K) (n := d)) σ hg
  have hAG : glAut σ (g : GL (Fin d) K) = glMap σ (g : GL (Fin d) K) :=
    Units.ext (by
      rw [coe_glAut, CFSG.LieType.SemisimpleCentralizers.HeldLang.coe_glMap])
  have hmA : (A : GL (Fin d) K) * glAut σ (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ ∈
      StatedSU d (2 ^ f) K :=
    (SetLike.ext_iff.1 (statedSU_eq_gramSU h d) _).2 (conj_mem_gramSU h _ A.2 hmσ)
  have h1 : u (g : StatedProj (StatedSU d (2 ^ f) K)) =
      ((⟨_, hmA⟩ : ↥(StatedSU d (2 ^ f) K)) : StatedProj (StatedSU d (2 ^ f) K)) :=
    hu g ⟨_, hmA⟩ (by
      show (A : GL (Fin d) K) * glAut σ (g : GL (Fin d) K) * (A : GL (Fin d) K)⁻¹ = _
      rw [hAG])
  have hfσ : primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := d)) σ
      ((⟨g, hg⟩ : gramSU h (idGram K d)) : primeFormP h (idGram K d)) =
      ((primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := d)) σ ⟨g, hg⟩ :
        gramSU h (idGram K d)) : primeFormP h (idGram K d)) :=
    primeFormFieldAut_mk h (isPrimeFormGram_idGram (K := K) (n := d)) σ _
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, h1,
    statedProjEquivPrimeFormP_mk, statedProjEquivPrimeFormP_mk, MulAut.mul_apply, hfσ,
    primeFormConjHom_mk]
  rfl

theorem conjHom_mul_fieldHom_not_mem [Finite K] (h : UnitaryFieldData 2 f K) {d : ℕ} (hd : 3 ≤ d)
    (hq : ¬(d = 3 ∧ 2 ^ f = 2)) (A : primeFormUnitary h (idGram K d)) {σ : K ≃+* K}
    (hσ : σ ≠ 1) :
    primeFormConjHom h (idGram K d) A *
        primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := d)) σ ∉
      primeFormD h (idGram K d) := by
  intro hmem
  rw [← ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := d)) hd hq,
    MonoidHom.mem_ker, primeFormFieldFactor_apply] at hmem
  exact hσ hmem

theorem congr_not_mem_primeFormD [Finite K] {S : Type} [Group S] (h : UnitaryFieldData 2 f K)
    {d : ℕ} (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ f = 2)) {τ : K ≃+* K} {hτ : ∀ x, τ (τ x) = x}
    (hτq : ∀ x, τ x = x ^ 2 ^ f) {α : MulAut S} {A : GL (Fin d) K} (hA : A ∈ heldGU d K τ hτ)
    {σ : K ≃+* K} (hσ : σ ≠ 1) {u : MulAut (LargeEvenProj (StatedSU d (2 ^ f) K))}
    (e : S ≃* LargeEvenProj (StatedSU d (2 ^ f) K)) (heu : ∀ l, e (α l) = u (e l))
    (hu : ∀ g g' : ↥(StatedSU d (2 ^ f) K),
      (g' : GL (Fin d) K) = A * glMap σ (g : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d (2 ^ f) K) g) = LargeEvenProjMk (StatedSU d (2 ^ f) K) g') :
    MulAut.congr (e.trans (statedProjEquivPrimeFormP h (by omega : 1 ≤ d))) α ∉
      primeFormD h (idGram K d) := by
  have h1 : MulAut.congr e α = u := by
    ext y
    obtain ⟨l, rfl⟩ := e.surjective y
    show e (α (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply, heu]
  have h2 : MulAut.congr (e.trans (statedProjEquivPrimeFormP h (by omega : 1 ≤ d))) α =
      MulAut.congr (statedProjEquivPrimeFormP h (by omega : 1 ≤ d)) (MulAut.congr e α) := by
    ext y
    rfl
  rw [h2, h1, congr_statedProj_twist h (by omega) ⟨A, mem_primeFormUnitary_of_heldGU h hτq hA⟩ σ hu]
  exact conjHom_mul_fieldHom_not_mem h hd hq _ hσ

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
