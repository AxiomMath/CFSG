module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def psuToPrimeForm (h : UnitaryFieldData p f K) :
    unitaryPSU h 3 ≃* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

theorem mem_primeFormUnitary_of_mem_unitaryIsom3 (h : UnitaryFieldData p f K) {A : GL (Fin 3) K}
    (hA : A ∈ unitaryIsom3 h) : A ∈ primeFormUnitary h (idGram K 3) := by
  change ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (idGram K 3) *
    (A : Matrix (Fin 3) (Fin 3) K) = idGram K 3
  rw [show idGram K 3 = 1 from rfl, Matrix.mul_one]
  exact hA

theorem congr_psuConj (h : UnitaryFieldData p f K) (A : unitaryIsom3 h) :
    MulAut.congr (psuToPrimeForm h) (psuConj h A) =
      primeFormConjHom h (idGram K 3) ⟨A, mem_primeFormUnitary_of_mem_unitaryIsom3 h A.2⟩ := by
  ext z
  obtain ⟨y, rfl⟩ := (psuToPrimeForm h).surjective z
  induction y using QuotientGroup.induction_on with
  | H g =>
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, psuConj_mk]
    change _ = primeFormConjAut h _ _ ((psuToPrimeForm h) (g : unitaryPSU h 3))
    have hg : (psuToPrimeForm h) (g : unitaryPSU h 3) =
        ((⟨g.1, by rw [← unitarySU_eq_gramSU h 3]; exact g.2⟩ : gramSU h _) : primeFormP h _) :=
      rfl
    rw [hg, primeFormConjAut_mk]
    rfl

theorem psuConj_eq_one_of_primeForm (h : UnitaryFieldData p f K)
    (key : ∀ {D H : Subgroup (MulAut (primeFormP h (idGram K 3)))}, IsElemAbelian 3 D →
      Nat.card D = 3 ^ 2 → innerAut (primeFormP h (idGram K 3)) ≤ H →
      ∀ Y : primeFormUnitary h (idGram K 3),
        primeFormConjHom h (idGram K 3) Y ∈ localDeltaIn 3 H D →
        primeFormConjHom h (idGram K 3) Y = 1)
    {D H : Subgroup (MulAut (unitaryPSU h 3))} (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9)
    (hH : innerAut (unitaryPSU h 3) ≤ H) {A : unitaryIsom3 h}
    (hα : psuConj h A ∈ localDeltaIn 3 H D) : psuConj h A = 1 := by
  set φ : MulAut (unitaryPSU h 3) ≃* MulAut (primeFormP h (idGram K 3)) :=
    MulAut.congr (psuToPrimeForm h) with hφ
  have hcard9 : Nat.card D = 3 ^ 2 := by rw [hcard]; norm_num
  have hD' : IsElemAbelian 3 (D.map φ.toMonoidHom) :=
    (isEkIn_map_mulEquiv 3 2 φ (A := ⊤) (D := D) ⟨le_top, hD, hcard9⟩).2.1
  have hcard' : Nat.card (D.map φ.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hcard9]
  have hH' : innerAut (primeFormP h (idGram K 3)) ≤ H.map φ.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj ((psuToPrimeForm h).symm x), hH ⟨_, rfl⟩, ?_⟩
    change MulAut.congr (psuToPrimeForm h) (MulAut.conj ((psuToPrimeForm h).symm x)) =
      MulAut.conj x
    rw [congr_conj_apply, MulEquiv.apply_symm_apply]
  have hY : primeFormConjHom h (idGram K 3)
      ⟨A, mem_primeFormUnitary_of_mem_unitaryIsom3 h A.2⟩ ∈
        localDeltaIn 3 (H.map φ.toMonoidHom) (D.map φ.toMonoidHom) := by
    rw [localDeltaIn_map_mulEquiv, ← congr_psuConj]
    exact Subgroup.mem_map_of_mem _ hα
  have h1 := key hD' hcard' hH' _ hY
  rw [← congr_psuConj] at h1
  exact φ.injective (by rw [map_one]; exact h1)

end CFSG.HardMathSupport.Solomon.Coordinator
