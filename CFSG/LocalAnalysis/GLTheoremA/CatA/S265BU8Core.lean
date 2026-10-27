module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Comm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Wt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Fix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2UniResF

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.GLTheoremA.HDescUniRes
open Matrix

theorem exists_layer_of_fieldHom_u8 {K : Type} [Field K] (h : UnitaryFieldData 2 3 K) {n : ℕ}
    (hn : n = 5 ∨ n = 6) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {E₀ V : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hED : E₀ ≤ primeFormD h (idGram K n)) (hE3 : ∀ c ∈ E₀, c ^ 3 = 1)
    (hEc : ∀ c ∈ E₀, ∀ d ∈ E₀, c * d = d * c)
    (hEσ : ∀ c ∈ E₀, primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ * c =
      c * primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ)
    (h27 : 27 ≤ Nat.card E₀) (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥)
    (hVD : V ≤ primeFormD h (idGram K n)) (hEV : ∀ c ∈ E₀, ∀ v ∈ V, c * v * c⁻¹ ∈ V) :
    ∃ c ∈ E₀, c ≠ 1 ∧ GLAPLayer 3
      (fixSubgroup (primeFormFieldHom h (isPrimeFormGram_idGram (K := K) (n := n)) σ) ⊓
        fixSubgroup c) ≠ ⊥ := by
  haveI := h.finite
  haveI : CharP K 2 := h.charP
  have hn3 : 3 ≤ n := by omega
  obtain ⟨T₂, hT2, hT, hTU, hTE⟩ :=
    exists_two_lift_of_le_primeFormD h hn3 (by norm_num) hV2 hV hVD hEV
  obtain ⟨W, hW, hiso, hWE⟩ := exists_isotropic_stable h hT2 hT hTU
    (Â := (E₀.comap (primeFormConjHom h (idGram K n))).map
      (primeFormUnitary h (idGram K n)).subtype)
    (Subgroup.map_subtype_le _) (by
      rintro _ ⟨X, hX, rfl⟩ t ht
      exact hTE X hX t ht)
  have hWE' : ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E₀ →
      ∀ w ∈ W, ((X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := fun X hX =>
    hWE X (Subgroup.mem_map_of_mem _ hX)
  obtain ⟨X, hXE, hX1, hX3, R, χ, hRX, h4⟩ := exists_four_eigen h hn hσ hED hE3 hEσ h27 hW
    hiso hWE' (mul_comm_of_isotropic_stable h hn hσ hED hE3 hEc hEσ h27 hW hiso hWE')
  exact ⟨_, hXE, hX1, glaPLayer_ne_bot_of_four_eigen h hn hσ hX3 (hEσ _ hXE) hRX h4⟩

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
