module

public import CFSG.LieType.SeitzGeneration.OuterHeisFixed
public import CFSG.LieType.SeitzGeneration.UnitaryScope

public section

namespace CFSG.LieType.SeitzGeneration

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem heisD_unitary (h : UnitaryFieldData ℓ f K) {ω : K} (hω : h.bar ω * ω = 1) :
    ((heisD ω).map h.bar)ᵀ * heisD ω = 1 := by
  rw [heisD, diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [map_pow, ← mul_pow, hω, one_pow]

theorem heisC_one_unitary (h : UnitaryFieldData ℓ f K) :
    ((heisC (1 : K)).map h.bar)ᵀ * heisC 1 = 1 := by
  have hmap : (heisC (1 : K)).map h.bar = heisC 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisC]
  rw [hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisC, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_heis_pair_unitary (h : UnitaryFieldData ℓ f K) {ω : K} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hωb : h.bar ω * ω = 1) {σ : K ≃+* K} (hσω : σ ω = ω) :
    ∃ s t : primeFormP h (idGram K 3), Commute s t ∧ s ≠ 1 ∧ s ^ 3 = 1 ∧ t ^ 3 = 1 ∧
      t ∉ Subgroup.zpowers s ∧
      primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ s = s ∧
      primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ t = t := by
  have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
  set u : Kˣ := Units.mk0 ω hω0 with hu
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [hu] using hω3)
  have hid : idGram K 3 = 1 := Units.val_one
  let D : gramSU h (idGram K 3) :=
    ⟨Matrix.SpecialLinearGroup.toGL ⟨heisD ω, by rw [det_heisD, hω3]⟩, by
      refine mem_gramSU.mpr ⟨?_, ?_⟩
      · change ((heisD ω).map h.bar)ᵀ * idGram K 3 * heisD ω = idGram K 3
        rw [hid, Matrix.mul_one]
        exact heisD_unitary h hωb
      · change (heisD ω).det = 1
        rw [det_heisD, hω3]⟩
  let S : gramSU h (idGram K 3) :=
    ⟨Matrix.SpecialLinearGroup.toGL ⟨heisC 1, det_heisC_one⟩, by
      refine mem_gramSU.mpr ⟨?_, ?_⟩
      · change ((heisC (1 : K)).map h.bar)ᵀ * idGram K 3 * heisC 1 = idGram K 3
        rw [hid, Matrix.mul_one]
        exact heisC_one_unitary h
      · exact det_heisC_one⟩
  let z : gramSU h (idGram K 3) := ⟨GeneralLinearGroup.scalar (Fin 3) u, by
      refine mem_gramSU.mpr ⟨?_, ?_⟩
      · exact mem_primeFormUnitary.mp (scalar_mem_primeFormUnitary h (c := u) hωb)
      · rw [GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal, Fin.prod_univ_three]
        simp only [hu, Units.val_mk0]
        rw [← hω3]
        ring⟩
  have hzN : z ∈ normOneScalars h (gramSU h (idGram K 3)) 3 :=
    ⟨u, by rw [UnitaryFieldData.norm, mul_comm]; exact hωb, hu3, rfl⟩
  have hDS : D * S = z * (S * D) := Subtype.ext (Units.ext (by
    change heisD ω * heisC 1 = (GeneralLinearGroup.scalar (Fin 3) u : Matrix (Fin 3) (Fin 3) K) *
      (heisC 1 * heisD ω)
    rw [GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    exact heisD_mul_heisC hω3))
  have hker : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3)).ker ≤
      Subgroup.center (gramSU h (idGram K 3)) := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ 3
  have hz1 : z ≠ 1 := by
    intro hz
    have h1 := congrArg (fun A : gramSU h (idGram K 3) =>
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) hz
    simp [z, hu, scalar_apply] at h1
    exact hω1 h1
  obtain ⟨hcomm, hd1, hnot⟩ := heis_pair_of_central
    (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3)) hker
    ((QuotientGroup.eq_one_iff z).mpr hzN) hz1 hDS
  have hfix : ∀ g : gramSU h (idGram K 3), glAut σ (g : GL (Fin 3) K) = g →
      primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3) g) =
        QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3) g := fun g hg => by
    change primeFormFieldAut h isPrimeFormGram_one σ (g : primeFormP h (idGram K 3)) =
      (g : primeFormP h (idGram K 3))
    rw [primeFormFieldAut_mk]
    congr 1
    exact Subtype.ext hg
  refine ⟨_, _, hcomm, hd1, ?_, ?_, hnot, hfix D (Units.ext ?_), hfix S (Units.ext ?_)⟩
  · rw [← map_pow, show D ^ 3 = 1 from Subtype.ext (Units.ext (by
      change heisD ω ^ 3 = 1
      exact heisD_pow_three hω3)), map_one]
  · rw [← map_pow, show S ^ 3 = 1 from Subtype.ext (Units.ext (by
      change heisC (1 : K) ^ 3 = 1
      exact heisC_one_pow_three)), map_one]
  · rw [coe_glAut]
    exact map_heisD σ.toRingHom hσω
  · rw [coe_glAut]
    exact map_heisC_one σ.toRingHom

end Unitary

end CFSG.LieType.SeitzGeneration
